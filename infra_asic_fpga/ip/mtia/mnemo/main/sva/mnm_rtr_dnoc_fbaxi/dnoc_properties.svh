// parameter DNOC_INPUT = 1: DNOC input, = 0: DNOC output
//
// other parameters:
//  CREDITS_INIT  - initial value of credit counter after reset
//  CREDITS_MIN   - minimum value for credit counter before requests can be sent out
//  SRC_DIR       - instantiated direction (if >= 6, no constraints used on direction)

  //localparam CREDITS_WIDTH = $clog2(CREDITS_INIT+1);  // number of bits needed to store this value
  localparam CREDITS_WIDTH = cip_rtr_pkg::RTR_TX_DEPTH_W;


  // Default Clocking and Reset scheme
  default clocking @(posedge clk); endclocking
  default disable iff (!reset_n);


  // basic TTL (time to live) signal properties

  property dnoc_ttl_always_at_least_1;
    dnoc_valid |-> dnoc_bundle.ttl != '0;
  endproperty

  property dnoc_ttl_always_within_maximum;
    dnoc_valid |-> dnoc_bundle.ttl <= cip_pkg::CIP_NOC_TTL_DEFAULT;
  endproperty


  // set up dnoc first and last beat indicators

  wire dnoc_read;  // indicate if rx input is a read channel or not
  assign dnoc_read = dnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ;

  wire dnoc_last;  // pick out when last beat of burst is seen
  assign dnoc_last = dnoc_read ? dnoc_bundle.payload.daxi_r.last : dnoc_bundle.payload.daxi_combo_aw_w.w.last;

  // flag up for first beat of bursts
  logic dnoc_first;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      dnoc_first <= 1'b1;
    end
    else if (dnoc_valid) begin
      // will be set to zero after first beat (if not also last beat) and when last beat seen, it gets set to 1
      dnoc_first <= dnoc_last;
    end
  end    

  // ttl same throughout a burst
  property dnoc_ttl_same_throughout_burst;
    dnoc_valid && !dnoc_last |=> $stable(dnoc_bundle.ttl);
  endproperty

  localparam TOTAL_NUM_VCS_WIDTH = $clog2(TOTAL_NUM_VCS + 1);
  wire [TOTAL_NUM_VCS_WIDTH-1:0] dnoc_payload_vc;
  assign dnoc_payload_vc = (dnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ) ? TOTAL_NUM_VCS_WIDTH'('d0)
                                                                                : TOTAL_NUM_VCS_WIDTH'('d1) + dnoc_bundle.payload.daxi_combo_aw_w.aw.user.vc;

  // vc same throught a burst
  property dnoc_vc_same_throughout_burst;
    dnoc_valid && !dnoc_last |=> $stable(dnoc_payload_vc);
  endproperty

  // credit counters per VC

  wire use_llc_credits;

  if (CREDITS_INIT_LLC != 0) begin
    assign use_llc_credits = ((SRC_DIR == cip_rtr_pkg::NOC_DIR_WEST) && (my_location.xcoord == 1)) ||
                             ((SRC_DIR == cip_rtr_pkg::NOC_DIR_EAST) && (my_location.xcoord == 5))  ;
  end
  else begin
    assign use_llc_credits = 1'b0;
  end

  wire [TOTAL_NUM_VCS-1:0][cip_rtr_pkg::RTR_TX_DEPTH_W-1:0] CREDITS_INIT_MUXED = use_llc_credits ? {TOTAL_NUM_VCS{cip_rtr_pkg::RTR_TX_DEPTH_W'(CREDITS_INIT_LLC)}}
                                                                                                 : CREDITS_INIT;

  logic first_cycle_out_of_reset;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      first_cycle_out_of_reset <= 1'b1;
    end
    else begin
      first_cycle_out_of_reset <= 1'b0;
    end
  end

  logic [TOTAL_NUM_VCS-1:0][CREDITS_WIDTH-1:0] dnoc_credit_counter;

  wire [TOTAL_NUM_VCS-1:0] dnoc_credit_counter_incr;
  wire [TOTAL_NUM_VCS-1:0] dnoc_credit_counter_decr;

  genvar v;

  for (v=0; v<TOTAL_NUM_VCS; v++) begin
    assign dnoc_credit_counter_incr[v] = dnoc_credit_release[v];
    assign dnoc_credit_counter_decr[v] = dnoc_valid && (dnoc_payload_vc == v);

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        dnoc_credit_counter[v] <= CREDITS_INIT[v];
      end
      else if (first_cycle_out_of_reset && use_llc_credits) begin
        dnoc_credit_counter[v] <= CREDITS_INIT_LLC;
      end
      else begin
        dnoc_credit_counter[v] <= dnoc_credit_counter[v] + dnoc_credit_counter_incr[v] - dnoc_credit_counter_decr[v];
      end
    end
  end


  // whenever credit release happens, dnoc credit counter never goes above its initial value
  property dnoc_credit_releases_no_excess(i);
    dnoc_credit_release[i] |-> (dnoc_credit_counter[i] < CREDITS_INIT_MUXED[i]);
  endproperty

  // extract 'len' from dnoc payload
  wire [1:0] dnoc_len;
  assign dnoc_len = dnoc_read ? dnoc_bundle.payload.daxi_r.id.len : dnoc_bundle.payload.daxi_combo_aw_w.aw.id.len;

  // if dnoc_valid asserted, then its credit counter is at least the minimum allowed
  property dnoc_valid_with_sufficient_credit(i);
    dnoc_valid && (dnoc_payload_vc == i) && dnoc_first |-> dnoc_credit_counter[i] >= (dnoc_len + CREDITS_MIN);
  endproperty

  // if credit_counter less than its initial value, will always see credit release appear
  property dnoc_credit_release_for_each_valid_liveness(i);
    dnoc_credit_counter[i] < CREDITS_INIT_MUXED[i] |-> s_eventually (dnoc_credit_release[i]);
  endproperty

  // credit release covers

  wire [TOTAL_NUM_VCS-1:0] dnoc_credit_counter_is_zero;
  for (v=0; v<TOTAL_NUM_VCS; v++) begin
    assign dnoc_credit_counter_is_zero[v] = (dnoc_credit_counter[v] == '0);
  end

  property dnoc_credit_counter_can_reach_zero(i);
    dnoc_credit_counter_is_zero[i];
  endproperty

  property dnoc_credit_counter_zero_to_maximum_liveness(i);
    dnoc_credit_counter_is_zero[i] ##[1:$] (dnoc_credit_counter[i] == CREDITS_INIT_MUXED[i]);
  endproperty


  // set up direction constraints
  wire cip_pkg::coord_id_t dnoc_tgt_id;
  assign dnoc_tgt_id = (dnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ) ? dnoc_bundle.payload.daxi_r.user.tgt_id
                                                                            : dnoc_bundle.payload.daxi_combo_aw_w.aw.user.tgt_id;

  property dnoc_tgt_id_not_northwards;
    !(dnoc_tgt_id.ycoord < my_location.ycoord);
  endproperty

  property dnoc_tgt_id_not_southwards;
    !(dnoc_tgt_id.ycoord > my_location.ycoord);
  endproperty

  property dnoc_tgt_id_not_westwards;
    !(dnoc_tgt_id.xcoord < my_location.xcoord);
  endproperty

  property dnoc_tgt_id_not_eastwards;
    !(dnoc_tgt_id.xcoord > my_location.xcoord+1);
  endproperty

  property dnoc_tgt_id_not_leaf0wards;
    !(dnoc_tgt_id.xcoord == my_location.xcoord);
  endproperty

  property dnoc_tgt_id_not_leaf1wards;
    !(dnoc_tgt_id.xcoord == my_location.xcoord+1);
  endproperty

  property dnoc_tgt_id_cip_id_is_0_or_1;
    dnoc_valid |-> dnoc_tgt_id.cip_id inside {2'b00, 2'b01};
  endproperty

  property dnoc_tgt_id_cip_id_same_as_in_my_location;
    dnoc_valid |-> dnoc_tgt_id.cip_id == my_location.cip_id;
  endproperty

  // indicators on which AXI channels are being used
  wire dnoc_is_R_channel, dnoc_is_AW_W_channel;

  assign dnoc_is_R_channel    = (dnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ );
  assign dnoc_is_AW_W_channel = (dnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_WRITE);

  // pick out specific AXI write signals
  wire awvalid;
  wire [8:0] awid;
  wire [1:0] awlen;
  wire [cip_pkg::CIP_DAXI_AW_ADDR_WIDTH-1:0] awaddr;
  wire [cip_pkg::CIP_DAXI_AW_CACHE_WIDTH-1:0] awcache;
  wire [cip_pkg::CIP_DAXI_AW_LOCK_WIDTH-1:0] awlock;
  wire [cip_pkg::CIP_DAXI_AW_USER_WIDTH-1:0] awuser;
  wire [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0] awuservc;
  wire [cip_pkg::CIP_DAXI_AWUSER_NOC_ID_WIDTH-1:0] awnocid;
  wire cip_pkg::coord_id_t awsrcid;
  wire cip_pkg::coord_id_t awtgtid;
  wire [cip_pkg::CIP_DAXI_AWUSER_HOST_WIDTH-1:0] awhost;
  wire [2:0] awsize;
  wire [3:0] awuser_reduction_type;

  assign awvalid  = dnoc_valid && dnoc_is_AW_W_channel;
  assign awid     = dnoc_bundle.payload.daxi_combo_aw_w.aw.id.iid;
  assign awlen    = dnoc_bundle.payload.daxi_combo_aw_w.aw.id.len;
  assign awaddr   = dnoc_bundle.payload.daxi_combo_aw_w.aw.addr;
  assign awcache  = dnoc_bundle.payload.daxi_combo_aw_w.aw.cache;
  assign awlock   = dnoc_bundle.payload.daxi_combo_aw_w.aw.lock;
  assign awuser   = dnoc_bundle.payload.daxi_combo_aw_w.aw.user;
  assign awuservc = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.vc;
  assign awhost   = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.host;
  assign awnocid  = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.noc_id;
  assign awsrcid  = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.src_id;
  assign awtgtid  = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.tgt_id;
  assign awsize   = dnoc_bundle.payload.daxi_combo_aw_w.w.strb.size;

  assign awuser_reduction_type = dnoc_bundle.payload.daxi_combo_aw_w.aw.user.reduction_type;

  wire wlast;
  wire [1:0] wuser;
  wire wstrb_enc;
  wire [6:0] wstrb_beat_offset;
  wire wstrb_subf;
  wire wstrb_rord;

  assign wlast             = dnoc_bundle.payload.daxi_combo_aw_w.w.last;
  assign wuser             = dnoc_bundle.payload.daxi_combo_aw_w.w.user;
  assign wstrb_enc         = dnoc_bundle.payload.daxi_combo_aw_w.w.user.wstrb_enc;
  assign wstrb_beat_offset = dnoc_bundle.payload.daxi_combo_aw_w.w.strb.beat_offset;
  assign wstrb_subf        = dnoc_bundle.payload.daxi_combo_aw_w.w.strb.subf;
  assign wstrb_rord        = dnoc_bundle.payload.daxi_combo_aw_w.w.strb.rord;


  // pick out specific AXI read signals
  wire rvalid;
  wire [8:0] rid;
  wire [1:0] rlen;
  wire [cip_pkg::CIP_DAXI_R_USER_WIDTH-1:0] ruser;
  wire [cip_pkg::CIP_DAXI_RUSER_NOC_ID_WIDTH-1:0] rnocid;
  wire cip_pkg::coord_id_t rtgtid;
  wire [cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH-1:0] rcc_dir;
  wire cip_pkg::CC_OPCODE_e rcc_opcode;
  wire [cip_pkg::CIP_DAXI_RUSER_CC_LANE_WIDTH-1:0] rcc_lane;
  wire [cip_pkg::CIP_DAXI_RUSER_PE_IN_CC_WIDTH-1:0] rpe_in_cc;
  wire [cip_pkg::CIP_DAXI_R_LAST_WIDTH-1:0] rlast;

  assign rvalid     = dnoc_valid && dnoc_is_R_channel;
  assign rid        = dnoc_bundle.payload.daxi_r.id.iid;
  assign rlen       = dnoc_bundle.payload.daxi_r.id.len;
  assign ruser      = dnoc_bundle.payload.daxi_r.user;
  assign rnocid     = dnoc_bundle.payload.daxi_r.user.noc_id;
  assign rtgtid     = dnoc_bundle.payload.daxi_r.user.tgt_id;
  assign rcc_dir    = dnoc_bundle.payload.daxi_r.user.cc_dir;
  assign rcc_opcode = dnoc_bundle.payload.daxi_r.user.cc_opcode;
  assign rcc_lane   = dnoc_bundle.payload.daxi_r.user.cc_lane;
  assign rpe_in_cc  = dnoc_bundle.payload.daxi_r.user.pe_in_cc;
  assign rlast      = dnoc_bundle.payload.daxi_r.last;


  // AW+W - Write Address and Data Channel properties

  // if AWVALID without WLAST seen, then next cycle another AWVALID will appear
  property awvalids_in_burst_are_consecutive;
    awvalid && !wlast |=> awvalid;
  endproperty

  // AWADDRs are the same throughout a burst
  property awaddrs_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awaddr);
  endproperty

  // AWCACHEs are the same throughout a burst
  property awcaches_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awcache);
  endproperty

  // AWLOCKs are the same throughout a burst
  property awlocks_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awlock);
  endproperty

  // AWIDs are the same throughout a burst
  property awids_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awid);
  endproperty

  // AWLENs are the same throughout a burst
  property awlens_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awlen);
  endproperty

  // AWLEN restricted to only 2'b00 or 2'b01
  property awlen_restricted;
    awvalid |-> !awlen[1];
  endproperty

  // AWUSERs are the same throughout a burst
  property awusers_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awuser);
  endproperty

  // WUSERs are the same throughout a burst
  property wusers_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(wuser);
  endproperty

  // track number of beats seen so far in a AW+W burst
  logic [1:0] wdata_items_seen;  // dnoc_bundle.payload.d_axi_aw.id.len is 2 bits

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      wdata_items_seen <= '0;
    end
    else if (awvalid) begin
      if (wlast) begin
        wdata_items_seen <= '0;
      end
      else begin
        wdata_items_seen <= wdata_items_seen + 2'b01;
      end
    end
  end

  // WLAST is high when expected
  property wlast_as_expected;
    awvalid |-> wlast == (wdata_items_seen == awlen);
  endproperty

  // A burst must not cross a 4kbyte boundary
  wire [cip_pkg::CIP_DAXI_AW_ADDR_WIDTH-1:0] awaddr_at_burst_end;
  assign awaddr_at_burst_end = awaddr + (awlen << awsize);

  property awaddr_burst_within_4kb_boundary;
    awvalid |-> awaddr[cip_pkg::CIP_DAXI_AW_ADDR_WIDTH-1:12] == awaddr_at_burst_end[cip_pkg::CIP_DAXI_AW_ADDR_WIDTH-1:12];
  endproperty

  // if awvalid asserted, AW source id coords are within grid bounds
  property awsrcid_coords_within_grid;
    awvalid |-> (awsrcid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (awsrcid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
                (awsrcid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (awsrcid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // if awvalid asserted, AW target id coords are within grid bounds
  property awtgtid_coords_within_grid;
    awvalid |-> (awtgtid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (awtgtid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
                (awtgtid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (awtgtid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // if awvalid asserted and awhost is 1, then wuser.wstrb_enc is 1
  property awhost_wstrb_enc_value_is_legal;
    awvalid && awhost |-> wstrb_enc;
  endproperty

  // some wstrb fields are the same throughout a burst
  property wstrb_beat_offset_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(wstrb_beat_offset);
  endproperty

  property awsize_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awsize);
  endproperty

  property wstrb_subf_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(wstrb_subf);
  endproperty

  property wstrb_rord_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(wstrb_rord);
  endproperty

  // aw_host_size field value is legal
  property awhost_size_field_value_is_legal;
    awvalid && awhost |-> awsize != 3'b111;
  endproperty

  // awuser_reduction_type only has legal values
  property awuser_reduction_type_value_is_legal;
    awvalid |-> awuser_reduction_type inside {4'b0000, 4'b0100, 4'b0101, 4'b0110, 4'b1000,
                                              4'b1001, 4'b1010, 4'b1100, 4'b1101, 4'b1110};
  endproperty

  // AW user vc within legal range
  property awuser_vc_is_legal;
    awvalid |-> awuservc < WRITE_VCS;
  endproperty


  // AW channel covers

  property awuser_src_id_x_coord(x);
    awvalid && (awsrcid.xcoord == x);
  endproperty

  property awuser_src_id_y_coord(y);
    awvalid && (awsrcid.ycoord == y);
  endproperty

  property awuser_tgt_id_x_coord(x);
    awvalid && (awtgtid.xcoord == x);
  endproperty

  property awuser_tgt_id_y_coord(y);
    awvalid && (awtgtid.ycoord == y);
  endproperty

  property awuser_noc_id(n);
    awvalid && (awnocid == n);
  endproperty

  property awuser_vc(n);
    awvalid && (awuservc == n);
  endproperty

  property awid_len(n);
    awvalid && (awlen == n);
  endproperty

  property awuser_host(n);
    awvalid && (awhost == n);
  endproperty

  property awsize_is(n);
    awvalid && awhost && (awsize == n);
  endproperty


  // R - Read Data Channel properties

  // if RVALID without RLAST seen, then next cycle another RVALID will appear
  property rvalids_in_burst_are_consecutive;
    rvalid && !rlast |=> rvalid;
  endproperty

  // RIDs are the same throughout a burst
  property rids_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(rid);
  endproperty

  // RLENs are the same throughout a burst
  property rlens_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(rlen);
  endproperty

  // RLEN restricted to only 2'b00 or 2'b01
  property rlen_restricted;
    rvalid |-> !rlen[1];
  endproperty

  // RUSERs are the same throughout a burst
  property rusers_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(ruser);
  endproperty

  // track number of beats seen so far in a R burst
  logic [1:0] rdata_items_seen;  // dnoc_bundle.payload.daxi_r.id.len is 2 bits

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      rdata_items_seen <= '0;
    end
    else if (rvalid) begin
      if (rlast) begin
        rdata_items_seen <= '0;
      end
      else begin
        rdata_items_seen <= rdata_items_seen + 2'b01;
      end
    end
  end

  // RLAST is high when expected
  property rlast_as_expected;
    rvalid |-> rlast == (rdata_items_seen == rlen);
  endproperty

  // if rvalid asserted, R target id coords are within grid bounds
  property rtgtid_coords_within_grid;
    rvalid |-> (rtgtid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (rtgtid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
               (rtgtid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (rtgtid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // cc_lane limited to legal values (cc_dir = row)
  property rcc_lane_is_legal_row;
    rvalid && (rcc_dir == cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH'('d1)) |-> (rcc_lane < cip_pkg::CIP_DAXI_RUSER_CC_LANE_WIDTH'('d13));  // legal range is 0..12
  endproperty

  // cc_lane limited to legal values (cc_dir = column)
  property rcc_lane_is_legal_column;
    rvalid && (rcc_dir == cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH'('d0)) |-> (rcc_lane < cip_pkg::CIP_DAXI_RUSER_CC_LANE_WIDTH'('d6));  // legal range is 0..5
  endproperty

  // cc_opcode never RDM (temporary restriction)
  property rcc_opcode_never_RDM;
    rvalid |-> (rcc_opcode != 2'b10);
  endproperty


  // R channel covers

  property ruser_tgt_id_x_coord(x);
    rvalid && (rtgtid.xcoord == x);
  endproperty

  property ruser_tgt_id_y_coord(y);
    rvalid && (rtgtid.ycoord == y);
  endproperty

  property ruser_noc_id(n);
    rvalid && (rnocid == n);
  endproperty

  property ruser_cc_opcode(n);
    rvalid && (rcc_opcode == n);
  endproperty

  property rcc_dir_1_ruser_cc_lane(n);
    rvalid  && (rcc_dir == cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH'('d1)) && (rcc_lane == n);
  endproperty

  property rcc_dir_0_ruser_cc_lane(n);
    rvalid  && (rcc_dir == cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH'('d0)) && (rcc_lane == n);
  endproperty

  property ruser_pe_in_cc_clear(n);
    rvalid && !rpe_in_cc[n];
  endproperty

  property ruser_pe_in_cc_set(n);
    rvalid && rpe_in_cc[n];
  endproperty


  // covers between both AW+W and R channels

  property no_gaps_write_channel_read_channel;
    awvalid ##1 rvalid;
  endproperty

  property no_gaps_read_channel_write_channel;
    rvalid ##1 awvalid;
  endproperty

  property no_gaps_write_channel_write_channel;
    awvalid ##1 awvalid;
  endproperty

  property no_gaps_read_channel_read_channel;
    rvalid ##1 rvalid;
  endproperty

  property gap_1_write_channel_read_channel;
    awvalid ##1 (!awvalid && !rvalid) ##1 rvalid;
  endproperty

  property gap_1_read_channel_write_channel;
    rvalid ##1 (!rvalid && !awvalid) ##1 awvalid;
  endproperty

  property gap_1_write_channel_write_channel;
    awvalid ##1 !awvalid ##1 awvalid;
  endproperty

  property gap_1_read_channel_read_channel;
    rvalid ##1 !rvalid ##1 rvalid;
  endproperty

  property gap_2_write_channel_read_channel;
    awvalid ##1 (!awvalid && !rvalid)[*2] ##1 rvalid;
  endproperty

  property gap_2_read_channel_write_channel;
    rvalid ##1 (!rvalid && !awvalid)[*2] ##1 awvalid;
  endproperty

  property gap_2_write_channel_write_channel;
    awvalid ##1 !awvalid[*2] ##1 awvalid;
  endproperty

  property gap_2_read_channel_read_channel;
    rvalid ##1 !rvalid[*2] ##1 rvalid;
  endproperty
