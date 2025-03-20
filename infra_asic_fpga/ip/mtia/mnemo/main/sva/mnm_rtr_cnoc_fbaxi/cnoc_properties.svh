// parameter CNOC_INPUT = 1: CNOC input, = 0: CNOC output
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

  property cnoc_ttl_always_at_least_1;
    cnoc_valid |-> cnoc_bundle.ttl != '0;
  endproperty

  property cnoc_ttl_always_within_maximum;
    cnoc_valid |-> cnoc_bundle.ttl <= cip_pkg::CIP_NOC_TTL_DEFAULT;
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

  logic [TOTAL_NUM_VCS-1:0][CREDITS_WIDTH-1:0] cnoc_credit_counter;

  wire [TOTAL_NUM_VCS-1:0] cnoc_credit_counter_incr;
  wire [TOTAL_NUM_VCS-1:0] cnoc_credit_counter_decr;

  localparam TOTAL_NUM_VCS_WIDTH = $clog2(TOTAL_NUM_VCS + 1);
  wire [TOTAL_NUM_VCS_WIDTH-1:0] cnoc_payload_vc;
  assign cnoc_payload_vc = (cnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ) ? TOTAL_NUM_VCS_WIDTH'('d0) + cnoc_bundle.payload.daxi_ar.user.vc
                                                                                : TOTAL_NUM_VCS_WIDTH'('d0) + cnoc_bundle.payload.daxi_b.user.vc + READ_VCS;

  genvar v;

  for (v=0; v<TOTAL_NUM_VCS; v++) begin
    assign cnoc_credit_counter_incr[v] = cnoc_credit_release[v];
    assign cnoc_credit_counter_decr[v] = cnoc_valid && (cnoc_payload_vc == v);

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        cnoc_credit_counter[v] <= CREDITS_INIT[v];
      end
      else if (first_cycle_out_of_reset && use_llc_credits) begin
        cnoc_credit_counter[v] <= CREDITS_INIT_LLC;
      end
      else begin
        cnoc_credit_counter[v] <= cnoc_credit_counter[v] + cnoc_credit_counter_incr[v] - cnoc_credit_counter_decr[v];
      end
    end
  end

  // whenever credit release happens, cnoc credit counter never goes above its initial value
  property cnoc_credit_releases_no_excess(i);
    cnoc_credit_release[i] |-> (cnoc_credit_counter[i] < CREDITS_INIT_MUXED[i]);
  endproperty

  // if cnoc_valid asserted, then its credit counter is at least the minimum allowed
  property cnoc_valid_with_sufficient_credit(i);
    cnoc_valid && (cnoc_payload_vc == i) |-> cnoc_credit_counter[i] >= CREDITS_MIN;
  endproperty

  // if credit_counter less than its initial value, will always see credit release appear
  property cnoc_credit_release_for_each_valid_liveness(i);
    cnoc_credit_counter[i] < CREDITS_INIT_MUXED[i] |-> s_eventually (cnoc_credit_release[i]);
  endproperty

  // credit release covers

  wire [TOTAL_NUM_VCS-1:0] cnoc_credit_counter_is_zero;
  for (v=0; v<TOTAL_NUM_VCS; v++) begin
    assign cnoc_credit_counter_is_zero[v] = (cnoc_credit_counter[v] == '0);
  end

  property cnoc_credit_counter_can_reach_zero(i);
    cnoc_credit_counter_is_zero[i];
  endproperty

  property cnoc_credit_counter_zero_to_maximum_liveness(i);
    cnoc_credit_counter_is_zero[i] ##[1:$] (cnoc_credit_counter[i] == CREDITS_INIT_MUXED[i]);
  endproperty


  // set up direction constraints
  wire cip_pkg::coord_id_t cnoc_tgt_id;
  assign cnoc_tgt_id = (cnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ) ? cnoc_bundle.payload.daxi_ar.user.tgt_id
                                                                            : cnoc_bundle.payload.daxi_b.user.tgt_id;

  property cnoc_tgt_id_not_northwards;
    !(cnoc_tgt_id.ycoord < my_location.ycoord);
  endproperty

  property cnoc_tgt_id_not_southwards;
    !(cnoc_tgt_id.ycoord > my_location.ycoord);
  endproperty

  property cnoc_tgt_id_not_westwards;
    !(cnoc_tgt_id.xcoord < my_location.xcoord);
  endproperty

  property cnoc_tgt_id_not_eastwards;
    !(cnoc_tgt_id.xcoord > my_location.xcoord+1);
  endproperty

  property cnoc_tgt_id_not_leaf0wards;
    !(cnoc_tgt_id.xcoord == my_location.xcoord);
  endproperty

  property cnoc_tgt_id_not_leaf1wards;
    !(cnoc_tgt_id.xcoord == my_location.xcoord+1);
  endproperty

  property cnoc_tgt_id_cip_id_is_0_or_1;
    cnoc_valid |-> cnoc_tgt_id.cip_id inside {2'b00, 2'b01};
  endproperty

  property cnoc_tgt_id_cip_id_same_as_in_my_location;
    cnoc_valid |-> cnoc_tgt_id.cip_id == my_location.cip_id;
  endproperty

  // indicators on which AXI channels are being used
  wire cnoc_is_AR_channel, cnoc_is_B_channel;

  assign cnoc_is_AR_channel = (cnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_READ );
  assign cnoc_is_B_channel  = (cnoc_bundle.channel == cip_pkg::NOC_CHANNEL_E_WRITE);

  // pick out specific AXI write signals
  wire bvalid;
  wire [8:0] bid;
  wire [cip_pkg::CIP_DAXI_B_USER_WIDTH-1:0] buser;
  wire [cip_pkg::CIP_DAXI_BUSER_NOC_ID_WIDTH-1:0] bnocid;
  wire cip_pkg::coord_id_t btgtid;
  wire [cip_pkg::CIP_DAXI_BUSER_VC_WIDTH-1:0] buservc;

  assign bvalid  = cnoc_valid && cnoc_is_B_channel;
  assign bid     = cnoc_bundle.payload.daxi_b.id.iid;
  assign buser   = cnoc_bundle.payload.daxi_b.user;
  assign bnocid  = cnoc_bundle.payload.daxi_b.user.noc_id;
  assign btgtid  = cnoc_bundle.payload.daxi_b.user.tgt_id;
  assign buservc = cnoc_bundle.payload.daxi_b.user.vc;

  // pick out specific AXI read signals
  wire arvalid;
  wire [8:0] arid;
  wire [1:0] arlen;
  wire [cip_pkg::CIP_DAXI_AR_ADDR_WIDTH-1:0] araddr;
  wire [cip_pkg::CIP_DAXI_AR_USER_WIDTH-1:0] aruser;
  wire [cip_pkg::CIP_DAXI_ARUSER_NOC_ID_WIDTH-1:0] arnocid;
  wire cip_pkg::coord_id_t arsrcid;
  wire cip_pkg::coord_id_t artgtid;
  wire [cip_pkg::CIP_DAXI_ARUSER_HOST_SUBF_WIDTH-1:0] arhost;
  wire [cip_pkg::CIP_DAXI_ARUSER_HOST_ARSIZE_WIDTH-1:0] arsize;
  wire [cip_pkg::CIP_DAXI_ARUSER_VC_WIDTH-1:0] aruservc;
  wire cip_pkg::CC_OPCODE_e arcc_opcode;

  assign arvalid     = cnoc_valid && cnoc_is_AR_channel;
  assign arid        = cnoc_bundle.payload.daxi_ar.id.iid;
  assign arlen       = cnoc_bundle.payload.daxi_ar.id.len;
  assign araddr      = cnoc_bundle.payload.daxi_ar.addr;
  assign aruser      = cnoc_bundle.payload.daxi_ar.user;
  assign arnocid     = cnoc_bundle.payload.daxi_ar.user.noc_id;
  assign arsrcid     = cnoc_bundle.payload.daxi_ar.user.src_id;
  assign artgtid     = cnoc_bundle.payload.daxi_ar.user.tgt_id;
  assign arhost      = cnoc_bundle.payload.daxi_ar.user.host;
  assign arsize      = cnoc_bundle.payload.daxi_ar.user.host_arsize;
  assign aruservc    = cnoc_bundle.payload.daxi_ar.user.vc;
  assign arcc_opcode = cnoc_bundle.payload.daxi_ar.user.cc_opcode;


  // B - Write Response Channel properties

  // if bvalid asserted, B target id coords are within grid bounds
  property btgtid_coords_within_grid;
    bvalid |-> (btgtid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (btgtid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
               (btgtid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (btgtid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // B user vc within legal range
  property buser_vc_is_legal;
    bvalid |-> buservc < WRITE_VCS;
  endproperty


  // B channel covers

  property buser_tgt_id_x_coord(x);
    bvalid && (btgtid.xcoord == x);
  endproperty

  property buser_tgt_id_y_coord(y);
    bvalid && (btgtid.ycoord == y);
  endproperty

  property buser_noc_id(n);
    bvalid && (bnocid == n);
  endproperty

  property buser_vc(n);
    bvalid && (buservc == n);
  endproperty


  // AR channel properties

  // ar_host_size field value is legal
  property arhost_size_field_is_legal;
    arvalid && (arhost == cip_pkg::CIP_DAXI_ARUSER_HOST_SUBF_WIDTH'('d1)) |-> arsize != cip_pkg::CIP_DAXI_ARUSER_HOST_ARSIZE_WIDTH'('b111);
  endproperty

  // A burst must not cross a 4kbyte boundary
  wire [cip_pkg::CIP_DAXI_AR_ADDR_WIDTH-1:0] araddr_at_burst_end;
  assign araddr_at_burst_end = araddr + (arlen << arsize);
 
  property araddr_burst_within_4kb_boundary;
    arvalid |-> araddr[cip_pkg::CIP_DAXI_AR_ADDR_WIDTH-1:12] == araddr_at_burst_end[cip_pkg::CIP_DAXI_AR_ADDR_WIDTH-1:12];
  endproperty

  // if arvalid asserted, AR source id coords are within grid bounds
  property arsrcid_coords_within_grid;
    arvalid |-> (arsrcid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (arsrcid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
                (arsrcid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (arsrcid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // if arvalid asserted, AR target id coords are within grid bounds
  property artgtid_coords_within_grid;
    arvalid |-> (artgtid.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START-1) && (artgtid.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END+1) &&
                (artgtid.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START-1) && (artgtid.ycoord <= cip_pkg::CIP_RTR_GRID_COORD_Y_END+1);
  endproperty

  // cc_opcode never is RDNR
  property arcc_opcode_is_legal;
    arvalid |-> arcc_opcode != cip_pkg::CC_OPCODE_E_RDNR;
  endproperty

  // AR user vc within legal range
  property aruser_vc_is_legal;
    arvalid |-> aruservc < READ_VCS;
  endproperty


  // AR channel covers

  property aruser_src_id_x_coord(x);
    arvalid && (arsrcid.xcoord == x);
  endproperty

  property aruser_src_id_y_coord(y);
    arvalid && (arsrcid.ycoord == y);
  endproperty

  property aruser_tgt_id_x_coord(x);
    arvalid && (artgtid.xcoord == x);
  endproperty

  property aruser_tgt_id_y_coord(y);
    arvalid && (artgtid.ycoord == y);
  endproperty

  property aruser_noc_id(n);
    arvalid && (arnocid == n);
  endproperty

  property aruser_vc(n);
    arvalid && (aruservc == n);
  endproperty

  property arid_len(n);
    arvalid && (arlen == n);
  endproperty


  // covers between both B and AR channels

  property no_gaps_write_channel_read_channel;
    bvalid ##1 arvalid;
  endproperty

  property no_gaps_read_channel_write_channel;
    arvalid ##1 bvalid;
  endproperty

  property no_gaps_write_channel_write_channel;
    bvalid ##1 bvalid;
  endproperty

  property no_gaps_read_channel_read_channel;
    arvalid ##1 arvalid;
  endproperty

  property gap_1_write_channel_read_channel;
    bvalid ##1 (!bvalid && !arvalid) ##1 arvalid;
  endproperty

  property gap_1_read_channel_write_channel;
    arvalid ##1 (!arvalid && !bvalid) ##1 bvalid;
  endproperty

  property gap_1_write_channel_write_channel;
    bvalid ##1 !bvalid ##1 bvalid;
  endproperty

  property gap_1_read_channel_read_channel;
    arvalid ##1 !arvalid ##1 arvalid;
  endproperty

  property gap_2_write_channel_read_channel;
    bvalid ##1 (!bvalid && !arvalid)[*2] ##1 arvalid;
  endproperty

  property gap_2_read_channel_write_channel;
    arvalid ##1 (!arvalid && !bvalid)[*2] ##1 bvalid;
  endproperty

  property gap_2_write_channel_write_channel;
    bvalid ##1 !bvalid[*2] ##1 bvalid;
  endproperty

  property gap_2_read_channel_read_channel;
    arvalid ##1 !arvalid[*2] ##1 arvalid;
  endproperty
