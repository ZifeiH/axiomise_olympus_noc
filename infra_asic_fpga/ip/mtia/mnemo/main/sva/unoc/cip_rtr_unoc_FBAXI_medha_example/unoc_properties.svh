
  localparam GRID_COORD_X_START = 0;
  localparam GRID_COORD_X_END = 9;
  localparam GRID_COORD_Y_START = 0;
  localparam GRID_COORD_Y_END = 14;

  // Default Clocking and Reset scheme
  default clocking @(posedge clk); endclocking
  default disable iff (!reset_n);


  // used as index in 'for' loops
  integer i;



  // basic TTL (time to live) signal properties

  property unoc_resp_ttl_always_at_least_1;
    unoc_resp_valid |-> unoc_resp_bundle.ttl != '0;  // 'never zero' same as 'at least 1' (for unsigned numbers)
  endproperty

  property unoc_req_ttl_always_at_least_1;
    unoc_req_valid |-> unoc_req_bundle.ttl != '0;  // 'never zero' same as 'at least 1' (for unsigned numbers)
  endproperty

  property unoc_resp_ttl_always_at_most_16;
    unoc_resp_valid |-> CFG_CHK? unoc_resp_bundle.ttl == cip_pkg::CIP_NOC_TTL_DEFAULT :
                                 unoc_resp_bundle.ttl < cip_pkg::CIP_NOC_TTL_DEFAULT ;  // 'never zero' same as 'at least 1' (for unsigned numbers)
  endproperty

  property unoc_req_ttl_always_at_most_16;
    unoc_req_valid |-> unoc_req_bundle.ttl < cip_pkg::CIP_NOC_TTL_DEFAULT;  // 'never zero' same as 'at least 1' (for unsigned numbers)
  endproperty

  logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0] unoc_resp_len;
  assign unoc_resp_len = unoc_resp_bundle.channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP ? 
                         unoc_resp_bundle.payload.uaxi_r.id.len : 'd0;

  wire unoc_resp_read;  // indicate if rx input is a read channel or not
  assign unoc_resp_read = unoc_resp_bundle.channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP;

  wire unoc_resp_last;  // pick out when last beat of burst is seen
  assign unoc_resp_last = unoc_resp_read ? unoc_resp_bundle.payload.uaxi_r.last : 1'b1;

  // flag up for first beat of bursts
  logic unoc_resp_first;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      unoc_resp_first <= 1'b1;
    end
    else if (unoc_resp_valid) begin
      // will be set to zero after first beat (if not also last beat) and when last beat seen, it gets set to 1
      unoc_resp_first <= unoc_resp_last;
    end
  end  

  
  logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0] unoc_req_len;
  assign unoc_req_len = unoc_req_bundle.channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ ? 
                         unoc_req_bundle.payload.uaxi_combo_aw_w.aw.id.len : 0;


  wire unoc_req_write;  // indicate if rx input is a read channel or not
  assign unoc_req_write = unoc_req_bundle.channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ;

  wire unoc_req_last;  // pick out when last beat of burst is seen
  assign unoc_req_last = unoc_req_write ? unoc_req_bundle.payload.uaxi_combo_aw_w.w.last : 1'b1;

  // flag up for first beat of bursts
  logic unoc_req_first;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      unoc_req_first <= 1'b1;
    end
    else if (unoc_req_valid) begin
      // will be set to zero after first beat (if not also last beat) and when last beat seen, it gets set to 1
      unoc_req_first <= unoc_req_last;
    end
  end  

  



  property unoc_resp_slave_channel;
    unoc_resp_valid |-> unoc_resp_bundle.channel inside {cip_pkg::UNOC_CHANNEL_E_READ_RESP,
                                                         cip_pkg::UNOC_CHANNEL_E_WRITE_RESP};
  endproperty

  property unoc_req_master_channel;
    unoc_req_valid |-> unoc_req_bundle.channel inside {cip_pkg::UNOC_CHANNEL_E_READ_REQ,
                                                         cip_pkg::UNOC_CHANNEL_E_WRITE_REQ};
  endproperty


  // indicators on which AXI channels are being used
  wire unoc_req_is_AR_channel, unoc_resp_is_B_channel;
  wire unoc_resp_is_R_channel,  unoc_req_is_AW_W_channel;
  
  assign unoc_resp_is_R_channel    = (unoc_resp_bundle.channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP );
  assign unoc_resp_is_B_channel    = (unoc_resp_bundle.channel == cip_pkg::UNOC_CHANNEL_E_WRITE_RESP);
  assign unoc_req_is_AR_channel    = (unoc_req_bundle.channel == cip_pkg::UNOC_CHANNEL_E_READ_REQ );
  assign unoc_req_is_AW_W_channel  = (unoc_req_bundle.channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ);

  // pick out specific AXI write signals
  //aw channel
  wire awvalid;
  cip_pkg::uaxi_id_t awid;
  wire [cip_pkg::CIP_GLOBAL_UAXI_ADDR_W-1:0] awaddr;
  wire [cip_pkg::CIP_UAXI_AW_USER_WIDTH-1:0] awuser;
  wire [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0] awlen;
  wire [cip_pkg::CIP_UAXI_AW_SIZE_WIDTH-1:0] awsize;
  wire cip_pkg::coord_id_t awsrcid;
  wire cip_pkg::coord_id_t awtgtid;

  assign awvalid = unoc_req_valid && unoc_req_is_AW_W_channel;
  assign awid    = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.id;
  assign awaddr  = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.addr;
  assign awuser  = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.user;
  assign awlen   = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.id.len;
  assign awsize  = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.size;
  assign awsrcid = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.id.originator_id;
  assign awtgtid = unoc_req_bundle.payload.uaxi_combo_aw_w.aw.user.tgt_id;



  //w channel
  wire [cip_pkg::CIP_UAXI_W_LAST_WIDTH-1:0] wlast;
  assign wlast = unoc_req_bundle.payload.uaxi_combo_aw_w.w.last;

  //b channel
  wire bvalid;
  wire [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0] bid;
  wire [cip_pkg::CIP_UAXI_B_USER_WIDTH-1:0] buser;
  wire cip_pkg::coord_id_t bsrcid;
  wire cip_pkg::coord_id_t btgtid;

  assign bvalid = unoc_resp_valid && unoc_resp_is_B_channel;
  assign bid    = unoc_resp_bundle.payload.uaxi_b.id.iid;
  assign buser  = unoc_resp_bundle.payload.uaxi_b.user;
  assign bsrcid = unoc_resp_bundle.payload.uaxi_b.user.src_id;
  assign btgtid = unoc_resp_bundle.payload.uaxi_b.id.originator_id; 

  // pick out specific AXI read signals
  //ar channel
  wire arvalid;
  wire [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0] arid;
  wire [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0] arlen;
  wire [cip_pkg::CIP_UAXI_AR_USER_WIDTH-1:0] aruser;
  wire [cip_pkg::CIP_UAXI_AR_SIZE_WIDTH-1:0] arsize;
  wire [cip_pkg::CIP_UAXI_AR_ADDR_WIDTH-1:0] araddr;
  wire cip_pkg::coord_id_t arsrcid;
  wire cip_pkg::coord_id_t artgtid;


  assign arvalid = unoc_req_valid && unoc_req_is_AR_channel;
  assign arid    = unoc_req_bundle.payload.uaxi_ar.id.iid;
  assign arlen   = unoc_req_bundle.payload.uaxi_ar.id.len;
  assign aruser  = unoc_req_bundle.payload.uaxi_ar.user;
  assign arsize  = unoc_req_bundle.payload.uaxi_ar.size;
  assign araddr  = unoc_req_bundle.payload.uaxi_ar.addr;
  assign arsrcid = unoc_req_bundle.payload.uaxi_ar.id.originator_id;
  assign artgtid = unoc_req_bundle.payload.uaxi_ar.user.tgt_id;

  //r channel
  wire rvalid;
  cip_pkg::uaxi_id_t rid;
  cip_pkg::uaxi_ruser_t ruser;
  wire [cip_pkg::CIP_UAXI_R_LAST_WIDTH-1:0] rlast;
  wire [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0] rlen;
  // wire cip_pkg::coord_id_t rsrcid;
  wire cip_pkg::coord_id_t rtgtid;
  assign rvalid = unoc_resp_valid && unoc_resp_is_R_channel;
  assign rid    = unoc_resp_bundle.payload.uaxi_r.id;
  assign ruser  = unoc_resp_bundle.payload.uaxi_r.user;
  assign rlen = unoc_resp_bundle.payload.uaxi_r.id.len;
  assign rlast  = unoc_resp_bundle.payload.uaxi_r.last;
  assign rtgtid = unoc_resp_bundle.payload.uaxi_r.id.originator_id;


  // AW+W - Write Address and Data Channel properties

  //valid values for awsize are 2 and 3 for 4B and 8B granularity
  property awsize_valid;
    awvalid |-> awsize inside {'d2, 'd3};
  endproperty

  // if AWVALID without WLAST seen, then next cycle another AWVALID will appear
  property awvalids_in_burst_are_consecutive;
    awvalid && !wlast |=> awvalid;
  endproperty

  // TTL is the same throughout a burst
  property write_req_ttl_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(unoc_req_bundle.ttl);
  endproperty


  // AWADDRs are the same throughout a burst
  property awaddrs_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awaddr);
  endproperty

  // AWIDs are the same throughout a burst
  property awids_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awid);
  endproperty


  // AWLENs are the same throughout a burst
  property awlens_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awlen);
  endproperty


  // AWUSERs are the same throughout a burst
  property awusers_in_burst_same_throughout;
    awvalid && !wlast |=> $stable(awuser);
  endproperty

  // track number of beats seen so far in a AW+W burst
  logic [2:0] wdata_items_seen;  // unoc_req_bundle.payload.d_axi_aw.id.len is 3 bits

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      wdata_items_seen <= '0;
    end
    else if (awvalid) begin
      if (!wlast) begin
         wdata_items_seen <= wdata_items_seen + 3'b001;
      end
      else begin
         wdata_items_seen <= '0;
    end
    end
  end

  // WLAST is high when expected
  property wlast_as_expected;
    awvalid |-> wlast == (wdata_items_seen == awlen);
  endproperty

  // if awvalid asserted, AW source id coords are within grid bounds
  property awsrcid_coords_within_grid;
    awvalid |-> (awsrcid.xcoord >= GRID_COORD_X_START) && (awsrcid.xcoord <= GRID_COORD_X_END) &&
                (awsrcid.ycoord >= GRID_COORD_Y_START) && (awsrcid.ycoord <= GRID_COORD_Y_END);
  endproperty



  // if awvalid asserted, AW target id coords are within grid bounds
  property awtgtid_coords_within_grid;
    awvalid |-> (awtgtid.xcoord >= GRID_COORD_X_START) && (awtgtid.xcoord <= GRID_COORD_X_END) &&
                (awtgtid.ycoord >= GRID_COORD_Y_START) && (awtgtid.ycoord <= GRID_COORD_Y_END);
  endproperty


  property btgtid_coords_within_grid;
    bvalid |-> (btgtid.xcoord >= GRID_COORD_X_START) && (btgtid.xcoord <= GRID_COORD_X_END) &&
               (btgtid.ycoord >= GRID_COORD_Y_START) && (btgtid.ycoord <= GRID_COORD_Y_END);
  endproperty



  // AR channel properties

  //valid values for arsize are 2 and 3 for 4B and 8B granularity
  property arsize_valid;
    arvalid |-> arsize inside {'d2, 'd3};
  endproperty



  // A burst must not cross a 4kbyte boundary
  wire [32:0] araddr_at_burst_end;
  assign araddr_at_burst_end = araddr + (arlen << arsize);



  property araddr_burst_within_4kb_boundary;
    arvalid |-> araddr[32:12] == araddr_at_burst_end[32:12];
  endproperty


  // if arvalid asserted, AR source id coords are within grid bounds
  property arsrcid_coords_within_grid;
    arvalid |-> (arsrcid.xcoord >= GRID_COORD_X_START) && (arsrcid.xcoord <= GRID_COORD_X_END) &&
                (arsrcid.ycoord >= GRID_COORD_Y_START) && (arsrcid.ycoord <= GRID_COORD_Y_END);
  endproperty



  // if arvalid asserted, AR target id coords are within grid bounds

  property artgtid_coords_within_grid;
    arvalid |-> (artgtid.xcoord >= GRID_COORD_X_START) && (artgtid.xcoord <= GRID_COORD_X_END) &&
                (artgtid.ycoord >= GRID_COORD_Y_START) && (artgtid.ycoord <= GRID_COORD_Y_END);
  endproperty



  // R - Read Data Channel properties


  logic [3:0] rvalid_cnt;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      rvalid_cnt <= 4'd0;
    end
    else if(rvalid && !rlast) begin
      rvalid_cnt <= rvalid_cnt + 4'd1;
    end
    else if(rvalid && rlast) begin
      rvalid_cnt <= 4'd0;
    end
  end
  
  // if RVALID without RLAST seen, then next cycle another RVALID will appear
  property rvalids_in_burst_are_consecutive;
    rvalid && !rlast |=> rvalid;
  endproperty


  // ttl is the same throughout a burst
  property read_resp_ttl_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(unoc_resp_bundle.ttl);
  endproperty

  // RIDs are the same throughout a burst
  property rids_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(rid);
  endproperty

  // RUSERs are the same throughout a burst
  property rusers_in_burst_same_throughout;
    rvalid && !rlast |=> $stable(ruser);
  endproperty

  //?? RIDs match previously sent ARIDs
  property rid_matches_previous_arid;
    rvalid |-> rid_match_seen;
  endproperty

  //?? RLAST is high when expected
  property rlast_as_expected;
    rvalid |-> rlast == (rlen == rvalid_cnt);
 endproperty

  // if rvalid asserted, R target id coords are within grid bounds
  property rtgtid_coords_within_grid;
    rvalid |-> (rtgtid.xcoord >= GRID_COORD_X_START) && (rtgtid.xcoord <= GRID_COORD_X_END) &&
               (rtgtid.ycoord >= GRID_COORD_Y_START) && (rtgtid.ycoord <= GRID_COORD_Y_END);
  endproperty


  // Other aux code
  logic rtr_is_tgt;
  assign rtr_is_tgt =  awvalid ? (awtgtid.xcoord == rtr_location.xcoord && awtgtid.ycoord == rtr_location.ycoord) :
                      (arvalid ? (artgtid.xcoord == rtr_location.xcoord && artgtid.ycoord == rtr_location.ycoord) :
                      (bvalid  ? (btgtid.xcoord  == rtr_location.xcoord && btgtid.ycoord  == rtr_location.ycoord) :
                      (rvalid  ?  (rtgtid.xcoord == rtr_location.xcoord && rtgtid.ycoord  == rtr_location.ycoord)  : 1'b0)));
  
  
  