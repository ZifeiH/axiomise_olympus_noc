
    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_out_vc;
    logic [mnm_pkg::MNM_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_out_channel;
    logic                                                 d_noc_out_is_aww_channel
    logic                                                 d_noc_out_is_r_channel;

    logic [mnm_pkg::MNM_DAXI_ID_IID_WIDTH-1:0]            d_noc_out_iid;
    logic                                                 d_noc_out_read;
    logic                                                 d_noc_out_last;

		logic                                                 d_noc_out_awvalid;
		logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]            d_noc_out_awlen;
		logic                                                 d_noc_out_wlast;
    logic [11-1:0]                                        d_noc_out_wid;
    logic [mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:0]           d_noc_out_awaddr;
    logic [mnm_pkg::MNM_DAXI_AW_CACHE_WIDTH-1:0]          d_noc_out_awcache;
    logic [mnm_pkg::MNM_DAXI_AW_LOCK_WIDTH-1:0]           d_noc_out_awlock;
    logic [mnm_pkg::MNM_DAXI_AW_USER_WIDTH-1:0]           d_noc_out_awuser;
    logic [mnm_pkg::MNM_DAXI_W_USER_WIDTH-1:0]            d_noc_out_wuser;
    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_out_awuservc;
    logic [mnm_pkg::MNM_DAXI_AWUSER_NOC_ID_WIDTH-1:0]     d_noc_out_awnocid;
    logic mnm_pkg::coord_id_t                             d_noc_out_awsrcid;
    logic mnm_pkg::coord_id_t                             d_noc_out_awtgtid;
    logic [mnm_pkg::MNM_DAXI_AWUSER_HOST_WIDTH-1:0]       awhost;
    logic [2:0]                                           d_noc_out_awsize;
    logic [3:0]                                           d_noc_out_awuser_reduction_type;


		logic                                                 d_noc_out_rvalid;
    logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]         		d_noc_out_rlen;
    logic                                              		d_noc_out_rlast;
    logic [11-1:0]                                        d_noc_out_rid;
    logic [mnm_pkg::MNM_DAXI_R_USER_WIDTH-1:0]            d_noc_out_ruser;
    logic [mnm_pkg::MNM_DAXI_RUSER_NOC_ID_WIDTH-1:0]      d_noc_out_rnocid;
    logic mnm_pkg::coord_id_t                             d_noc_out_rtgtid;
    logic [mnm_pkg::MNM_DAXI_RUSER_CC_DIR_WIDTH-1:0]      d_noc_out_rcc_dir;
    logic mnm_pkg::amo_opcode_e                           d_noc_out_rcc_opcode;
    logic [mnm_pkg::MNM_DAXI_RUSER_CC_LANE_WIDTH-1:0]     d_noc_out_rcc_lane;


    assign d_noc_out_vc                                    = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    
    assign d_noc_out_channel                               = d_noc_out.channel;
    assign d_noc_out_is_aww_channel                        = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_WRITE;
    assign d_noc_out_is_r_channel                          = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_READ ;

    assign d_noc_out_iid                                   = d_noc_out_is_aww_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.id.iid :
                                                             d_noc_out_is_r_channel   ? d_noc_out.payload.daxi_r.id.iid : 
                                                             '0;
    
      
    assign d_noc_out_read                                  = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_READ;
    
    assign d_noc_out_last                                  = d_noc_out_read ? d_noc_out.payload.daxi_r.last : d_noc_out.payload.daxi_combo_aw_w.w.last;


    assign d_noc_out_awvalid                               = d_noc_out_valid && d_noc_out_is_aww_channel;
    assign d_noc_out_awlen                                 = d_noc_out.payload.daxi_combo_aw_w.aw.len;
    assign d_noc_out_wlast                                 = d_noc_out.payload.daxi_combo_aw_w.w.last;
    assign d_noc_out_wid                                   = d_noc_out.payload.daxi_combo_aw_w.aw.id.iid;
    assign d_noc_out_awaddr                                = d_noc_out.payload.daxi_combo_aw_w.aw.addr;
    // assign d_noc_out_awcache                               = d_noc_out.payload.daxi_combo_aw_w.aw.cache;
    // assign d_noc_out_awlock                                = d_noc_out.payload.daxi_combo_aw_w.aw.lock;
    assign d_noc_out_awuser                                = d_noc_out.payload.daxi_combo_aw_w.aw.user;
    assign d_noc_out_wuser                                 = d_noc_out.payload.daxi_combo_aw_w.w.user;
    assign d_noc_out_awuservc                              = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    // assign d_noc_out_awhost                                = d_noc_out.payload.daxi_combo_aw_w.aw.user.host;
    assign d_noc_out_awnocid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.noc_id;
    assign d_noc_out_awsrcid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.src_id;
    assign d_noc_out_awtgtid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.tgt_id;
    // assign d_noc_out_awsize                                = d_noc_out.payload.daxi_combo_aw_w.w.strb.size;

    // assign d_noc_out_wstrb_beat_offset                     = d_noc_out.payload.daxi_combo_aw_w.w.strb.beat_offset;
    // assign d_noc_out_wstrb_subf                            = d_noc_out.payload.daxi_combo_aw_w.w.strb.subf;
    // assign d_noc_out_wstrb_rord                            = d_noc_out.payload.daxi_combo_aw_w.w.strb.rord;

    // assign d_noc_out_awuser_reduction_type                 = 

    assign d_noc_out_rvalid                                = d_noc_out_valid && d_noc_out_is_r_channel;
    assign d_noc_out_rlen                                  = d_noc_out.payload.daxi_r.user.len;
    assign d_noc_out_rlast                                 = d_noc_out.payload.daxi_r.last;
    assign d_noc_out_rid                                   = d_noc_out.payload.daxi_r.id.iid;
    assign d_noc_out_ruser                                 = d_noc_out.payload.daxi_r.user;
    assign d_noc_out_rnocid                                = d_noc_out.payload.daxi_r.user.noc_id;
    assign d_noc_out_rtgtid                                = d_noc_out.payload.daxi_r.user.tgt_id;
    // assign d_noc_out_rcc_dir                               = d_noc_out.payload.daxi_r.user.cc_dir;
    // assign d_noc_out_rcc_lane                              = d_noc_out.payload.daxi_r.user.cc_lane;
    