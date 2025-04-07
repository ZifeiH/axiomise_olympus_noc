/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_input_signal_defines.sv
// This file contains mnm dnoc input signal defines
/////////////////////////////////////////////////////////////////////////////////////////
    logic [mnm_pkg::MNM_DATA_NOC_CHANNEL_WIDTH-1:0]                   d_noc_in_channel;
    logic                                                             d_noc_in_is_aww_channel;
    logic                                                             d_noc_in_is_r_channel;

    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]                     d_noc_in_vc;
    logic [mnm_pkg::MNM_DAXI_ID_IID_WIDTH-1:0]                        d_noc_in_iid;
    logic                                                             d_noc_in_read;
    logic                                                             d_noc_in_last;
    mnm_pkg::coord_id_t                                               d_noc_in_tgtid;

		logic                                                             d_noc_in_awvalid;
		logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]                        d_noc_in_awlen;
		logic                                                             d_noc_in_wlast;
    logic [mnm_pkg::MNM_DAXI_AW_ID_WIDTH-1:0]                         d_noc_in_awid;
    logic [mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:0]                       d_noc_in_awaddr;
    logic [mnm_pkg::MNM_DAXI_AW_USER_WIDTH-1:0]                       d_noc_in_awuser;
    logic [mnm_pkg::MNM_DAXI_W_USER_WIDTH-1:0]                        d_noc_in_wuser;
    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]                     d_noc_in_awuservc;
    logic [mnm_pkg::MNM_DAXI_AWUSER_NOC_ID_WIDTH-1:0]                 d_noc_in_awnocid;
    mnm_pkg::coord_id_t                                               d_noc_in_awsrcid;
    mnm_pkg::coord_id_t                                               d_noc_in_awtgtid;
    logic [mnm_pkg::MNM_DAXI_AWUSER_SIZE_WIDTH-1:0]                   d_noc_in_awsize;
    logic [mnm_pkg::MNM_DAXI_AWUSER_AMO_OP_WIDTH-1:0]                 d_noc_in_wstrb_amo_op;
    logic [mnm_pkg::MNM_DAXI_WSTRB_DAXI_WSTRB_FULL_WIDTH-1:0]         d_noc_in_wstrb_full;
    logic [mnm_pkg::MNM_DAXI_WSTRB_AMO_WSTRB_AMO_WIDTH-1:0]           d_noc_in_wstrb_amo;
    logic [mnm_pkg::MNM_DAXI_WSTRB_AMO_WSTRB_AMO_RSVD_WIDTH-1:0]      d_noc_in_wstrb_rsvd;

		logic                                                             d_noc_in_rvalid;
    logic [mnm_pkg::MNM_DAXI_RUSER_LEN_WIDTH-1:0]                     d_noc_in_rlen;
    logic                                                          		d_noc_in_rlast;
    logic [mnm_pkg::MNM_DAXI_R_ID_WIDTH-1:0]                          d_noc_in_rid;
    logic [mnm_pkg::MNM_DAXI_R_USER_WIDTH-1:0]                        d_noc_in_ruser;
    logic [mnm_pkg::MNM_DAXI_RUSER_NOC_ID_WIDTH-1:0]                  d_noc_in_rnocid;
    mnm_pkg::coord_id_t                                               d_noc_in_rtgtid;
    logic [mnm_pkg::MNM_DAXI_RUSER_VC_WIDTH-1:0]                      d_noc_in_ruservc;
    
    assign d_noc_in_channel                               = d_noc_in.channel;
    assign d_noc_in_is_aww_channel                        = d_noc_in.channel == mnm_pkg::DNOC_CHANNEL_E_WRITE;
    assign d_noc_in_is_r_channel                          = d_noc_in.channel == mnm_pkg::DNOC_CHANNEL_E_READ ;
   
    assign d_noc_in_vc                                    = d_noc_in_is_aww_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.vc:
                                                            d_noc_in_is_r_channel   ? d_noc_in.payload.daxi_r.user.vc : 
                                                            '0;
    assign d_noc_in_iid                                   = d_noc_in_is_aww_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.id.iid :
                                                            d_noc_in_is_r_channel   ? d_noc_in.payload.daxi_r.id.iid : 
                                                            '0; 
    assign d_noc_in_read                                  = d_noc_in.channel == mnm_pkg::DNOC_CHANNEL_E_READ;
    assign d_noc_in_last                                  = d_noc_in_read ? d_noc_in.payload.daxi_r.last : d_noc_in.payload.daxi_combo_aw_w.w.last;
    assign d_noc_in_tgtid                                 = d_noc_in_is_aww_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id:
                                                            d_noc_in_is_r_channel   ? d_noc_in.payload.daxi_r.user.tgt_id: 
                                                            '0;

    assign d_noc_in_awvalid                               = d_noc_in_valid && d_noc_in_is_aww_channel;
    assign d_noc_in_awlen                                 = d_noc_in.payload.daxi_combo_aw_w.aw.len;
    assign d_noc_in_wlast                                 = d_noc_in.payload.daxi_combo_aw_w.w.last;
    assign d_noc_in_awid                                  = d_noc_in.payload.daxi_combo_aw_w.aw.id.iid;
    assign d_noc_in_awaddr                                = d_noc_in.payload.daxi_combo_aw_w.aw.addr;
    assign d_noc_in_awuser                                = d_noc_in.payload.daxi_combo_aw_w.aw.user;
    assign d_noc_in_wuser                                 = d_noc_in.payload.daxi_combo_aw_w.w.user;
    assign d_noc_in_awuservc                              = d_noc_in.payload.daxi_combo_aw_w.aw.user.vc;
    assign d_noc_in_awnocid                               = d_noc_in.payload.daxi_combo_aw_w.aw.user.noc_id;
    assign d_noc_in_awsrcid                               = d_noc_in.payload.daxi_combo_aw_w.aw.user.src_id;
    assign d_noc_in_awtgtid                               = d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id;
    assign d_noc_in_awsize                                = d_noc_in.payload.daxi_combo_aw_w.aw.user.size;

    assign d_noc_in_wstrb_amo_op                          = d_noc_in.payload.daxi_combo_aw_w.aw.user.amo_op;
    assign d_noc_in_wstrb_full                            = d_noc_in.payload.daxi_combo_aw_w.w.strb.daxi_wstrb_full;
    assign d_noc_in_wstrb_amo                             = d_noc_in.payload.daxi_combo_aw_w.w.strb.daxi_wrstrb_amo.wstrb_amo;
    assign d_noc_in_wstrb_amo_rsvd                        = d_noc_in.payload.daxi_combo_aw_w.w.strb.daxi_wrstrb_amo.wstrb_amo_rsvd;
  
    assign d_noc_in_rvalid                                = d_noc_in_valid && d_noc_in_is_r_channel;
    assign d_noc_in_rlen                                  = d_noc_in.payload.daxi_r.user.len;
    assign d_noc_in_rlast                                 = d_noc_in.payload.daxi_r.last;
    assign d_noc_in_rid                                   = d_noc_in.payload.daxi_r.id.iid;
    assign d_noc_in_ruser                                 = d_noc_in.payload.daxi_r.user;
    assign d_noc_in_rnocid                                = d_noc_in.payload.daxi_r.user.noc_id;
    assign d_noc_in_rtgtid                                = d_noc_in.payload.daxi_r.user.tgt_id;
    assign d_noc_in_ruservc                               = d_noc_in.payload.daxi_r.user.vc;