/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_output_signal_defines.sv
// This file contains mnm dnoc output signal defines
/////////////////////////////////////////////////////////////////////////////////////////
    logic [mnm_pkg::MNM_DATA_NOC_CHANNEL_WIDTH-1:0]                   d_noc_out_channel;
    logic                                                             d_noc_out_is_aww_channel;
    logic                                                             d_noc_out_is_r_channel;

    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]                     d_noc_out_vc;
		logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]                        d_noc_out_len;
    logic [mnm_pkg::MNM_DAXI_ID_IID_WIDTH-1:0]                        d_noc_out_iid;
    logic                                                             d_noc_out_read;
    logic                                                             d_noc_out_last;
    mnm_pkg::coord_id_t                                               d_noc_out_tgtid;

		logic                                                             d_noc_out_awvalid;
		logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]                        d_noc_out_awlen;
		logic                                                             d_noc_out_wlast;
    logic [mnm_pkg::MNM_DAXI_AW_ID_WIDTH-1:0]                         d_noc_out_awid;
    logic [mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:0]                       d_noc_out_awaddr;
    logic [mnm_pkg::MNM_DAXI_AW_USER_WIDTH-1:0]                       d_noc_out_awuser;
    logic [mnm_pkg::MNM_DAXI_W_USER_WIDTH-1:0]                        d_noc_out_wuser;
    logic [mnm_pkg::MNM_DAXI_AWUSER_VC_WIDTH-1:0]                     d_noc_out_awuservc;
    logic [mnm_pkg::MNM_DAXI_AWUSER_NOC_ID_WIDTH-1:0]                 d_noc_out_awnocid;
    mnm_pkg::coord_id_t                                               d_noc_out_awsrcid;
    mnm_pkg::coord_id_t                                               d_noc_out_awtgtid;
    logic [mnm_pkg::MNM_DAXI_AWUSER_SIZE_WIDTH-1:0]                   d_noc_out_awsize;
    logic [mnm_pkg::MNM_DAXI_AWUSER_AMO_OP_WIDTH-1:0]                 d_noc_out_wstrb_amo_op;
    logic [mnm_pkg::MNM_DAXI_WSTRB_DAXI_WSTRB_FULL_WIDTH-1:0]         d_noc_out_wstrb_full;
    logic [mnm_pkg::MNM_DAXI_WSTRB_AMO_WSTRB_AMO_WIDTH-1:0]           d_noc_out_wstrb_amo;
    logic [mnm_pkg::MNM_DAXI_WSTRB_AMO_WSTRB_AMO_RSVD_WIDTH-1:0]      d_noc_out_wstrb_rsvd;

		logic                                                             d_noc_out_rvalid;
    logic [mnm_pkg::MNM_DAXI_AW_LEN_WIDTH-1:0]         		            d_noc_out_rlen;
    logic                                              		            d_noc_out_rlast;
    logic [mnm_pkg::MNM_DAXI_R_ID_WIDTH-1:0]                          d_noc_out_rid;
    logic [mnm_pkg::MNM_DAXI_R_USER_WIDTH-1:0]                        d_noc_out_ruser;
    logic [mnm_pkg::MNM_DAXI_RUSER_NOC_ID_WIDTH-1:0]                  d_noc_out_rnocid;
    mnm_pkg::coord_id_t                                               d_noc_out_rtgtid;
    mnm_pkg::coord_id_t                                               d_noc_out_rsrcid;
    logic [mnm_pkg::MNM_DAXI_RUSER_VC_WIDTH-1:0]                      d_noc_out_ruservc;

    assign d_noc_out_channel                               = d_noc_out.channel;
    assign d_noc_out_is_aww_channel                        = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_WRITE;
    assign d_noc_out_is_r_channel                          = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_READ ;
    
    assign d_noc_out_vc                                    = d_noc_out_is_aww_channel ? (d_noc_out.payload.daxi_combo_aw_w.aw.user.vc+ mnm_pkg::MNM_DNOC_R_NUM_VC):
                                                             d_noc_out_is_r_channel   ?  d_noc_out.payload.daxi_r.user.vc : 
                                                             '0;
    assign d_noc_out_len                                   = d_noc_out_is_aww_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.len:
                                                             d_noc_out_is_r_channel   ? d_noc_out.payload.daxi_r.user.len: 
                                                             '0;                                                        
    assign d_noc_out_iid                                   = d_noc_out_is_aww_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.id.iid :
                                                             d_noc_out_is_r_channel   ? d_noc_out.payload.daxi_r.id.iid : 
                                                             '0;      
    assign d_noc_out_read                                  = d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_READ;
    assign d_noc_out_last                                  = d_noc_out_read ? d_noc_out.payload.daxi_r.last : d_noc_out.payload.daxi_combo_aw_w.w.last;
    assign d_noc_out_tgtid                                 = d_noc_out_is_aww_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.user.tgt_id:
                                                             d_noc_out_is_r_channel   ? d_noc_out.payload.daxi_r.user.tgt_id: 
                                                             '0;

    assign d_noc_out_awvalid                               = d_noc_out_valid && d_noc_out_is_aww_channel;
    assign d_noc_out_awlen                                 = d_noc_out.payload.daxi_combo_aw_w.aw.len;
    assign d_noc_out_wlast                                 = d_noc_out.payload.daxi_combo_aw_w.w.last;
    assign d_noc_out_awid                                  = d_noc_out.payload.daxi_combo_aw_w.aw.id.iid;
    assign d_noc_out_awaddr                                = d_noc_out.payload.daxi_combo_aw_w.aw.addr;
    assign d_noc_out_awuser                                = d_noc_out.payload.daxi_combo_aw_w.aw.user;
    assign d_noc_out_wuser                                 = d_noc_out.payload.daxi_combo_aw_w.w.user;
    assign d_noc_out_awuservc                              = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    assign d_noc_out_awnocid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.noc_id;
    assign d_noc_out_awsrcid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.src_id;
    assign d_noc_out_awtgtid                               = d_noc_out.payload.daxi_combo_aw_w.aw.user.tgt_id;
    assign d_noc_out_awsize                                = d_noc_out.payload.daxi_combo_aw_w.aw.user.size;

    assign d_noc_out_wstrb_amo_op                          = d_noc_out.payload.daxi_combo_aw_w.aw.user.amo_op;
    assign d_noc_out_wstrb_full                            = d_noc_out.payload.daxi_combo_aw_w.w.strb.daxi_wstrb_full;
    assign d_noc_out_wstrb_amo                             = d_noc_out.payload.daxi_combo_aw_w.w.strb.daxi_wrstrb_amo.wstrb_amo;
    assign d_noc_out_wstrb_amo_rsvd                        = d_noc_out.payload.daxi_combo_aw_w.w.strb.daxi_wrstrb_amo.wstrb_amo_rsvd;
  
    assign d_noc_out_rvalid                                = d_noc_out_valid && d_noc_out_is_r_channel;
    assign d_noc_out_rlen                                  = d_noc_out.payload.daxi_r.user.len;
    assign d_noc_out_rlast                                 = d_noc_out.payload.daxi_r.last;
    assign d_noc_out_rid                                   = d_noc_out.payload.daxi_r.id.iid;
    assign d_noc_out_ruser                                 = d_noc_out.payload.daxi_r.user;
    assign d_noc_out_rnocid                                = d_noc_out.payload.daxi_r.user.noc_id;
    assign d_noc_out_rtgtid                                = d_noc_out.payload.daxi_r.user.tgt_id;
    assign d_noc_out_rsrcid                                = d_noc_out.payload.daxi_r.user.src_id;
    assign d_noc_out_ruservc                               = d_noc_out.payload.daxi_r.user.vc;