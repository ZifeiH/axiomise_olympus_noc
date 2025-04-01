///////////////////////////////////////////////////
/// File: cip_rtr_unoc_FBAXI_signal_defines.sv
/// This file contains the signal defines being used in constrains file
///////////////////////////////////////////////////



    logic [VC_WIDTH-1:0]                               u_noc_in_AW_W_vc;
    logic [VC_WIDTH-1:0]                               u_noc_out_AW_W_vc;
    cip_pkg::unoc_channel_e                            u_noc_in_channel;
    cip_pkg::unoc_channel_e                            u_noc_out_channel;                        

    logic                                              unoc_AW_originator_is_CCP;
    logic                                              unoc_AW_originator_is_PCIE;

    logic                                              unoc_in_is_AW_W_channel, unoc_in_is_B_channel,unoc_in_is_R_channel, unoc_in_is_AR_channel;
    logic                                              unoc_out_is_AW_W_channel, unoc_out_is_B_channel, unoc_out_is_AR_channel, unoc_out_is_R_channel;

    logic                                              unoc_in_awvalid;
    logic [cip_pkg::CIP_UAXI_AW_ADDR_WIDTH-1:0]        unoc_in_awaddr;
    logic [cip_pkg::CIP_UAXI_AW_USER_WIDTH-1:0]        unoc_in_awuser;
                                              
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_in_awlen;
    logic [cip_pkg::CIP_UAXI_AW_SIZE_WIDTH-1:0]        unoc_in_awsize;
    logic [cip_pkg::CIP_UAXI_AW_ID_WIDTH-1:0]          unoc_in_awid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_in_awiid;
    logic                                              unoc_in_wlast;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         wdata_items_seen_AW;  // unoc_in_channel
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         wdata_items_seen_R;  // unoc_in_channel

    //b channel
    logic                                              unoc_in_bvalid;
    logic [cip_pkg::CIP_UAXI_B_ID_WIDTH-1:0]           unoc_in_bid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_in_biid;
    logic [cip_pkg::CIP_UAXI_B_USER_WIDTH-1:0]         unoc_in_buser;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_in_blen;

    //ar channel
    logic                                              unoc_in_arvalid;
    logic [cip_pkg::CIP_UAXI_AR_ID_WIDTH-1:0]          unoc_in_arid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_in_ariid;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_in_arlen;
    logic [cip_pkg::CIP_UAXI_AR_USER_WIDTH-1:0]        unoc_in_aruser;
    logic [cip_pkg::CIP_UAXI_AR_SIZE_WIDTH-1:0]        unoc_in_arsize;
    logic [cip_pkg::CIP_UAXI_AR_ADDR_WIDTH-1:0]        unoc_in_araddr;

    //r channel
    logic                                              unoc_in_rvalid;
    logic [cip_pkg::CIP_UAXI_R_ID_WIDTH-1:0]           unoc_in_rid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_in_riid;
    logic [cip_pkg::CIP_UAXI_R_USER_WIDTH-1:0]         unoc_in_ruser;
    logic                                              unoc_in_rlast;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_in_rlen;

    
    logic [XCOORD_WIDTH-1:0]                           unoc_in_tgtid_xcoord;
    logic [YCOORD_WIDTH-1:0]                           unoc_in_tgtid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                           unoc_in_tgtid_zcoord;
    logic [cip_pkg::CIP_ID_WIDTH-1:0]                  unoc_in_tgtid_cip_id;

    logic [XCOORD_WIDTH-1:0]                           unoc_in_srcid_xcoord;
    logic [YCOORD_WIDTH-1:0]                           unoc_in_srcid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                           unoc_in_srcid_zcoord;
    logic [cip_pkg::CIP_ID_WIDTH-1:0]                  unoc_in_srcid_cip_id;

    logic [XCOORD_WIDTH-1:0]                           unoc_out_srcid_xcoord;
    logic [YCOORD_WIDTH-1:0]                           unoc_out_srcid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                           unoc_out_srcid_zcoord;
    logic [cip_pkg::CIP_ID_WIDTH-1:0]                  unoc_out_srcid_cip_id;

    logic [XCOORD_WIDTH-1:0]                           unoc_in_resp_orgid_xcoord;
    logic [YCOORD_WIDTH-1:0]                           unoc_in_resp_orgid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                           unoc_in_resp_orgid_zcoord;
    logic [cip_pkg::CIP_ID_WIDTH-1:0]                  unoc_in_resp_orgid_cip_id;

    logic                                              unoc_out_awvalid;
    logic [cip_pkg::CIP_UAXI_AW_ADDR_WIDTH-1:0]        unoc_out_awaddr;
    logic [cip_pkg::CIP_UAXI_AW_USER_WIDTH-1:0]        unoc_out_awuser;
                                              
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_out_awlen;
    logic [cip_pkg::CIP_UAXI_AW_SIZE_WIDTH-1:0]        unoc_out_awsize;
    logic [cip_pkg::CIP_UAXI_AW_ID_WIDTH-1:0]          unoc_out_awid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_out_awiid;
    logic                                              unoc_out_wlast;

    //b channel
    logic                                              unoc_out_bvalid;
    logic [cip_pkg::CIP_UAXI_B_ID_WIDTH-1:0]           unoc_out_bid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_out_biid;
    logic [cip_pkg::CIP_UAXI_B_USER_WIDTH-1:0]         unoc_out_buser;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_out_blen;

    //ar channel
    logic                                              unoc_out_arvalid;
    logic [cip_pkg::CIP_UAXI_AR_ID_WIDTH-1:0]          unoc_out_arid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_out_ariid;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_out_arlen;
    logic [cip_pkg::CIP_UAXI_AR_USER_WIDTH-1:0]        unoc_out_aruser;
    logic [cip_pkg::CIP_UAXI_AR_SIZE_WIDTH-1:0]        unoc_out_arsize;
    logic [cip_pkg::CIP_UAXI_AR_ADDR_WIDTH-1:0]        unoc_out_araddr;

    //r channel
    logic                                              unoc_out_rvalid;
    logic [cip_pkg::CIP_UAXI_R_ID_WIDTH-1:0]           unoc_out_rid;
    logic [cip_pkg::CIP_UAXI_ID_IID_WIDTH-1:0]         unoc_out_riid;
    logic [cip_pkg::CIP_UAXI_R_USER_WIDTH-1:0]         unoc_out_ruser;
    logic                                              unoc_out_rlast;
    logic [cip_pkg::CIP_UAXI_ID_LEN_WIDTH-1:0]         unoc_out_rlen;

    logic                                              y_first;

    assign u_noc_in_AW_W_vc                            = u_noc_in.payload.uaxi_combo_aw_w.aw.user.vc;
    assign u_noc_in_channel                            = u_noc_in.channel;
    assign u_noc_out_AW_W_vc                           = u_noc_out.payload.uaxi_combo_aw_w.aw.user.vc;
    assign u_noc_out_channel                           = u_noc_out.channel;

    assign unoc_in_is_AW_W_channel                     = u_noc_in_channel == `write_req ;
    assign unoc_in_is_R_channel                        = u_noc_in_channel == `read_resp ;
    assign unoc_in_is_AR_channel                       = u_noc_in_channel == `read_req  ;
    assign unoc_in_is_B_channel                        = u_noc_in_channel == `write_resp;

    assign unoc_out_is_AW_W_channel                    = u_noc_out_channel == `write_req ;
    assign unoc_out_is_R_channel                       = u_noc_out_channel == `read_resp ;
    assign unoc_out_is_AR_channel                      = u_noc_out_channel == `read_req  ;
    assign unoc_out_is_B_channel                       = u_noc_out_channel == `write_resp;

    assign unoc_in_awvalid                             = u_noc_in_valid && unoc_in_is_AW_W_channel;
    assign unoc_in_awuser                              = u_noc_in.payload.uaxi_combo_aw_w.aw.user;
    assign unoc_in_awlen                               = u_noc_in.payload.uaxi_combo_aw_w.aw.id.len;
    assign unoc_in_awsize                              = u_noc_in.payload.uaxi_combo_aw_w.aw.size;
    assign unoc_in_awaddr                              = u_noc_in.payload.uaxi_combo_aw_w.aw.addr;
    assign unoc_in_awid                                = u_noc_in.payload.uaxi_combo_aw_w.aw.id;
    assign unoc_in_awiid                               = u_noc_in.payload.uaxi_combo_aw_w.aw.id.iid;
    assign unoc_in_wlast                               = u_noc_in.payload.uaxi_combo_aw_w.w.last;

    assign unoc_in_bvalid                              = u_noc_in_valid && unoc_in_is_B_channel;
    assign unoc_in_bid                                 = u_noc_in.payload.uaxi_b.id;
    assign unoc_in_biid                                = u_noc_in.payload.uaxi_b.id.iid;
    assign unoc_in_buser                               = u_noc_in.payload.uaxi_b.user;
    assign unoc_in_bsrcid                              = u_noc_in.payload.uaxi_b.user.src_id;
    assign unoc_in_btgtid                              = u_noc_in.payload.uaxi_b.id.originator_id; 
    assign unoc_in_blen                                = u_noc_in.payload.uaxi_b.id.len;
    
    assign unoc_in_arvalid                             = u_noc_in_valid && unoc_in_is_AR_channel;
    assign unoc_in_arid                                = u_noc_in.payload.uaxi_ar.id;
    assign unoc_in_ariid                               = u_noc_in.payload.uaxi_ar.id.iid;
    assign unoc_in_arlen                               = u_noc_in.payload.uaxi_ar.id.len;
    assign unoc_in_aruser                              = u_noc_in.payload.uaxi_ar.user;
    assign unoc_in_arsize                              = u_noc_in.payload.uaxi_ar.size;
    assign unoc_in_araddr                              = u_noc_in.payload.uaxi_ar.addr;
    assign unoc_in_arsrcid                             = u_noc_in.payload.uaxi_ar.id.originator_id;
    assign unoc_in_artgtid                             = u_noc_in.payload.uaxi_ar.user.tgt_id;

    assign unoc_in_rvalid                              = u_noc_in_valid && unoc_in_is_R_channel;
    assign unoc_in_rid                                 = u_noc_in.payload.uaxi_r.id;
    assign unoc_in_riid                                = u_noc_in.payload.uaxi_r.id.iid;
    assign unoc_in_ruser                               = u_noc_in.payload.uaxi_r.user;
    assign unoc_in_rlast                               = u_noc_in.payload.uaxi_r.last;
    assign unoc_in_rlen                                = u_noc_in.payload.uaxi_r.id.len;

    assign unoc_out_awvalid                             = u_noc_out_valid && unoc_out_is_AW_W_channel;
    assign unoc_out_awuser                              = u_noc_out.payload.uaxi_combo_aw_w.aw.user;
    assign unoc_out_awlen                               = u_noc_out.payload.uaxi_combo_aw_w.aw.id.len;
    assign unoc_out_awsize                              = u_noc_out.payload.uaxi_combo_aw_w.aw.size;
    assign unoc_out_awaddr                              = u_noc_out.payload.uaxi_combo_aw_w.aw.addr;
    assign unoc_out_awid                                = u_noc_out.payload.uaxi_combo_aw_w.aw.id;
    assign unoc_out_awiid                               = u_noc_out.payload.uaxi_combo_aw_w.aw.id.iid;
    assign unoc_out_wlast                               = u_noc_out.payload.uaxi_combo_aw_w.w.last;

    assign unoc_out_bvalid                              = u_noc_out_valid && unoc_out_is_B_channel;
    assign unoc_out_bid                                 = u_noc_out.payload.uaxi_b.id;
    assign unoc_out_biid                                = u_noc_out.payload.uaxi_b.id.iid;
    assign unoc_out_buser                               = u_noc_out.payload.uaxi_b.user;
    assign unoc_out_bsrcid                              = u_noc_out.payload.uaxi_b.user.src_id;
    assign unoc_out_btgtid                              = u_noc_out.payload.uaxi_b.id.originator_id; 
    assign unoc_out_blen                                = u_noc_out.payload.uaxi_b.id.len;
    
    assign unoc_out_arvalid                             = u_noc_out_valid && unoc_out_is_AR_channel;
    assign unoc_out_arid                                = u_noc_out.payload.uaxi_ar.id;
    assign unoc_out_ariid                               = u_noc_out.payload.uaxi_ar.id.iid;
    assign unoc_out_arlen                               = u_noc_out.payload.uaxi_ar.id.len;
    assign unoc_out_aruser                              = u_noc_out.payload.uaxi_ar.user;
    assign unoc_out_arsize                              = u_noc_out.payload.uaxi_ar.size;
    assign unoc_out_araddr                              = u_noc_out.payload.uaxi_ar.addr;
    assign unoc_out_arsrcid                             = u_noc_out.payload.uaxi_ar.id.originator_id;
    assign unoc_out_artgtid                             = u_noc_out.payload.uaxi_ar.user.tgt_id;

    assign unoc_out_rvalid                              = u_noc_out_valid && unoc_out_is_R_channel;
    assign unoc_out_rid                                 = u_noc_out.payload.uaxi_r.id;
    assign unoc_out_riid                                = u_noc_out.payload.uaxi_r.id.iid;
    assign unoc_out_ruser                               = u_noc_out.payload.uaxi_r.user;
    assign unoc_out_rlast                               = u_noc_out.payload.uaxi_r.last;
    assign unoc_out_rlen                                = u_noc_out.payload.uaxi_r.id.len;

    assign is_y_first                                  = unoc_in_awvalid || unoc_in_arvalid;


    assign unoc_in_tgtid_xcoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.user.tgt_id.xcoord      :
                                                         unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.user.tgt_id.xcoord                 : 
                                                         unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.xcoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.xcoord             : 
                                                         '0;

    assign unoc_in_tgtid_ycoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.user.tgt_id.ycoord      :
                                                         unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.user.tgt_id.ycoord                 : 
                                                         unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.ycoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.ycoord             : 
                                                         '0;

    assign unoc_in_tgtid_zcoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.user.tgt_id.zcoord      :
                                                         unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.user.tgt_id.zcoord                 : 
                                                         unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.zcoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.zcoord             : 
                                                         '0;

    assign unoc_in_tgtid_cip_id                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.user.tgt_id.cip_id      :
                                                         unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.user.tgt_id.cip_id                 : 
                                                         unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.cip_id             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.cip_id             : 
                                                         '0;

    assign unoc_in_resp_orgid_xcoord                   = unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.xcoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.xcoord             : 
                                                         '0;

    assign unoc_in_resp_orgid_ycoord                   = unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.ycoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.ycoord             : 
                                                         '0;

    assign unoc_in_resp_orgid_zcoord                   = unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.zcoord             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.zcoord             : 
                                                         '0;

    assign unoc_in_resp_orgid_cip_id                   = unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.id.originator_id.cip_id             :
                                                         unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.id.originator_id.cip_id             : 
                                                         '0;

    assign unoc_in_srcid_xcoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.id.originator_id.xcoord :
                                                          unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.id.originator_id.xcoord            : 
                                                          unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.user.src_id.xcoord                  :
                                                          unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.user.src_id.xcoord                  : 
                                                          '0;

    assign unoc_in_srcid_ycoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.id.originator_id.ycoord :
                                                          unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.id.originator_id.ycoord            : 
                                                          unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.user.src_id.ycoord                  :
                                                          unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.user.src_id.ycoord                  : 
                                                          '0;

    assign unoc_in_srcid_zcoord                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.id.originator_id.zcoord :
                                                          unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.id.originator_id.zcoord            : 
                                                          unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.user.src_id.zcoord                  :
                                                          unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.user.src_id.zcoord                  : 
                                                          '0;

    assign unoc_in_srcid_cip_id                        = unoc_in_is_AW_W_channel ? u_noc_in.payload.uaxi_combo_aw_w.aw.id.originator_id.cip_id :
                                                          unoc_in_is_AR_channel   ? u_noc_in.payload.uaxi_ar.id.originator_id.cip_id            : 
                                                          unoc_in_is_R_channel    ? u_noc_in.payload.uaxi_r.user.src_id.cip_id                  :
                                                          unoc_in_is_B_channel    ? u_noc_in.payload.uaxi_b.user.src_id.cip_id                  : 
                                                          '0;

    assign unoc_out_srcid_xcoord                        = unoc_out_is_AW_W_channel ? u_noc_out.payload.uaxi_combo_aw_w.aw.id.originator_id.xcoord :
                                                          unoc_out_is_AR_channel   ? u_noc_out.payload.uaxi_ar.id.originator_id.xcoord            : 
                                                          unoc_out_is_R_channel    ? u_noc_out.payload.uaxi_r.user.src_id.xcoord                  :
                                                          unoc_out_is_B_channel    ? u_noc_out.payload.uaxi_b.user.src_id.xcoord                  : 
                                                          '0;

    assign unoc_out_srcid_ycoord                        = unoc_out_is_AW_W_channel ? u_noc_out.payload.uaxi_combo_aw_w.aw.id.originator_id.ycoord :
                                                          unoc_out_is_AR_channel   ? u_noc_out.payload.uaxi_ar.id.originator_id.ycoord            : 
                                                          unoc_out_is_R_channel    ? u_noc_out.payload.uaxi_r.user.src_id.ycoord                  :
                                                          unoc_out_is_B_channel    ? u_noc_out.payload.uaxi_b.user.src_id.ycoord                  : 
                                                          '0;

    assign unoc_out_srcid_zcoord                        = unoc_out_is_AW_W_channel ? u_noc_out.payload.uaxi_combo_aw_w.aw.id.originator_id.zcoord :
                                                          unoc_out_is_AR_channel   ? u_noc_out.payload.uaxi_ar.id.originator_id.zcoord            : 
                                                          unoc_out_is_R_channel    ? u_noc_out.payload.uaxi_r.user.src_id.zcoord                  :
                                                          unoc_out_is_B_channel    ? u_noc_out.payload.uaxi_b.user.src_id.zcoord                  : 
                                                          '0;

    assign unoc_out_srcid_cip_id                        = unoc_out_is_AW_W_channel ? u_noc_out.payload.uaxi_combo_aw_w.aw.id.originator_id.cip_id :
                                                          unoc_out_is_AR_channel   ? u_noc_out.payload.uaxi_ar.id.originator_id.cip_id            : 
                                                          unoc_out_is_R_channel    ? u_noc_out.payload.uaxi_r.user.src_id.cip_id                  :
                                                          unoc_out_is_B_channel    ? u_noc_out.payload.uaxi_b.user.src_id.cip_id                  : 
                                                          '0;

