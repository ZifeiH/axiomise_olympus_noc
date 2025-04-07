/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_cnoc_signal_defines.sv
// This file contains cip router signals
/////////////////////////////////////////////////////////////////////////////////////////
//------------------------------------------------------------------------------
//-- Signal defines
//------------------------------------------------------------------------------

    logic [CIP_CNOC_TOTAL_NUM_VC_WIDTH-1:0]             cnoc_in_vc;
    logic [CIP_CNOC_TOTAL_NUM_VC_WIDTH-1:0]             cnoc_out_vc;

    logic [cip_pkg::CIP_DAXI_ARUSER_NOC_ID_WIDTH-1:0]   cnoc_in_arnoc_id;
    logic [cip_pkg::CIP_DAXI_ARUSER_NOC_ID_WIDTH-1:0]   cnoc_in_bnoc_id;

    logic [cip_pkg::CIP_DAXI_BUSER_NOC_ID_WIDTH-1:0]    cnoc_out_arnoc_id;
    logic [cip_pkg::CIP_DAXI_BUSER_NOC_ID_WIDTH-1:0]    cnoc_out_bnoc_id;

    logic [23:0]                                        disabled_pe;
    
    logic [cip_pkg::CIP_DAXI_ID_IID_WIDTH-1:0]          c_noc_out_iid;
    logic [cip_pkg::CIP_DAXI_ID_IID_WIDTH-1:0]          c_noc_in_iid;

    logic [XCOORD_WIDTH-1:0]                            cnoc_in_tgtid_xcoord;
    logic [YCOORD_WIDTH-1:0]                            cnoc_in_tgtid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                            cnoc_in_tgtid_zcoord;
    logic [ZCOORD_WIDTH-1:0]                            cnoc_in_tgtid_cip_id;

    logic [XCOORD_WIDTH-1:0]                            cnoc_in_srcid_xcoord;
    logic [YCOORD_WIDTH-1:0]                            cnoc_in_srcid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                            cnoc_in_srcid_zcoord;
    logic [ZCOORD_WIDTH-1:0]                            cnoc_in_srcid_cip_id;


    logic                                               cnoc_in_is_AR_channel;
    logic                                               cnoc_in_is_B_channel;
    logic                                               cnoc_out_is_AR_channel;
    logic                                               cnoc_out_is_B_channel;

    assign cnoc_in_vc                                   = cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.vc :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.vc  : 
                                                          '0;

    assign cnoc_out_vc                                  = cnoc_out_is_AR_channel ? c_noc_out.payload.daxi_ar.user.vc :
                                                          cnoc_out_is_B_channel  ? c_noc_out.payload.daxi_b.user.vc  : 
                                                          '0;

    assign cnoc_in_is_AR_channel                        = c_noc_in.channel  == cip_pkg::NOC_CHANNEL_E_READ ;
    assign cnoc_in_is_B_channel                         = c_noc_in.channel  == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign cnoc_out_is_AR_channel                       = c_noc_out.channel == cip_pkg::NOC_CHANNEL_E_READ ;
    assign cnoc_out_is_B_channel                        = c_noc_out.channel == cip_pkg::NOC_CHANNEL_E_WRITE;

    assign cnoc_in_bnoc_id                              = c_noc_in.payload.daxi_b.user.noc_id;
    assign cnoc_in_arnoc_id                             = c_noc_in.payload.daxi_ar.user.noc_id;
    assign cnoc_out_arnoc_id                            = c_noc_out.payload.daxi_ar.user.noc_id;

    assign c_noc_in_iid                                 = cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.id.iid :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.id.iid  : 
                                                          '0;

    assign c_noc_out_iid                                 = cnoc_out_is_AR_channel ? c_noc_out.payload.daxi_ar.id.iid :
                                                           cnoc_out_is_B_channel  ? c_noc_out.payload.daxi_b.id.iid  : 
                                                           '0;

    assign cnoc_in_tgtid_xcoord                         = cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.tgt_id.xcoord :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.tgt_id.xcoord  : 
                                                          '0;

    assign cnoc_in_tgtid_ycoord                         =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.tgt_id.ycoord :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.tgt_id.ycoord  : 
                                                          '0;

    assign cnoc_in_tgtid_cip_id                         =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.tgt_id.cip_id :
                                                           cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.tgt_id.cip_id  : 
                                                           '0;


    assign cnoc_in_srcid_xcoord                         = cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.src_id.xcoord :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.src_id.xcoord  : 
                                                          '0;

    assign cnoc_in_srcid_ycoord                        =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.src_id.ycoord :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.src_id.ycoord  : 
                                                          '0;

    assign cnoc_in_srcid_zcoord                        =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.src_id.zcoord :
                                                          cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.src_id.zcoord  : 
                                                          '0;

    assign cnoc_in_srcid_cip_id                         =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.src_id.cip_id :
                                                           cnoc_in_is_B_channel  ? c_noc_in.payload.daxi_b.user.src_id.cip_id  : 
                                                           '0;
    assign cnoc_in_tgtid_zcoord                        =  cnoc_in_is_AR_channel ? c_noc_in.payload.daxi_ar.user.tgt_id.zcoord :
                                                          cnoc_in_is_B_channel ? c_noc_in.payload.daxi_b.user.tgt_id.zcoord   : 
                                                          '0;

  
