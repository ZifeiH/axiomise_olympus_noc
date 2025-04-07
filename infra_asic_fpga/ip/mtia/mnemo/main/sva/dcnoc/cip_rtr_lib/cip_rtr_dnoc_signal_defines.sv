/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_dnoc_signal_defines.sv
// This file contains cip router signals
/////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- Signal defines for cip_rtr_unoc_checker_sva.sv --
//------------------------------------------------------------------------------

    logic [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_in_vc;
    logic [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_out_vc;

    logic [cip_pkg::CIP_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_in_channel;
    logic [cip_pkg::CIP_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_out_channel;

    logic                                                 dnoc_in_is_AW_W_channel, dnoc_in_is_R_channel;
    logic                                                 dnoc_out_is_AW_channel, dnoc_out_is_R_channel;
    
    logic [cip_pkg::CIP_DAXI_ID_IID_WIDTH-1:0]            d_noc_in_iid;
    logic [cip_pkg::CIP_DAXI_ID_IID_WIDTH-1:0]            d_noc_out_iid;

		logic                                                	d_noc_in_awvalid;
		logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]            d_noc_in_awlen;
		logic                                                 d_noc_in_wlast;

    logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]         		d_noc_in_rlen;
    logic                                              		d_noc_in_rlast;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_OPCODE_WIDTH-1:0]   d_noc_in_rcc_opcode;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_LANE_WIDTH-1:0]  		d_noc_in_rcc_lane;
    logic [cip_pkg::CIP_DAXI_RUSER_PE_IN_CC_WIDTH-1:0] 		d_noc_in_rpe_in_cc;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH-1:0]   		d_noc_in_rcc_dir;    

    logic                                              		d_noc_out_awvalid;
    logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]         		d_noc_out_awlen;
    logic                                              		d_noc_out_wlast;

    logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]         		d_noc_out_rlen;
    logic                                              		d_noc_out_rlast;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_OPCODE_WIDTH-1:0]   d_noc_out_rcc_opcode;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_LANE_WIDTH-1:0]  		d_noc_out_rcc_lane;
    logic [cip_pkg::CIP_DAXI_RUSER_PE_IN_CC_WIDTH-1:0] 		d_noc_out_rpe_in_cc;
    logic [cip_pkg::CIP_DAXI_RUSER_CC_DIR_WIDTH-1:0]   		d_noc_out_rcc_dir; 

    logic [cip_pkg::CIP_DAXI_AWUSER_NOC_ID_WIDTH-1:0]     d_noc_out_awnoc_id;
    logic [cip_pkg::CIP_DAXI_AWUSER_NOC_ID_WIDTH-1:0]     d_noc_in_awnoc_id;

    logic [cip_pkg::CIP_DAXI_RUSER_NOC_ID_WIDTH-1:0]      d_noc_out_rnoc_id;
    logic [cip_pkg::CIP_DAXI_RUSER_NOC_ID_WIDTH-1:0]      d_noc_in_rnoc_id;

    logic [23:0]                                          disabled_pe;

    // logic                                                 left_pe_disabled;
    // // logic                                                 left_is_me;

    // logic                                                 right_pe_disabled;
    logic                                                 right_is_me;

    logic                                                 left_row_shift_south;
    logic                                                 right_row_shift_south;

    logic                                                 left_row_shift_south_for_south;
    logic                                                 right_row_shift_south_for_south;

    logic                                                 right_pe_disabled_in_row_minus_1;
    logic                                                 left_pe_disabled_in_row_minus_1;

    logic [XCOORD_WIDTH-1:0]                              dnoc_in_tgtid_xcoord;
    logic [YCOORD_WIDTH-1:0]                              dnoc_in_tgtid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                              dnoc_in_tgtid_zcoord;
    logic [ZCOORD_WIDTH-1:0]                              dnoc_in_tgtid_cip_id;

    logic [XCOORD_WIDTH-1:0]                              dnoc_in_srcid_xcoord;
    logic [YCOORD_WIDTH-1:0]                              dnoc_in_srcid_ycoord;
    logic [ZCOORD_WIDTH-1:0]                              dnoc_in_srcid_zcoord;
    logic [ZCOORD_WIDTH-1:0]                              dnoc_in_srcid_cip_id;

    assign d_noc_in_vc                                    = d_noc_in.payload.daxi_combo_aw_w.aw.user.vc;
    assign d_noc_out_vc                                   = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    
    assign dnoc_in_is_AW_W_channel                        = d_noc_in.channel == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign dnoc_in_is_R_channel                           = d_noc_in.channel == cip_pkg::NOC_CHANNEL_E_READ ;

    assign dnoc_out_is_AW_channel                         = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign dnoc_out_is_R_channel                          = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_READ ;

    assign d_noc_in_iid                                   = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.id.iid :
                                                            dnoc_in_is_R_channel    ? d_noc_in.payload.daxi_r.id.iid  : 
                                                            '0;

    assign d_noc_out_iid                                  = dnoc_in_is_AW_W_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.id.iid :
                                                            dnoc_in_is_R_channel    ? d_noc_out.payload.daxi_r.id.iid  : 
                                                            '0;

    assign d_noc_in_awlen                                 = d_noc_in.payload.daxi_combo_aw_w.aw.id.len;
    assign d_noc_in_wlast                                 = d_noc_in.payload.daxi_combo_aw_w.w.last;
    assign d_noc_in_awnoc_id                              = d_noc_in.payload.daxi_combo_aw_w.aw.user.noc_id;

    assign d_noc_in_rlast                                 = d_noc_in.payload.daxi_r.last;
    assign d_noc_in_rlen                                  = d_noc_in.payload.daxi_r.id.len;
    assign d_noc_in_rcc_dir                               = d_noc_in.payload.daxi_r.user.cc_dir;
    assign d_noc_in_rcc_opcode                            = d_noc_in.payload.daxi_r.user.cc_opcode;
    assign d_noc_in_rcc_lane                              = d_noc_in.payload.daxi_r.user.cc_lane;
    assign d_noc_in_rpe_in_cc                             = d_noc_in.payload.daxi_r.user.pe_in_cc;
    assign d_noc_in_rnoc_id                               = d_noc_in.payload.daxi_r.user.noc_id;

    assign d_noc_out_rlast                                = d_noc_out.payload.daxi_r.last;
    assign d_noc_out_rlen                                 = d_noc_out.payload.daxi_r.id.len;
    assign d_noc_out_rcc_dir                              = d_noc_out.payload.daxi_r.user.cc_dir;
    assign d_noc_out_rcc_opcode                           = d_noc_out.payload.daxi_r.user.cc_opcode;
    assign d_noc_out_rcc_lane                             = d_noc_out.payload.daxi_r.user.cc_lane;
    assign d_noc_out_rpe_in_cc                            = d_noc_out.payload.daxi_r.user.pe_in_cc;
    assign d_noc_out_rnoc_id                              = d_noc_out.payload.daxi_r.user.noc_id;

    assign d_noc_out_awlen                                = d_noc_out.payload.daxi_combo_aw_w.aw.id.len;
    assign d_noc_out_wlast                                = d_noc_out.payload.daxi_combo_aw_w.w.last;
    assign d_noc_out_awnoc_id                             = d_noc_out.payload.daxi_combo_aw_w.aw.user.noc_id;

    assign dnoc_in_tgtid_xcoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id.xcoord     :
                                                            dnoc_in_is_R_channel    ? d_noc_in.payload.daxi_r.user.tgt_id.xcoord                 : 
                                                            '0;
   
    assign dnoc_in_tgtid_ycoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id.ycoord     :
                                                            dnoc_in_is_R_channel    ? d_noc_in.payload.daxi_r.user.tgt_id.ycoord                 : 
                                                            '0;
   
    assign dnoc_in_tgtid_zcoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id.zcoord     :
                                                            dnoc_in_is_R_channel    ? d_noc_in.payload.daxi_r.user.tgt_id.zcoord                 : 
                                                            '0;

    assign dnoc_in_tgtid_cip_id                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.tgt_id.cip_id     :
                                                            dnoc_in_is_R_channel    ? d_noc_in.payload.daxi_r.user.tgt_id.cip_id                 : 
                                                            '0;


    assign dnoc_in_srcid_xcoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.src_id.xcoord     :
                                                            dnoc_in_is_R_channel ? d_noc_in.payload.daxi_r.user.src_id.xcoord                 : 
                                                            '0;
   
    assign dnoc_in_srcid_ycoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.src_id.ycoord     :
                                                            dnoc_in_is_R_channel ? d_noc_in.payload.daxi_r.user.src_id.ycoord                 : 
                                                            '0;
   
    assign dnoc_in_srcid_zcoord                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.src_id.zcoord     :
                                                            dnoc_in_is_R_channel ? d_noc_in.payload.daxi_r.user.src_id.zcoord                 : 
                                                            '0;

    assign dnoc_in_srcid_cip_id                           = dnoc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.user.src_id.cip_id     :
                                                            dnoc_in_is_R_channel ? d_noc_in.payload.daxi_r.user.src_id.cip_id                 : 
                                                            '0;



