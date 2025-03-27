/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_d_noc_signal_defines.sv
// This file contains cip router signals
/////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- Signal defines for cip_rtr_unoc_checker_sva.sv --
//------------------------------------------------------------------------------

    logic [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_in_vc;
    logic [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_out_vc;

    logic [cip_pkg::CIP_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_in_channel;
    logic [cip_pkg::CIP_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_out_channel;

    logic                                                 d_noc_in_is_AW_W_channel, d_noc_in_is_R_channel;
    logic                                                 d_noc_out_is_AW_channel, d_noc_out_is_R_channel;
    
    logic [cip_pkg::CIP_DAXI_ID_IID_WIDTH-1:0]            d_noc_in_iid;

		logic                                                d_noc_in_awvalid;
		logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]           d_noc_in_awlen;
		logic                                                d_noc_in_wlast;

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

    assign d_noc_in_vc                                    = d_noc_in.payload.daxi_combo_aw_w.aw.user.vc;
    assign d_noc_out_vc                                   = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    
    assign d_noc_in_is_AW_W_channel                        = d_noc_in.channel == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign d_noc_in_is_R_channel                           = d_noc_in.channel == cip_pkg::NOC_CHANNEL_E_READ ;

    assign d_noc_out_is_AW_channel                         = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign d_noc_out_is_R_channel                          = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_READ ;

    assign d_noc_in_iid                                   = d_noc_in_is_AW_W_channel ? d_noc_in.payload.daxi_combo_aw_w.aw.id.iid :
                                                            d_noc_in_is_R_channel    ? d_noc_in.payload.daxi_r.id.iid  : 
                                                            '0;

    assign d_noc_out_iid                                  = d_noc_in_is_AW_W_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.id.iid :
                                                            d_noc_in_is_R_channel    ? d_noc_out.payload.daxi_r.id.iid  : 
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

