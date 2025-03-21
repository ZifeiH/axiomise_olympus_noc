
    logic [cip_pkg::CIP_DAXI_AWUSER_VC_WIDTH-1:0]         d_noc_out_vc;

    logic [cip_pkg::CIP_DATA_NOC_CHANNEL_WIDTH-1:0]       d_noc_out_channel;

    logic                                                 d_noc_out_is_AW_W_channel, d_noc_out_is_R_channel;
    
		logic                                                 d_noc_out_awvalid;
		logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]            d_noc_out_awlen;
		logic                                                 d_noc_out_wlast;

    logic [cip_pkg::CIP_DAXI_ID_LEN_WIDTH-1:0]         		d_noc_out_rlen;
    logic                                              		d_noc_out_rlast;


    assign d_noc_out_vc                                    = d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;
    
    assign d_noc_out_is_aww_channel                        = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_WRITE;
    assign d_noc_out_is_r_channel                           = d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_READ ;

    assign d_noc_out_iid                                   = d_noc_out_is_AW_W_channel ? d_noc_out.payload.daxi_combo_aw_w.aw.id.iid :
                                                            d_noc_out_is_R_channel    ? d_noc_out.payload.daxi_r.id.iid  : 
                                                            '0;

    assign d_noc_out_awlen                                 = d_noc_out.payload.daxi_combo_aw_w.aw.id.len;
    assign d_noc_out_wlast                                 = d_noc_out.payload.daxi_combo_aw_w.w.last;

    assign d_noc_out_rlast                                 = d_noc_out.payload.daxi_r.last;
    assign d_noc_out_rlen                                  = d_noc_out.payload.daxi_r.id.len;

