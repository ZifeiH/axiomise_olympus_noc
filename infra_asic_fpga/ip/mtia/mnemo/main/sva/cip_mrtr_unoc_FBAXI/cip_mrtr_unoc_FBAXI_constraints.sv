///////////////////////////////////////////////////
/// File: cip_mrtr_unoc_FBAXI_constraints.sv
/// This file contains the assumptions for FBAXI
///////////////////////////////////////////////////

module cip_mrtr_unoc_fbaxi_constraints # (
  parameter RTR_LOCATION_X_COORD    = 3,
  parameter RTR_LOCATION_Y_COORD    = 4,
  parameter RTR_LOCATION_CIP_ID     = 0,
  parameter SIDE                    = 0

) (

	input logic																						clk,
	input	logic																						reset_n,

  input	cip_pkg::utility_noc_t                         	u_noc_in,
  input	logic                                          	u_noc_in_valid,

  input	cip_pkg::utility_noc_t                         	u_noc_out,
  input	logic                                          	u_noc_out_valid,

  input	cip_pkg::cip_grid_location_t										rtr_location
);

  `define read_req    cip_pkg::UNOC_CHANNEL_E_READ_REQ;
  `define write_req   cip_pkg::UNOC_CHANNEL_E_WRITE_REQ;
  `define write_resp  cip_pkg::UNOC_CHANNEL_E_WRITE_RESP;
  `define read_resp   cip_pkg::UNOC_CHANNEL_E_READ_RESP;

  `include "cip_mrtr_unoc_FBAXI_signal_defines.sv"
  `include "cip_mrtr_unoc_FBAXI_constraints_defines.sv"

  generate 
    if((`is_sw_corner_RTR && SIDE == WEST) || (`is_se_corner_RTR && SIDE == EAST)) begin
      /*@ASM There should be no traffic from west and east at sw corner rtr and se corner rtr respectively @*/
      `SV_ASSERT(FVPH_RTR_FV_am_no_traffic_from_WE_at_sw_se,     !u_noc_in_valid);
    end
  endgenerate

  generate if(!((`is_sw_corner_RTR && SIDE == WEST) || ( `is_se_corner_RTR && SIDE == EAST))) begin

  /*@ASM Legal len values for aw @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_aw_burst_len       ,    unoc_in_awvalid |-> unoc_in_awlen <= 7);
  /*@ASM Legal len values for ar @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_ar_burst_len       ,    unoc_in_arvalid |-> unoc_in_arlen <= 7);
  /*@ASM Legal len values for r @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_r_burst_len        ,    unoc_in_rvalid  |-> unoc_in_rlen <= 7);
  /*@ASM Legal len values for b @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_b_burst_len        ,    unoc_in_bvalid  |-> unoc_in_blen <= 7);
  /*@ASM Legal size values for aw @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_aw_size_valid      ,    unoc_in_awvalid |-> (unoc_in_awsize == 2 || unoc_in_awsize == 3));
  /*@ASM Legal size values for ar @*/
  `SV_ASSERT (FVPH_RTR_FV_am_set_ar_size_valid      ,    unoc_in_arvalid |-> (unoc_in_arsize == 2 || unoc_in_arsize == 3));  

  /*@ASM Legal aw len towards cfg @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_unoc_in_awlen_towards_cfg      ,    unoc_in_awvalid && (((unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                                                            (unoc_in_tgtid_ycoord == rtr_location.ycoord) &&
                                                                                             unicast2mrtr)                                 || 
                                                                                             scw2rtr)    

                                                                   |-> unoc_in_awlen == 3'h0);

  /*@ASM Legal ar len towards cfg @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_unoc_in_rlen_towards_cfg      ,    unoc_in_arvalid && ((unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                                                          (unoc_in_tgtid_ycoord == rtr_location.ycoord) &&
                                                                                           unicast2mrtr)
                                                                             
                                                                  |-> unoc_in_arlen == 3'h0);

  /*@ASM Only single beat illegal tgt id towards cfg @*/
  `SV_ASSERT (FVPH_RTR_FV_am_only_single_beat_illegal_tgt_id_towards_cfg      ,    u_noc_in_valid && (unoc_in_tgtid_ycoord == rtr_location.ycoord) &&
                                                                                   ((unoc_in_tgtid_xcoord == (rtr_location.xcoord + 1)) && 
                                                                                     unicast2rtr                                          ||
                                                                                     unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_UNICAST_MAX2   ||
                                                                                    unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_UNICAST_MAX2_MB)
                                                                               |-> (unoc_in_awlen == 3'b0) && (unoc_in_arlen == 3'b0) &&
                                                                                   (unoc_in_rlen == 3'b0) && (unoc_in_blen == 3'b0));

  if(SIDE == NORTH) begin
    /*@ASM Legal zcoord values of aw tgtid for cip0 if I am at cip0 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord_for_cip0_at_cip0    ,    unoc_in_awvalid && cip0 && !unoc_in_tgtid_cip_id? non_scw : 1); 
    /*@ASM Legal zcoord values of aw tgtid for cip1 if I am at cip0 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord_for_cip1_at_cip0    ,    unoc_in_awvalid && cip0 && unoc_in_tgtid_cip_id? all_req_types : 1); 
    /*@ASM Legal zcoord values of aw tgtid if I am at cip1 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord_at_cip1             ,    unoc_in_awvalid && cip1? non_scw : 1);
  end
  else begin
    /*@ASM Legal zcoord values of aw tgtid @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord               ,    unoc_in_awvalid |-> non_scw);
  end

  /*@ASM Legal zcoord values of tgtid for ar @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_ar_tgtid_zcoord                       ,    unoc_in_arvalid |-> non_scw); 

  // /*@ASM Legal zcoord for req towards mrtr @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_zcoord_towards_mrtr                   ,    (unoc_in_awvalid || unoc_in_arvalid)          && 
                                                                              (unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                                              (unoc_in_tgtid_ycoord == rtr_location.ycoord) 
                                                                              |-> !(unicast2crtr                                          || 
                                                                                    unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_UNICAST_MAX2    ||
                                                                                    unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_UNICAST_MAX2_MB
                                                                                    )); 

  /*@ASM Legal zcoord values of orgid for r and b @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_b_r_orgid_zcoord    ,    unoc_in_rvalid || unoc_in_bvalid |-> non_scw); 

  /*@ASM Legal zcoord values of orgid for ar and aw @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_ar_aw_orgid_zcoord    ,    unoc_in_arvalid || unoc_in_awvalid |-> non_scw_resp); 

  /*@ASM Legal zcoord values of srcid for r @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_r_srcid_zcoord    ,    unoc_in_rvalid |-> non_scw_resp); 

  if(SIDE == SOUTH) begin
    /*@ASM Legal zcoord values of b srcid for cip0 if I am at cip0 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord_for_cip0_at_cip0    ,    unoc_in_bvalid && cip0 && !unoc_in_srcid_cip_id? non_scw_resp : 1); 
    /*@ASM Legal zcoord values of b srcid for cip1 if I am at cip0 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord_for_cip1_at_cip0    ,    unoc_in_bvalid && cip0 && unoc_in_srcid_cip_id?
                                                                             non_scw_resp || scw_resp_cip1 : 1); 
    /*@ASM Legal zcoord values of b srcid if I am at cip1 @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord_at_cip1             ,    unoc_in_bvalid && cip1? non_scw_resp : 1);
  end
  else begin
    /*@ASM Legal zcoord values of b srcid @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord               ,    unoc_in_bvalid |-> non_scw_resp);
  end

  /*@ASM Legal cip_id values in tgt_id and org_id for req and resp respectively @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_cip_id_values_for_tgt_id    ,    u_noc_in_valid |-> unoc_in_tgtid_cip_id inside {0, 1}); 

  /*@ASM Legal cip_id values in org_id and src_id for req and resp respectively @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_cip_id_values_for_src_id    ,    u_noc_in_valid |-> unoc_in_srcid_cip_id inside {0, 1});

  /*@ASM Rresp transactions are not allowed towards RTR @*/
  `SV_ASSERT (FVPH_RTR_FV_am_no_rresp_towards_rtr   ,    u_noc_in_valid && (unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                         (unoc_in_tgtid_ycoord == rtr_location.ycoord) && unicast2rtr
                                                         |-> !unoc_in_is_R_channel); 
  
  /*@ASM Wresp transactions are not allowed towards RTR @*/
  `SV_ASSERT (FVPH_RTR_FV_am_no_wresp_towards_rtr  ,    u_noc_in_valid && (unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                         (unoc_in_tgtid_ycoord == rtr_location.ycoord) && unicast2rtr
                                                         |-> !unoc_in_is_B_channel); 

  /*@ASM Tagging iid to identify traffic at output @*/
  `SV_ASSERT (FVPH_RTR_FV_am_tagging_iid           ,   unoc_in_is_AW_W_channel? unoc_in_awiid   == SIDE :
                                                       unoc_in_is_AR_channel  ? unoc_in_ariid   == SIDE :
                                                       unoc_in_is_R_channel   ? unoc_in_riid    == SIDE :
                                                       unoc_in_is_B_channel   ? unoc_in_biid    == SIDE :
                                                       0);

  if(SIDE == SOUTH) begin
    /*@ASM Legal cipid in orgid for SCW resp  @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_cipid_in_orgid_for_scw_rsp  ,    unoc_in_bvalid && unoc_in_srcid_zcoord[3]
                                                                      |-> !unoc_in_tgtid_cip_id);
  end

  if(SIDE == NORTH) begin : u_noc_north_in

      /*@ASM Legal tgt_id from north @*/
      `SV_ASSERT (FVPH_RTR_FV_am_north_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_north_in_tgtid_set);
      /*@ASM Legal src_id from north @*/
      `SV_ASSERT (FVPH_RTR_FV_am_north_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_north_in_srcid_set);

  end
  else if(SIDE == SOUTH) begin : u_noc_south_in

      /*@ASM Legal tgt_id from south @*/
      `SV_ASSERT (FVPH_RTR_FV_am_south_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_south_in_tgtid_set);
      /*@ASM Legal src_id from south @*/
      `SV_ASSERT (FVPH_RTR_FV_am_south_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_south_in_srcid_set);

  end
  else if(SIDE == EAST) begin : u_noc_east_in

      /*@ASM Legal tgt_id from east @*/
      `SV_ASSERT (FVPH_RTR_FV_am_east_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_east_in_tgtid_set);
      /*@ASM Legal src_id from east @*/
      `SV_ASSERT (FVPH_RTR_FV_am_east_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_east_in_srcid_set);

    end
    else if(SIDE == WEST) begin : u_noc_west_in

        /*@ASM Legal tgt_id from west @*/
        `SV_ASSERT (FVPH_RTR_FV_am_west_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_west_in_tgtid_set);
        /*@ASM Legal src_id from west @*/
        `SV_ASSERT (FVPH_RTR_FV_am_west_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_west_in_srcid_set);

    end
    else if(SIDE == LEAF0) begin : u_noc_leaf0_in
        /*@ASM Leaf0 cannot tgt itself @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf0_cannot_tgt_itself     ,    u_noc_in_valid |-> !((unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                                                      (unoc_in_tgtid_ycoord == rtr_location.ycoord) &&
                                                                                       unicast2me));

        /*@ASM Legal tgt_id from leaf0 @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf0_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_leaf0_in_tgtid_set);
        /*@ASM Legal src_id from leaf0 @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf0_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_leaf0_in_srcid_set);
  
    end
    else if(SIDE == LEAF1) begin : u_noc_leaf1_in
        /*@ASM Leaf1 cannot tgt itself @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf1_cannot_tgt_itself     ,    u_noc_in_valid |-> !((unoc_in_tgtid_xcoord == (rtr_location.xcoord + 1))  &&
                                                                                      (unoc_in_tgtid_ycoord == rtr_location.ycoord)        &&
                                                                                       unicast2me));

        /*@ASM Legal tgt_id from leaf1 @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf1_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_leaf1_in_tgtid_set);
        /*@ASM Legal src_id from leaf1 @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf1_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_leaf1_in_srcid_set);
        
    end
  end
  endgenerate

endmodule