///////////////////////////////////////////////////
/// File: cip_rtr_unoc_FBAXI_constraints.sv
/// This file contains the constrains for unoc FBAXI
///////////////////////////////////////////////////

module cip_rtr_unoc_fbaxi_constraints # (
  parameter RTR_GRID_COORD_Y_START  = cip_pkg::CIP_RTR_GRID_COORD_Y_START,
  parameter RTR_GRID_COORD_Y_END    = cip_pkg::CIP_RTR_GRID_COORD_Y_END,
  parameter RTR_GRID_COORD_X_START  = cip_pkg::CIP_RTR_GRID_COORD_X_START,
  parameter RTR_GRID_COORD_X_END    = cip_pkg::CIP_RTR_GRID_COORD_X_END,
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

  `include "cip_rtr_unoc_FBAXI_signal_defines.sv"
  `include "cip_rtr_unoc_FBAXI_constraints_defines.sv"

  // ------------------------------------------------------------------
  logic all_valid_tgt_zcoord_vals;
  logic tgt_ycoord_above_north; 
  logic tgt_ycoord_below_south;

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
                                                                      (unoc_in_tgtid_ycoord == rtr_location.ycoord)    &&
                                                                      (unicast2rtr || req_any_unicast2max)) || 
                                                                       scw2rtr)    

                                                                 |-> unoc_in_awlen == 3'h0);

  /*@ASM Legal ar len towards cfg @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_unoc_in_rlen_towards_cfg      ,    unoc_in_arvalid && ((unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                                     (unoc_in_tgtid_ycoord == rtr_location.ycoord)                      &&
                                                                     (unicast2rtr || req_any_unicast2max))
                                                                             
                                                                 |-> unoc_in_arlen == 3'h0);

  /*@ASM Only single beat illegal tgt id towards cfg @*/
  `SV_ASSERT (FVPH_RTR_FV_am_only_single_beat_illegal_tgt_id_towards_cfg      ,    u_noc_in_valid && (unoc_in_tgtid_xcoord == (rtr_location.xcoord + 1)) &&
                                                                                   (unoc_in_tgtid_ycoord == rtr_location.ycoord) && 
                                                                                   (unicast2rtr || req_any_unicast2max)
                                                                     |->           (unoc_in_awlen == 3'b0) && (unoc_in_arlen == 3'b0) &&
                                                                                   (unoc_in_rlen == 3'b0) && (unoc_in_blen == 3'b0));

  assign tgt_ycoord_above_north    = unoc_in_tgtid.ycoord < RTR_GRID_COORD_Y_START;
  assign tgt_ycoord_below_south    = unoc_in_tgtid.ycoord > RTR_GRID_COORD_Y_END;

  assign all_valid_tgt_zcoord_vals                    =  (tgt_ycoord_above_north || tgt_ycoord_below_south)?
                                                            all_req_types || req_any_unicast2max :
                                                            all_req_types;

  `SV_ASSERT (FVPH_RTR_FV_am_all_valid_tgt_zcoord_val , (unoc_in_awvalid || unoc_in_arvalid) |-> all_valid_tgt_zcoord_vals );

  /*@ASM Legal zcoord values of tgtid for aw @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord    ,    unoc_in_awvalid |-> all_req_types || req_any_unicast2max); 

  /*@ASM Legal zcoord values of tgtid for ar @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_ar_tgtid_zcoord    ,    unoc_in_arvalid |-> non_scw || req_any_unicast2max); 

  /*@ASM Legal zcoord values of orgid for r and b @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_b_r_orgid_zcoord    ,    unoc_in_rvalid || unoc_in_bvalid |-> non_scw); 

  /*@ASM Legal zcoord values of orgid for ar and aw @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_ar_aw_orgid_zcoord    ,    unoc_in_arvalid || unoc_in_awvalid |-> non_scw_resp); 

  /*@ASM Legal zcoord values of srcid for r @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_r_srcid_zcoord    ,    unoc_in_rvalid |-> non_scw_resp || resp_any_unicast2max); 

  if((SIDE != NORTH) && (SIDE != LEAF0) && (SIDE != LEAF1)) begin
    /*@ASM Legal zcoord values of srcid for b from south, west and east @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord    ,    unoc_in_bvalid |-> all_resp_types || resp_any_unicast2max); 
  end
  else if(SIDE == NORTH) begin
    /*@ASM Legal zcoord values of srcid for b from north @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord    ,    unoc_in_bvalid |-> non_scw_resp || resp_any_unicast2max);
  end

  /*@ASM Legal cip_id values in tgt_id and org_id for req and resp respectively @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_cip_id_values_for_tgt_id    ,    u_noc_in_valid |-> unoc_in_tgtid_cip_id inside {0, 1}); 

  /*@ASM Legal cip_id values in org_id and src_id for req and resp respectively @*/
  `SV_ASSERT (FVPH_RTR_FV_am_legal_cip_id_values_for_src_id    ,    u_noc_in_valid |-> unoc_in_srcid_cip_id inside {0, 1}); 

  if((SIDE == SOUTH) || (SIDE == LEAF0) || (SIDE == LEAF1)) begin
      /*@ASM To not allow SCW reqs from south, leaf0 and leaf1 @*/
      `SV_ASSERT (FVPH_RTR_FV_am_legal_aw_tgtid_zcoord_from_south_lf0_lf1      ,    unoc_in_awvalid |-> non_scw || req_any_unicast2max);  

      if(SIDE != SOUTH) begin
        /*@ASM Legal zcoord values of srcid for b from leafs @*/
        `SV_ASSERT (FVPH_RTR_FV_am_legal_b_srcid_zcoord_from_leafs    ,    unoc_in_bvalid |-> scw_pe_resp || unicast_pe_resp); 
      end
  end

  /*@ASM Rresp transactions are not allowed towards RTR @*/
  `SV_ASSERT (FVPH_RTR_FV_am_no_rresp_towards_rtr   ,    u_noc_in_valid && (unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                         (unoc_in_tgtid_ycoord == rtr_location.ycoord) && unicast2rtr
                                                         |-> !unoc_in_is_R_channel); 
  
  /*@ASM Wresp transactions are not allowed towards RTR @*/
  `SV_ASSERT (FVPH_RTR_FV_am_no_wresp_towards_rtr  ,    u_noc_in_valid && (unoc_in_tgtid_xcoord == rtr_location.xcoord) &&
                                                         (unoc_in_tgtid_ycoord == rtr_location.ycoord) && unicast2rtr
                                                         |-> !unoc_in_is_B_channel); 

  if(SIDE != NORTH) begin
    /*@ASM Legal cipid in orgid for SCW resp  @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_cipid_in_orgid_for_scw_rsp  ,    unoc_in_bvalid && unoc_in_srcid_zcoord[3]? !unoc_in_tgtid_cip_id : 1);
  end

  if(SIDE != SOUTH && SIDE != NORTH) begin
    /*@ASM Legal cipid in srcid for SCW resp  @*/
    `SV_ASSERT (FVPH_RTR_FV_am_legal_cipid_in_srcid_for_scw_rsp  ,    unoc_in_bvalid && unoc_in_srcid_zcoord[3]
                                                                      |-> unoc_in_srcid_cip_id == rtr_location.cip_id);
  end

  /*@ASM Tagging traffic to identify at outputs @*/
  `SV_ASSERT (FVPH_RTR_FV_am_noc_id                  , unoc_in_is_AW_W_channel? unoc_in_awiid   == SIDE :
                                                       unoc_in_is_AR_channel  ? unoc_in_ariid   == SIDE :
                                                       unoc_in_is_R_channel   ? unoc_in_riid    == SIDE :
                                                       unoc_in_is_B_channel   ? unoc_in_biid    == SIDE :
                                                       0);

  if(SIDE == NORTH) begin : u_noc_north_in

      /*@ASM Legal tgt_id from north according to UNOC Routing Guidelines Section (Page-58)@*/
      `SV_ASSERT (FVPH_RTR_FV_am_north_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_north_in_tgtid_set);
      /*@ASM Legal src_id from north according to UNOC Routing Guidelines Section (Page-58)@*/
      `SV_ASSERT (FVPH_RTR_FV_am_north_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_north_in_srcid_set && scw_org_set_n);

  end
  else if(SIDE == SOUTH) begin : u_noc_south_in

      /*@ASM Legal tgt_id from south according to UNOC Routing Guidelines Section (Page-58) @*/
      `SV_ASSERT (FVPH_RTR_FV_am_south_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_south_in_tgtid_set);
      /*@ASM Legal src_id from south according to UNOC Routing Guidelines Section (Page-58) @*/
      `SV_ASSERT (FVPH_RTR_FV_am_south_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_south_in_srcid_set);

  end
  else if(SIDE == EAST) begin : u_noc_east_in

      /*@ASM Legal tgt_id from east according to UNOC Routing Guidelines Section (Page-58) @*/
      `SV_ASSERT (FVPH_RTR_FV_am_east_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_east_in_tgtid_set);
      /*@ASM Legal src_id from east according to UNOC Routing Guidelines Section (Page-58) @*/
      `SV_ASSERT (FVPH_RTR_FV_am_east_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_east_in_srcid_set && scw_org_set_e);

    end
    else if(SIDE == WEST) begin : u_noc_west_in

        /*@ASM Legal tgt_id from west according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_west_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_west_in_tgtid_set);
        /*@ASM Legal src_id from west according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_west_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_west_in_srcid_set && scw_org_set_w);

    end
    else if(SIDE == LEAF0) begin : u_noc_leaf0_in

        /*@ASM Legal tgt_id from leaf0 according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf0_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_leaf0_in_tgtid_set);
        /*@ASM Legal src_id from leaf0 according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf0_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_leaf0_in_srcid_set);
  
    end
    else if(SIDE == LEAF1) begin : u_noc_leaf1_in

        /*@ASM Legal tgt_id from leaf1 according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf1_legal_tgtid_set     ,    u_noc_in_valid |-> u_noc_leaf1_in_tgtid_set);
        /*@ASM Legal src_id from leaf1 according to UNOC Routing Guidelines Section (Page-58) @*/
        `SV_ASSERT (FVPH_RTR_FV_am_leaf1_legal_srcid_set     ,    u_noc_in_valid |-> u_noc_leaf1_in_srcid_set);
        
    end

endmodule