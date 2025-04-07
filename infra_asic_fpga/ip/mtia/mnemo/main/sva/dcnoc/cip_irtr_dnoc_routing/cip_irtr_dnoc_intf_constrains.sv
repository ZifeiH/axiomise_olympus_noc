/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_intf_constrains.sv
//  This file contains irtr dnoc interface constrains
/////////////////////////////////////////////////////////////////////////////////////////
module cip_rtr_dnoc_intf_constrains # (

            parameter   SIDE                               = 0,
            parameter   num_of_nocs                        = 0,
            parameter   RTR_LOCATION_X_COORD               = 3,
            parameter   RTR_LOCATION_Y_COORD               = 4,
            parameter   RTR_LOCATION_CIP_ID                = 0
) (
            
  input     cip_pkg::data_noc_t                            d_noc_in,
  input     logic   [CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]       d_noc_in_credit_release,
  input     logic                                          d_noc_in_valid,

  input     cip_pkg::data_noc_t                            d_noc_out,
  input     logic   [CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]       d_noc_out_credit_release,
  input     logic                                          d_noc_out_valid,

  input     logic                                          clk,
  input     logic                                          reset_n

);  


//------------------------------------------------------------------------------
//-- Parameters
//------------------------------------------------------------------------------

    parameter is_north_edge_RTR                            = (RTR_LOCATION_Y_COORD == cip_pkg::CIP_RTR_GRID_COORD_Y_START);
    parameter is_south_edge_RTR                            = (RTR_LOCATION_Y_COORD == cip_pkg::CIP_RTR_GRID_COORD_Y_END-1)   ;
    parameter is_west_edge_RTR                             = (RTR_LOCATION_X_COORD == cip_pkg::CIP_RTR_GRID_COORD_X_START) ;
    parameter is_east_edge_RTR                             = (RTR_LOCATION_X_COORD == (cip_pkg::CIP_RTR_GRID_COORD_X_END-1)) ;
    parameter is_ne_corner_RTR                             = ((is_north_edge_RTR) && (is_east_edge_RTR));
    parameter is_nw_corner_RTR                             = ((is_north_edge_RTR) && (is_west_edge_RTR));
    parameter is_se_corner_RTR                             = ((is_south_edge_RTR) && (is_east_edge_RTR));
    parameter is_sw_corner_RTR                             = ((is_south_edge_RTR) && (is_west_edge_RTR));
    parameter is_cntr_RTR                                  =!((is_north_edge_RTR) || (is_south_edge_RTR) || (is_west_edge_RTR) || (is_east_edge_RTR));

    `include "../cip_rtr_lib/cip_rtr_dnoc_signal_defines.sv"
    `include "cip_irtr_dnoc_signal_defines.sv"
    `include "cip_irtr_dnoc_intf_constrains_defines.sv"


    localparam OUTSIDE_LLC         =  is_nw_corner_RTR  ? SIDE inside {WEST} :
                                      is_ne_corner_RTR  ? SIDE inside {EAST} : 0;

    localparam OUTSIDE_PE          =  is_nw_corner_RTR  ? SIDE inside {NORTH,WEST}:
                                      is_ne_corner_RTR  ? SIDE inside {NORTH,EAST}:
                                      is_sw_corner_RTR  ? SIDE inside {SOUTH,WEST}:
                                      is_se_corner_RTR  ? SIDE inside {SOUTH,EAST}:
                                      is_north_edge_RTR ? SIDE inside {NORTH}:
                                      is_south_edge_RTR ? SIDE inside {SOUTH}: 
                                      is_west_edge_RTR  ? SIDE inside {WEST} : 
                                      is_east_edge_RTR  ? SIDE inside {EAST} : 
                                      0;

    localparam NO_TRAFFIC_PORTS    =  is_nw_corner_RTR ? SIDE inside {WEST}  :
                                      is_ne_corner_RTR ? SIDE inside {EAST}  : 0;

    localparam EW_EDGE_LLC_TRAFFIC =  0; // llc -> soc request, soc -> llc resp

 generate 
    if (NO_TRAFFIC_PORTS) begin: traffic_not_allowed

           `SV_ASSERT (FVPH_RTR_FV_am_no_in_valid, !d_noc_in_valid);
           `SV_ASSERT (FVPH_RTR_FV_as_no_out_valid, !d_noc_out_valid);

    end else begin: traffic_allowed

//---------------------------------------- Credit release constrains -----------------------------------------------------

        cip_rtr_dnoc_credit_release_sva #(

            .SIDE                           (SIDE)

        ) cip_rtr_dnoc_credit_release_checker_sva (
            .d_noc_in                       (d_noc_in),
            .d_noc_in_credit_release        (d_noc_in_credit_release),
            .d_noc_in_valid                 (d_noc_in_valid),

            .d_noc_out                      (d_noc_out),
            .d_noc_out_credit_release       (d_noc_out_credit_release),
            .d_noc_out_valid                (d_noc_out_valid),

            .clk                            (clk),
            .reset_n                        (reset_n)
        );

//---------------------------------------- FBAXI constrains ------------------------------------------------------

        cip_rtr_dnoc_FBAXI_constraints # (

            .GEN_AW_W_ASM   (!EW_EDGE_LLC_TRAFFIC)

        ) dnoc_FBAXI_constraints 
        (
            .dnoc_bundle                    (d_noc_in),
            .dnoc_valid                     (d_noc_in_valid),

            .clk                            (clk),
            .reset_n                        (reset_n)  
        );

//---------------------------------------- General constrains -----------------------------------------------------

        `SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_cip_id               , dnoc_in_tgtid_cip_id    inside {0,1});
        `SV_ASSERT (FVPH_RTR_FV_am_valid_src_cip_id               , dnoc_in_srcid_cip_id    inside {0,1});
                 
        `SV_ASSERT (FVPH_RTR_FV_am_flow_control                   , !d_noc_in_valid);

        `SV_ASSERT (FVPH_RTR_FV_am_ar_vc_within_valid_range       , dnoc_in_is_AW_W_channel   |->    d_noc_in_vc < REQ_TOTAL_NUM_VC );
        `SV_ASSERT (FVPH_RTR_FV_am_b_vc_within_valid_range        , dnoc_in_is_R_channel      |->    d_noc_in_vc < RESP_TOTAL_NUM_VC );
             
        `SV_ASSERT (FVPH_RTR_FV_am_ttl_input_greater_than_1       , d_noc_in.ttl > 'd1         );
        `SV_ASSERT (FVPH_RTR_FV_am_ttl_input_less_than_25         , d_noc_in.ttl < 'd25        );

//---------------------------------------- Others specification constrains -----------------------------------------------------

        `SV_ASSERT (FVPH_RTR_FV_am_tgt_not_to_void                , d_noc_in_valid |-> !void_tgt_coords);
        
        `SV_ASSERT (FVPH_RTR_FV_am_src_not_from_void              , d_noc_in_valid |-> !void_src_coords);
        
        `SV_ASSERT (FVPH_RTR_FV_am_tgt_within_grid                , d_noc_in_valid |-> dnoc_in_tgtid_xcoord >= (CIP_RTR_GRID_COORD_X_START-1) && dnoc_in_tgtid_xcoord <= (CIP_RTR_GRID_COORD_X_END+1) &&
                                                                                       dnoc_in_tgtid_ycoord >= (CIP_RTR_GRID_COORD_Y_START-1) && dnoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END+1) );

        `SV_ASSERT (FVPH_RTR_FV_am_src_within_grid                , d_noc_in_valid |-> dnoc_in_srcid_xcoord >= (CIP_RTR_GRID_COORD_X_START-1) && dnoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END+1) &&
                                                                                       dnoc_in_srcid_ycoord >= (CIP_RTR_GRID_COORD_Y_START-1) && dnoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END+1) );         

        `SV_ASSERT (FVPH_RTR_FV_am_r_no_rdm                       , dnoc_in_is_R_channel      |->    d_noc_in_rcc_opcode != cip_pkg::CC_OPCODE_E_RDM );

        
        if (!OUTSIDE_PE) begin
        
            `SV_ASSERT (FVPH_RTR_FV_am_no_resp_from_pe_to_LLC        , d_noc_in_valid && dnoc_in_is_R_channel  && dnoc_in_src_is_PE  |-> !dnoc_in_tgt_to_LLC);
    
        end
    
        if (!OUTSIDE_LLC) begin
    
            `SV_ASSERT (FVPH_RTR_FV_am_no_traffic_from_LLC_to_LLC    , d_noc_in_valid  |-> !(dnoc_in_src_from_LLC && dnoc_in_tgt_to_LLC));
        
        end

        if (RTR_LOCATION_CIP_ID==1) begin
        
            `SV_ASSERT (FVPH_RTR_FV_am_tgt_not_to_maxb            , d_noc_in_valid && dnoc_in_tgt_within_cip  |-> dnoc_in_tgtid_ycoord != 0);
        
        end

      if (SIDE == NORTH) begin: d_noc_north_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_NORTH0 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_set , d_noc_in_valid |-> d_noc_north_in_tgt_set );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_north_in_src_set );

          `SV_COVER (FVPH_RTR_FV_co_aw_can_tgt_to_OWL_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord > CIP_RTR_GRID_COORD_Y_END    && dnoc_in_tgtid_cip_id ==1 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);
          `SV_COVER (FVPH_RTR_FV_co_r_can_tgt_to_OWL             , d_noc_in_valid  && dnoc_in_is_R_channel    ##0  dnoc_in_tgtid_ycoord > CIP_RTR_GRID_COORD_Y_END    && dnoc_in_tgtid_cip_id ==1 );

          if (RTR_LOCATION_CIP_ID==1) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 0);

      end
      else if (SIDE == SOUTH) begin: d_noc_south_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_SOUTH0 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_set , d_noc_in_valid |-> d_noc_south_in_tgt_set );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_south_in_src_set );

          `SV_COVER (FVPH_RTR_FV_co_aw_can_tgt_to_SOC_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord < CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id ==0 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);

          if (RTR_LOCATION_CIP_ID==0) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 1);

      end
      else if (SIDE == EAST) begin: d_noc_east_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_EAST0 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_set , d_noc_in_valid |-> d_noc_east_in_tgt_set );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_east_in_src_set );

          `SV_COVER (FVPH_RTR_FV_co_aw_can_tgt_to_SOC_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord < CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id ==0 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);

          if (RTR_LOCATION_CIP_ID==1) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 0);
          if (RTR_LOCATION_CIP_ID==0) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 1);
          
      end
      else if (SIDE == WEST) begin: d_noc_west_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_WEST0 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_set , d_noc_in_valid |-> d_noc_west_in_tgt_set );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_west_in_src_set );

          `SV_COVER  (FVPH_RTR_FV_co_aw_can_tgt_to_SOC_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord < CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id ==0 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);

          if (RTR_LOCATION_CIP_ID==1) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 0);
          if (RTR_LOCATION_CIP_ID==0) `SV_COVER(FVPH_RTR_FV_co_c2c_traffic , dnoc_in_srcid_cip_id == 1);

      end
      else if (SIDE == LEAF0) begin: d_noc_leaf0_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_LEAF0 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_leaf0_in_src_set );

          `SV_COVER (FVPH_RTR_FV_co_aw_can_tgt_to_SOC_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord < CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id ==0 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);

      end
      else if (SIDE == LEAF1) begin: d_noc_leaf1_in

          `SV_ASSERT (FVPH_RTR_FV_am_noc_ids       , d_noc_in_iid    == num_of_nocs + cip_rtr_pkg::IRTR_NOC_LEAF1 );
          `SV_ASSERT (FVPH_RTR_FV_am_valid_src_set , d_noc_in_valid |-> d_noc_leaf1_in_src_set );

          `SV_COVER (FVPH_RTR_FV_co_aw_can_tgt_to_SOC_and_turn   , d_noc_in_valid  && dnoc_in_is_AW_W_channel ##0  dnoc_in_tgtid_ycoord < CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id ==0 && dnoc_in_tgtid_xcoord != RTR_LOCATION_X_COORD);

      end 
    end

    endgenerate
 
   
endmodule