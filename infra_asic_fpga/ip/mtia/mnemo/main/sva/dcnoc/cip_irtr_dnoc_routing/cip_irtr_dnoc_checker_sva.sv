/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_checker_sva.sv
//  This file contains irtr dnoc routing checks
/////////////////////////////////////////////////////////////////////////////////////////

module cip_rtr_dnoc_checker_sva # (

  parameter            DATA_WIDTH            = 1,
  parameter [5:0]      DIR_VALUE             = 0,
  parameter            IID                   = 0,
  parameter            DEST_NOC_ID           = 0,
  parameter            TGT_LANE              = 0,
  parameter            GEN_ADD_COVS          = 1,
  parameter            RTR_LOCATION_X_COORD  = 3,
  parameter            RTR_LOCATION_Y_COORD  = 4,
  parameter            RTR_LOCATION_CIP_ID   = 0,
  parameter            TYPE                  = "E2E"     
  
) (

  input   cip_pkg::data_noc_t           d_noc_in,
  input   logic                         d_noc_in_valid,
  
  input   cip_pkg::data_noc_t           d_noc_out,
  input   logic                         d_noc_out_valid,           

  input   logic                         clk,
  input   logic                         reset_n
    
);

    logic                               left_pe_disabled;
    logic                               right_pe_disabled;
    logic                               is_req, is_resp;

    assign left_pe_disabled                 = RTR_LOCATION_CIP_ID == 0  ?   `CIP_IRTR_CFG_DISABLED_PE0[((RTR_LOCATION_X_COORD-CIP_RTR_GRID_COORD_X_START)*4)+3:(RTR_LOCATION_X_COORD-1)*4] == RTR_LOCATION_Y_COORD-CIP_RTR_GRID_COORD_Y_START:
                                                                            `CIP_IRTR_CFG_DISABLED_PE1[((RTR_LOCATION_X_COORD-CIP_RTR_GRID_COORD_X_START)*4)+3:(RTR_LOCATION_X_COORD-1)*4] == RTR_LOCATION_Y_COORD-CIP_RTR_GRID_COORD_Y_START;

    assign right_pe_disabled                = RTR_LOCATION_CIP_ID == 0  ?   `CIP_IRTR_CFG_DISABLED_PE0[(RTR_LOCATION_X_COORD*4)+3:RTR_LOCATION_X_COORD*4] == RTR_LOCATION_Y_COORD-CIP_RTR_GRID_COORD_Y_START:
                                                                            `CIP_IRTR_CFG_DISABLED_PE1[(RTR_LOCATION_X_COORD*4)+3:RTR_LOCATION_X_COORD*4] == RTR_LOCATION_Y_COORD-CIP_RTR_GRID_COORD_Y_START;

    `include "../cip_rtr_lib/cip_rtr_dnoc_signal_defines.sv"
    `include "cip_irtr_dnoc_signal_defines.sv"
    `include "cip_irtr_dnoc_routing_equations.sv"

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

    localparam NO_RESP_TRAFFIC_PORTS  = is_nw_corner_RTR ? DIR_VALUE[5:3] inside {WEST} || DIR_VALUE[2:0] inside {WEST}:
                                        is_ne_corner_RTR ? DIR_VALUE[5:3] inside {EAST} || DIR_VALUE[2:0] inside {EAST}:
                                        0;

    localparam NO_REQ_TRAFFIC_PORTS  =  is_nw_corner_RTR ? DIR_VALUE[5:3] inside {WEST} || DIR_VALUE[2:0] inside {WEST}:
                                        is_ne_corner_RTR ? DIR_VALUE[5:3] inside {EAST} || DIR_VALUE[2:0] inside {EAST}:
                                        0;

    localparam IS_X2L_INV2       =  TYPE=="INV2"&&(DIR_VALUE[2:0]==LEAF0||DIR_VALUE[2:0]==LEAF1);

    localparam illegal_req_paths = 
        DIR_VALUE    == {EAST,SOUTH}  ||
        DIR_VALUE    == {WEST,SOUTH}  ||     
        DIR_VALUE    == {SOUTH,LEAF0} && TGT_LANE inside {0,2} ||
        DIR_VALUE    == {SOUTH,LEAF1} && TGT_LANE inside {0,2} ||
        DIR_VALUE    == {NORTH,LEAF0} && TGT_LANE inside {1,3} ||
        DIR_VALUE    == {NORTH,LEAF1} && TGT_LANE inside {1,3} ||
        DIR_VALUE    == {EAST,NORTH}  && is_north_edge_RTR && RTR_LOCATION_CIP_ID==1     || // any x-first is possible cip north cip0 only
        DIR_VALUE    == {WEST,NORTH}  && is_north_edge_RTR && RTR_LOCATION_CIP_ID==1     || // any x-first is possible cip north cip0 only
        NO_REQ_TRAFFIC_PORTS;
  
    localparam illegal_resp_paths =      
        (DIR_VALUE     == {LEAF0,NORTH} && TGT_LANE>=LANES_CAN_TURN)||
        (DIR_VALUE     == {LEAF0,SOUTH} && TGT_LANE>=LANES_CAN_TURN)||
        (DIR_VALUE     == {LEAF1,NORTH} && TGT_LANE>=LANES_CAN_TURN)||
        (DIR_VALUE     == {LEAF1,SOUTH} && TGT_LANE>=LANES_CAN_TURN)||
         DIR_VALUE     == {SOUTH,EAST}  ||
         DIR_VALUE     == {SOUTH,WEST}  ||
         DIR_VALUE     == {LEAF0,EAST}  && is_east_edge_RTR ||
         DIR_VALUE     == {LEAF1,EAST}  && is_east_edge_RTR ||
         DIR_VALUE     == {LEAF0,WEST}  && is_west_edge_RTR ||
         DIR_VALUE     == {LEAF1,WEST}  && is_west_edge_RTR ||
         DIR_VALUE     == {NORTH,EAST}  && is_north_edge_RTR||
         DIR_VALUE     == {NORTH,WEST}  && is_north_edge_RTR||
         NO_RESP_TRAFFIC_PORTS;

  generate 
    if (!illegal_req_paths && !NO_REQ_TRAFFIC_PORTS) begin:wreq_expected

      for (genvar vc = 0; vc < REQ_TOTAL_NUM_VC ; vc ++ ) begin

        transaction_tracker_sva # (

          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)

        ) cip_rtr_dnoc_aw_sva (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_valid && d_noc_in_vc == vc && dnoc_in_is_AW_W_channel && dnoc_tgt_dir_valid && (IS_X2L_INV2?d_noc_in_iid == IID:1)),
          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_valid && d_noc_out_vc == vc && dnoc_out_is_AW_channel && d_noc_out_iid == IID),
          .clk        (clk),
          .reset_n    (reset_n)

        );

      end

      if (DIR_VALUE[5:3]==LEAF0) begin

        `SV_ASSERT (FVPH_RTR_FV_as_REQ_NOT_EXPECTED_FROM_DISABLED_LEAF0,   left_pe_disabled && d_noc_out_valid && dnoc_out_is_AW_channel |-> d_noc_out_iid != IID  );

      end
      if (DIR_VALUE[5:3]==LEAF1) begin

        `SV_ASSERT (FVPH_RTR_FV_as_REQ_NOT_EXPECTED_FROM_DISABLED_LEAF0,   right_pe_disabled && d_noc_out_valid && dnoc_out_is_AW_channel |-> d_noc_out_iid != IID  );

      end

    end else begin

        `SV_ASSERT (FVPH_RTR_FV_as_WRITE_NOT_VALID,        !(d_noc_out_valid && dnoc_out_is_AW_channel  && d_noc_out_iid == IID) );

    end

  endgenerate

  generate 
    if (!illegal_resp_paths ) begin:rresp_expected

      if(GEN_ADD_COVS) begin:R_RESP_COV
        `SV_COVER (FVPH_RTR_FV_co_READ_UNICAST,            d_noc_out_valid && dnoc_out_is_R_channel && d_noc_out_iid == IID );
      end
      
      for (genvar vc = 0; vc < RESP_TOTAL_NUM_VC ; vc ++ ) begin

        transaction_tracker_sva # (

          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)

        ) cip_rtr_dnoc_r_sva (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_valid && dnoc_in_is_R_channel && dnoc_tgt_dir_valid && (IS_X2L_INV2?d_noc_in_iid == IID:1)),
          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_valid && dnoc_out_is_R_channel && d_noc_out_iid == IID),
          .clk        (clk),
          .reset_n    (reset_n)

        );

      end

      // if (IID != cip_rtr_pkg::NOC_LEAF0 && IID != cip_rtr_pkg::NOC_LEAF1 && GEN_ADD_COVS) begin: RDM_expected_from_every_source_except_leaf 
      
      //     `SV_COVER (FVPH_RTR_FV_co_READ_MULTICAST_COL_WISE, (d_noc_out_valid && dnoc_out_is_R_channel && d_noc_out_iid == IID && d_noc_out_rcc_opcode == cip_pkg::CC_OPCODE_E_RDM &&   
      //                                     d_noc_out_rcc_dir == cip_pkg::ROW_COLUMN_SELECT_E_COLUMN) || ( (towards_left_pe || towards_west) && is_west_edge_RTR) || ( (towards_north || from_north) && is_north_edge_RTR) );
                                        
      //     `SV_COVER (FVPH_RTR_FV_co_READ_MULTICAST_ROW_WISE, (d_noc_out_valid && dnoc_out_is_R_channel && d_noc_out_iid == IID && d_noc_out_rcc_opcode == cip_pkg::CC_OPCODE_E_RDM &&   
      //                                     d_noc_out_rcc_dir == cip_pkg::ROW_COLUMN_SELECT_E_ROW) || ( (towards_left_pe || towards_west) && is_west_edge_RTR) || ( (towards_north || from_north) && is_north_edge_RTR)   );

      // end

    end 
    else if (!NO_RESP_TRAFFIC_PORTS) begin:r_resp_not_expected

        `SV_ASSERT (FVPH_RTR_FV_as_READ_NOT_EXPECTED,      d_noc_out_valid && dnoc_out_is_R_channel   |-> d_noc_out_iid != IID );     
      
    end else begin

        `SV_ASSERT (FVPH_RTR_FV_as_READ_NOT_VALID,         !(d_noc_out_valid && dnoc_out_is_R_channel && d_noc_out_iid == IID) );     

    end

  endgenerate



endmodule
