/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_routing_checker.sv
// This file contains mnm routing checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_routing_checker# (
  parameter NUM_VC              = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC,
  parameter d_noc_in_lane       = 0,
  parameter d_noc_out_lane      = 0
) (
	input     mnm_pkg::data_noc_t                            d_noc_in,
	input     logic                                          d_noc_in_valid,

	input     mnm_pkg::data_noc_t                            d_noc_out,
	input     logic                                          d_noc_out_valid,

  input     mnm_pkg::mnm_grid_location_t                   rtr_location,
  input     logic                          [NUM_VC-1:0]    is_y_first,

	input     logic                                          clk,
	input     logic                                          reset_n
);

    `include "../mnm_rtr_dnoc_fbaxi/mnm_dnoc_input_signal_defines.sv"
    `include "../mnm_rtr_dnoc_fbaxi/mnm_dnoc_output_signal_defines.sv"

    logic                                   [NUM_VC-1:0]   is_x_first;
    
    logic off_chip_2s;
    logic _2e;
    logic _2w;
    logic _2s;
    logic _2n;
    logic _2peg;
    logic _2llc;
    
    `SV_ASSERT (FVPH_RTR_FV_am_noc_iid_tracking               ,   d_noc_in_iid           == d_noc_in_lane);

    `SV_ASSERT (FVPH_RTR_FV_am_rtr_on_mnemo                   ,   rtr_location.chip_id.z == '0);

    // `SV_ASSERT (FVPH_RTR_FV_am_metis_never_tgt_for_req        ,   d_noc_in_awvalid    && (d_noc_in_awtgtid.chip_id.z != 1));

    // `SV_ASSERT (FVPH_RTR_FV_am_metis_never_src_for_resp       ,   d_noc_in_rvalid     && (d_noc_in_rsrcid.chip_id.z != 1));

    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rtr_coords_within_grid,  d_noc_in_valid |-> 
                                                             (rtr_location.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START) && (rtr_location.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END) &&
                                                             (rtr_location.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START) && (rtr_location.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END));

    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_src_coords_within_grid,  d_noc_in_valid |-> 
                                                             (d_noc_in_srcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_in_srcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                                                             (d_noc_in_srcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_in_srcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));  
    
    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_coords_within_grid,  d_noc_in_valid |-> 
                                                             (d_noc_in_tgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_in_tgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                                                             (d_noc_in_tgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_in_tgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1)); 


    for (genvar vc = 0; vc < (mnm_pkg::MNM_DNOC_R_NUM_VC + mnm_pkg::MNM_DNOC_AWW_NUM_VC) ; vc ++ ) begin

      assign is_x_first[vc] = !is_y_first[vc];

      // If the chip_id.y does not match the router’s rtr_location.chip_id.y, the router first routes south to the correct Mnemo. 
      assign off_chip_2s = (d_noc_in_tgtid.chip_id.y != rtr_location.chip_id.y);

      assign _2e = off_chip_2s? '0   : (is_x_first[vc]? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) : 
                    (is_y_first[vc]?   ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) :  '0 ) : '0));

      assign _2w = off_chip_2s? '0   : (is_x_first[vc]? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) : 
                    (is_y_first[vc]?   ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) :  '0 ) : '0));

      assign _2s = off_chip_2s? '1   : (is_y_first[vc]? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) : 
                    (is_x_first[vc]?   ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) :  '0 ) : '0));

      assign _2n = off_chip_2s? '0   : (is_y_first[vc]? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) : 
                    (is_x_first[vc]?   ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) :  '0 ) : '0));

      assign _2peg = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.z == '1)? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord)) : '0);
      assign _2llc = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.z == rtr_location.chip_id.z) && (d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord));

    if (vc < mnm_pkg::MNM_DNOC_R_NUM_VC)  begin: r_2e_checker
      transaction_tracker_sva # (

        .DATA_WIDTH(1),
        .CHECKER_DEPTH(64)
      ) transaction_tracker_sva_2e (

        .data_in    (d_noc_in.payload.daxi_r.data[0]),
        .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2e),

        .data_out   (d_noc_out.payload.daxi_r.data[0]),
        .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

        .clk        (clk),
        .reset_n    (reset_n)
      );
      end
      
      else begin: aww_2e_checker
      transaction_tracker_sva # (

        .DATA_WIDTH(1),
        .CHECKER_DEPTH(64)
      ) transaction_tracker_sva_2e (

        .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
        .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2e),

        .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
        .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

        .clk        (clk),
        .reset_n    (reset_n)
      );
    end  

  end


endmodule