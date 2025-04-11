/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_routing_constraints.sv
// This file contains mnm routing constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_routing_constraints # (
  parameter LANE_NUM = 0,
  parameter NUM_VC   = 11
) (
  input     mnm_pkg::data_noc_t                            d_noc_in,
  input     logic                                          d_noc_in_valid,

  input     mnm_pkg::data_noc_t                            d_noc_out,
  input     logic                                          d_noc_out_valid,

  input     mnm_pkg::mnm_grid_location_t                   rtr_location,
  input     logic   [NUM_VC-1:0]                           is_y_first,

  input     mnm_pkg::coord_id_t                            d_noc_in_tgtid,
  input     mnm_pkg::coord_id_t                            d_noc_in_srcid,

  input     logic                                          clk,
  input     logic                                          reset_n
);

    `include "../mnm_rtr_lib/mnm_dnoc_input_signal_defines.sv"
	
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

	logic [NUM_VC-1:0] is_x_first;

    logic [NUM_VC-1:0] d_noc_east_in_tgt_id;
    logic [NUM_VC-1:0] d_noc_west_in_tgt_id;
    logic [NUM_VC-1:0] d_noc_north_in_tgt_id;
    logic [NUM_VC-1:0] d_noc_south_in_tgt_id;

    logic [NUM_VC-1:0] d_noc_east_in_src_id;
    logic [NUM_VC-1:0] d_noc_west_in_src_id;
    logic [NUM_VC-1:0] d_noc_north_in_src_id;
    logic [NUM_VC-1:0] d_noc_south_in_src_id;
    logic              d_noc_llc_in_src_id;
    logic              d_noc_peg_in_src_id;


	assign    d_noc_llc_in_src_id   = (d_noc_in_srcid.xcoord == rtr_location.xcoord) && (d_noc_in_srcid.ycoord == rtr_location.ycoord) && (d_noc_in_srcid.chip_id.z == rtr_location.chip_id.z);
	assign    d_noc_peg_in_src_id   = (d_noc_in_srcid.xcoord == rtr_location.xcoord) && (d_noc_in_srcid.ycoord == rtr_location.ycoord) && (d_noc_in_srcid.chip_id.z != rtr_location.chip_id.z);
	
    for (genvar vc = 0; vc < (mnm_pkg::MNM_DNOC_R_NUM_VC + mnm_pkg::MNM_DNOC_AWW_NUM_VC) ; vc ++ ) begin

      	assign is_x_first[vc] = !is_y_first[vc];

		assign    d_noc_north_in_tgt_id[vc] = is_y_first[vc]  ? (((d_noc_in_tgtid.ycoord >= rtr_location.ycoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)) || (d_noc_in_tgtid.chip_id.y != rtr_location.chip_id.y)):
										      is_x_first[vc]  ? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord >= rtr_location.ycoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)) || (d_noc_in_tgtid.chip_id.y != rtr_location.chip_id.y): '0; 

		assign    d_noc_east_in_tgt_id[vc]  = is_y_first[vc]  ? ((d_noc_in_tgtid.xcoord <= rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)):
										      is_x_first[vc]  ? ((d_noc_in_tgtid.xcoord <= rtr_location.xcoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)): '0;
	
		assign    d_noc_south_in_tgt_id[vc] = is_y_first[vc]  ? ((d_noc_in_tgtid.ycoord <= rtr_location.ycoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)):
										      is_x_first[vc]  ? ((d_noc_in_tgtid.ycoord <= rtr_location.ycoord) && (d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)): '0;  

		assign    d_noc_west_in_tgt_id[vc]  = is_y_first[vc]  ? ((d_noc_in_tgtid.xcoord >= rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)):
										      is_x_first[vc]  ? ((d_noc_in_tgtid.xcoord >= rtr_location.xcoord) && (d_noc_in_tgtid.chip_id.y == rtr_location.chip_id.y)): '0;


		assign    d_noc_north_in_src_id[vc] = is_y_first[vc]  ? ((d_noc_in_srcid.ycoord < rtr_location.ycoord) && (d_noc_in_srcid.xcoord == rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)):
										      is_x_first[vc]  ? ((d_noc_in_srcid.ycoord < rtr_location.ycoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)): '0;

		assign    d_noc_east_in_src_id[vc]  = is_y_first[vc]  ? (((d_noc_in_srcid.xcoord > rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)) || ((d_noc_in_srcid.xcoord <= rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y != rtr_location.chip_id.y))):
										      is_x_first[vc]  ? ((d_noc_in_srcid.xcoord > rtr_location.xcoord) && (d_noc_in_srcid.ycoord == rtr_location.ycoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)) : '0;

		assign    d_noc_south_in_src_id[vc] = is_y_first[vc]  ? (((d_noc_in_srcid.ycoord > rtr_location.ycoord) && (d_noc_in_srcid.xcoord == rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)) || ((d_noc_in_srcid.chip_id.y != rtr_location.chip_id.y) && (d_noc_in_srcid.xcoord == (mnm_pkg::MNM_RTR_GRID_COORD_X_END+1-rtr_location.xcoord)))):
										  	  is_x_first[vc]  ? (((d_noc_in_srcid.ycoord > rtr_location.ycoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)) || (d_noc_in_srcid.chip_id.y != rtr_location.chip_id.y)): '0;

		assign    d_noc_west_in_src_id[vc]  = is_y_first[vc]  ? (((d_noc_in_srcid.xcoord < rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)) || ((d_noc_in_srcid.xcoord > (mnm_pkg::MNM_RTR_GRID_COORD_X_END+1-rtr_location.xcoord) && (d_noc_in_srcid.chip_id.y != rtr_location.chip_id.y)))) :
										      is_x_first[vc]  ? ((d_noc_in_srcid.xcoord < rtr_location.xcoord) && (d_noc_in_srcid.ycoord == rtr_location.ycoord) && (d_noc_in_srcid.chip_id.y == rtr_location.chip_id.y)): '0;


		if ((LANE_NUM == north0)  || (LANE_NUM == north1))      begin:north
    		`SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_id_north , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_north_in_tgt_id[vc]);
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_north , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_north_in_src_id[vc]);
		end
		else if ((LANE_NUM == east0)  || (LANE_NUM == east1))   begin: east
			`SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_id_east  , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_east_in_tgt_id[vc]);
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_east  , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_east_in_src_id[vc]);
		end
		else if ((LANE_NUM == south0)  || (LANE_NUM == south1)) begin: south
			`SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_id_south , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_south_in_tgt_id[vc]);
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_south , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_south_in_src_id[vc]);
		end
		else if ((LANE_NUM == west0)  || (LANE_NUM == west1))   begin: west
			`SV_ASSERT (FVPH_RTR_FV_am_valid_tgt_id_west  , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_west_in_tgt_id[vc] );
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_west  , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_west_in_src_id[vc] );
		end
		else if ((LANE_NUM == llc0)  || (LANE_NUM == llc1))		begin: llc
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_llc   , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_llc_in_src_id      );
		end
		else if (LANE_NUM == peg)                               begin: peg
			`SV_ASSERT (FVPH_RTR_FV_am_valid_src_id_peg   , d_noc_in_valid && d_noc_in_vc == vc |-> d_noc_peg_in_src_id      );
		end
	end

endmodule