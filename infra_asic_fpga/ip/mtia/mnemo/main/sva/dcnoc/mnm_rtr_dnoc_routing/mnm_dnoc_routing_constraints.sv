/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_routing_constraints.sv
// This file contains mnm routing constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_routing_constraints # (
  parameter LANE_NUM = 0
) (
  input     mnm_pkg::data_noc_t                            d_noc_in,
  input     logic                                          d_noc_in_valid,

  input     mnm_pkg::data_noc_t                            d_noc_out,
  input     logic                                          d_noc_out_valid,

  input     mnm_pkg::mnm_grid_location_t                   rtr_location,

	input     mnm_pkg::coord_id_t                            d_noc_in_tgtid,
	input     mnm_pkg::coord_id_t                            d_noc_in_srcid,

  input     logic                                          clk,
  input     logic                                          reset_n
);
	
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



endmodule