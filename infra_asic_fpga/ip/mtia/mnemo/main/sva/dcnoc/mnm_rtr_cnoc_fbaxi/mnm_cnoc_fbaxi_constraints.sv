/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_fbaxi_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_cnoc_fbaxi_constraints # (
  parameter NUM_VC = 11
) (
  // c_noc
  input   mnm_pkg::control_noc_t      c_noc_in,
  input   logic                       c_noc_in_valid,

  	// System Signals
  input   logic                       clk,
  input   logic                       reset_n
    
);

  `include "mnm_cnoc_input_signal_defines.sv"


	//------------------------------------------------------------------------------
	//-- FBAXI Constraints --
	//------------------------------------------------------------------------------

	generate
	
    //------------------------------------------------------------------------------
	  //-- AXI AR Channel --
	  //------------------------------------------------------------------------------

		// A burst must not cross a 4kbyte boundary
  	wire [mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:0] c_noc_in_araddr_at_burst_end;
  	assign c_noc_in_araddr_at_burst_end = c_noc_in_araddr + (c_noc_in_arlen << c_noc_in_arsize);

		// if (mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH > 12) begin : addr_width_more_than_12
    //     // AM  CNOC AR channel: addr locations in a burst are all within the same 4kB page 
    //     `SV_ASSERT (FVPH_RTR_FV_am_cnoc_araddr_burst_within_4kb_boundary, c_noc_in_arvalid |-> c_noc_in_araddr[mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:12] == c_noc_in_araddr_at_burst_end[mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:12]);
    // end

    // AM  CNOC AR channel: src_id coords are within grid  @*/
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_arsrcid_coords_within_grid, c_noc_in_arvalid |-> (c_noc_in_arsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_in_arsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                																							                       (c_noc_in_arsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_in_arsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
  
    // AM  CNOC AR channel: tgt_id coords within grid  @*/
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_artgtid_coords_within_grid, c_noc_in_arvalid |-> (c_noc_in_artgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_in_artgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
               																														 					 (c_noc_in_artgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_in_artgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));

    // AM  CNOC AR channel: noc_id has legal values
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_arnocid_is_legal,           c_noc_in_arvalid |-> (c_noc_in_arnocid >= 0) && ((c_noc_in_arnocid <= 11)));

  	// AM  CNOC AR channel: user.vc only has legal values  
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_aruser_vc_is_legal,         c_noc_in_arvalid |-> c_noc_in_aruservc < mnm_pkg::MNM_CNOC_AR_NUM_VC);


		//------------------------------------------------------------------------------
	  //-- B Channel --
	  //------------------------------------------------------------------------------

    // AM  CNOC AR channel: src_id coords are within grid
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_bsrcid_coords_within_grid,  c_noc_in_bvalid |->  (c_noc_in_bsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_in_bsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                																							                       (c_noc_in_bsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_in_bsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    
		// AM  CNOC B channel: tgt_id coords are within grid
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_btgtid_coords_within_grid,  c_noc_in_bvalid |->  (c_noc_in_btgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_in_btgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                 																													           (c_noc_in_btgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_in_btgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));

    // AM  CNOC B channel: noc_id has legal values
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_bnocid_is_legal,            c_noc_in_bvalid |-> (c_noc_in_bnocid >= 0) && ((c_noc_in_bnocid <= 11)));

		// AM  CNOC B channel: user.vc only has legal values
    `SV_ASSERT (FVPH_RTR_FV_am_cnoc_buser_vc_is_legal,          c_noc_in_bvalid |->  c_noc_in_buservc < mnm_pkg::MNM_CNOC_B_NUM_VC);

	endgenerate

endmodule