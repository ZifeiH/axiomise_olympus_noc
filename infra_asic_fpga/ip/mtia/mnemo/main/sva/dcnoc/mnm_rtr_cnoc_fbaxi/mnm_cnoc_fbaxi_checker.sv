/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_fbaxi_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_cnoc_fbaxi_checker # (
  parameter NUM_VC = 11
) (
  // c_noc
  input   mnm_pkg::control_noc_t      c_noc_out,
  input   logic                       c_noc_out_valid,

  	// System Signals
  input   logic                       clk,
  input   logic                       reset_n
    
);

  `ifdef ASSERT_OFF
    `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
  `endif

  `include "mnm_cnoc_output_signal_defines.sv"


	//------------------------------------------------------------------------------
	//-- FBAXI Checker --
	//------------------------------------------------------------------------------

	generate
	
    //------------------------------------------------------------------------------
	  //-- ttl --
	  //------------------------------------------------------------------------------

    // Couldn't find c_noc_out.ttl
    // `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_at_least_1,     c_noc_out_valid |-> c_noc_out.ttl != '0);
    // `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_within_maximum, c_noc_out_valid |-> c_noc_out.ttl <= mnm_pkg::MNM_NOC_TTL_DEFAULT);
    
    
    //------------------------------------------------------------------------------
	  //-- AXI AR Channel --
	  //------------------------------------------------------------------------------

		// A burst must not cross a 4kbyte boundary
  	wire [mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:0] c_noc_out_araddr_at_burst_end;
  	assign c_noc_out_araddr_at_burst_end = c_noc_out_araddr + (c_noc_out_arlen << c_noc_out_arsize);

		if (mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH > 12) begin : addr_width_more_than_12
        // AS  CNOC AR channel: addr locations in a burst are all within the same 4kB page
        `SV_ASSERT (FVPH_RTR_FV_as_cnoc_araddr_burst_within_4kb_boundary, c_noc_out_arvalid |-> c_noc_out_araddr[mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:12] == c_noc_out_araddr_at_burst_end[mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:12]);
    end

    // AS  CNOC AR channel: src_id coords are within grid
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arsrcid_coords_within_grid, c_noc_out_arvalid |-> (c_noc_out_arsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_out_arsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                																							                        (c_noc_out_arsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_out_arsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    
    // AS  CNOC AR channel: tgt_id coords within grid
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_artgtid_coords_within_grid, c_noc_out_arvalid |-> (c_noc_out_artgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_out_artgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
               																														 					  (c_noc_out_artgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_out_artgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
  	
    // AS  CNOC AR channel: noc_id has legal values
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arnocid_is_legal,           c_noc_out_arvalid |-> (c_noc_out_arnocid >= 0) && ((c_noc_out_arnocid <= 11)));
    
    // AS  CNOC AR channel: user.vc only has legal values 
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_aruser_vc_is_legal,         c_noc_out_arvalid |-> c_noc_out_aruservc < mnm_pkg::MNM_CNOC_AR_NUM_VC);


		//------------------------------------------------------------------------------
	  //-- B Channel --
	  //------------------------------------------------------------------------------

    // AS  CNOC AR channel: src_id coords are within grid
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_bsrcid_coords_within_grid,  c_noc_out_bvalid |->  (c_noc_out_bsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_out_bsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                																							                        (c_noc_out_bsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_out_bsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    
		// AS  CNOC B channel: tgt_id coords are within grid
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_btgtid_coords_within_grid,  c_noc_out_bvalid |->  (c_noc_out_btgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (c_noc_out_btgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                 																													            (c_noc_out_btgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (c_noc_out_btgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));

    // AS  CNOC B channel: noc_id has legal values
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_bnocid_is_legal,            c_noc_out_bvalid |-> (c_noc_out_bnocid >= 0) && ((c_noc_out_bnocid <= 11)));

		// AS  CNOC B channel: user.vc only has legal values
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_buser_vc_is_legal,          c_noc_out_bvalid |->  c_noc_out_buservc < mnm_pkg::MNM_CNOC_B_NUM_VC);

	endgenerate

endmodule