/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_routing_checker.sv
// This file contains mnm routing checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_routing_checker# (
	parameter NUM_LANES           = mnm_rtr_pkg::MNM_RTR_DNOC_SLICE_NUM_LANES,
  parameter NUM_VC              = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC,
  parameter RX_DEPTH_W          = mnm_rtr_pkg::MNM_RTR_DNOC_RX_DEPTH_W,
  parameter NUM_SHRD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS,
  parameter NUM_RSVD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS,
  parameter RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS)
) (
	input     mnm_pkg::data_noc_t                            d_noc_in,
	input     logic                                          d_noc_in_valid,

	input     mnm_pkg::data_noc_t                            d_noc_out,
	input     logic                                          d_noc_out_valid,

	input     logic                                          clk,
	input     logic                                          reset_n
);

    `include "../mnm_rtr_dnoc_fbaxi/mnm_dnoc_input_signal_defines.sv"
    `include "../mnm_rtr_dnoc_fbaxi/mnm_dnoc_output_signal_defines.sv"
    `include "../mnm_rtr_lib/csr_signal_defines.sv"

    logic is_y_first;
    logic is_x_first;
    
    logic off_chip_2s;
    logic _2e;
    logic _2w;
    logic _2s;
    logic _2n;
    logic _2peg;
    logic _2llc;

    for (genvar vc = 0; vc < NUM_VC ; vc ++ ) begin

      assign is_y_first =  csr_cfg_vc_y_first_routing[vc]==1;
      assign is_x_first = !csr_cfg_vc_y_first_routing[vc];

      // If the chip_id.y does not match the router’s rtr_location.chip_id.y, the router first routes south to the correct Mnemo. 
      assign off_chip_2s = (d_noc_in_tgtid.chip_id.ycoord != rtr_location.chip_id.ycoord);

      assign _2e = off_chip_2s? '0 : (is_x_first? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) : 
                    (is_y_first? ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) :  '0 ) : '0));

      assign _2w = off_chip_2s? '0 : (is_x_first? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) : 
                    (is_y_first? ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) :  '0 ) : '0));

      assign _2s = off_chip_2s? '1 : (is_y_first? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) : 
                    (is_x_first? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) :  '0 ) : '0));

      assign _2n = off_chip_2s? '0 : (is_y_first? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) : 
                    (is_x_first? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) :  '0 ) : '0));

      assign _2peg = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.zcoord == '1)? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord)) : '0);
      assign _2llc = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.zcoord == rtr_location.chip_id.zcoord) && (d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord));


      transaction_tracker_sva # (

        .DATA_WIDTH(1),
        .CHECKER_DEPTH(64)
      ) transaction_tracker_sva_n2e (

        .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
        .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2e),

        .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
        .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc),

        .clk        (clk),
        .reset_n    (reset_n)

      );

  end
  	

endmodule