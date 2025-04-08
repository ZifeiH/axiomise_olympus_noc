/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_checker.sv
// This file contains mnm dnoc checkers
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_checker # (
  parameter NUM_LANES           = mnm_rtr_pkg::MNM_RTR_DNOC_SLICE_NUM_LANES,
            NUM_VC              = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC,
            VCID_W              = mnm_rtr_pkg::MNM_RTR_DNOC_VCID_W,
            RX_DEPTH_W          = mnm_rtr_pkg::MNM_RTR_DNOC_RX_DEPTH_W,
            NUM_SHRD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS,
            NUM_RSVD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS,
            RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS),
            REMOVE_LANE         = {NUM_LANES{1'b0}}
) (
    input   logic                                                                                reset_n,
    input   logic                                                                                clk,

    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              d_noc_in,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_in_valid,

    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              d_noc_out,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_out_valid,

    input   mnm_pkg::mnm_grid_location_t                                                         rtr_location,
    input logic                                                     [NUM_VC-1:0]                 is_y_first
);  

    

    if (!REMOVE_LANE[north0] && !REMOVE_LANE[east0]) begin: n2e_checker
		mnm_dnoc_routing_checker #(
            .NUM_VC                           (NUM_VC),
            .d_noc_in_lane                    (north0),
            .d_noc_out_lane                   (east0)
        ) mnm_dnoc_routing_checker(
          	.d_noc_in             (d_noc_in[north0]),
          	.d_noc_in_valid       (d_noc_in_valid[north0]),

          	.d_noc_out            (d_noc_out[east0]),
         	.d_noc_out_valid      (d_noc_out_valid[east0]),

            .rtr_location         (rtr_location),
            .is_y_first           (is_y_first),

        	.clk                  (clk),
          	.reset_n              (reset_n)
    	);
	end
   
endmodule