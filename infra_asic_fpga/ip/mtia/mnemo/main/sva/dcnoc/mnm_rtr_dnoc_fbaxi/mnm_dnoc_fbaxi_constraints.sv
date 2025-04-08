/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_fbaxi_constraints # (
  parameter NUM_VC = 11
) (
  // d_noc
  input   mnm_pkg::data_noc_t         d_noc_in,
  input   logic                       d_noc_in_valid,

  	// System Signals
  input   logic                       clk,
  input   logic                       reset_n
    
);

  `include "mnm_dnoc_input_signal_defines.sv"


	//------------------------------------------------------------------------------
	//-- FBAXI Constraints --
	//------------------------------------------------------------------------------
	
	generate
	
    localparam TOTAL_NUM_VC_WIDTH = $clog2(NUM_VC + 1);
    wire [TOTAL_NUM_VC_WIDTH-1:0] d_noc_payload_vc;
    assign d_noc_payload_vc = (d_noc_in.channel == mnm_pkg::DNOC_CHANNEL_E_READ) ? TOTAL_NUM_VC_WIDTH'('d0)
                                                                                  :TOTAL_NUM_VC_WIDTH'('d1) + d_noc_in_vc;

    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_vc_same_throughout_burst, d_noc_in_valid && !d_noc_in_last |=> $stable(d_noc_payload_vc));


    //------------------------------------------------------------------------------
    //-- AXI AW+W Channel --
    //------------------------------------------------------------------------------

		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_awvalids_in_burst_are_consecutive, d_noc_in_awvalid && !d_noc_in_wlast |=> d_noc_in_awvalid);
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlens_in_burst_same_throughout,   d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_awlen));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_awaddrs_in_burst_same_throughout,  d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_awaddr));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_awids_in_burst_same_throughout,    d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_awid));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_awusers_in_burst_same_throughout,  d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_awuser));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_wusers_in_burst_same_throughout,   d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_wuser));
    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awsize_in_burst_same_throughout,   d_noc_in_awvalid && !d_noc_in_wlast |=> $stable(d_noc_in_awsize));

		// track number of beats seen so far in a AW+W burst
		logic [1-1:0] d_noc_in_wdata_items_seen;  // Need to confirm size

		always_ff @(posedge clk or negedge reset_n) begin
				if (!reset_n) begin
						d_noc_in_wdata_items_seen <= '0;
				end
				else if (d_noc_in_awvalid) begin
						if (d_noc_in_wlast) begin
								d_noc_in_wdata_items_seen <= '0;
						end
						else begin
								d_noc_in_wdata_items_seen <= d_noc_in_wdata_items_seen + 2'b01;
						end
				end
		end 

		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_wlast_as_expected,                 d_noc_in_awvalid |-> d_noc_in_wlast == (d_noc_in_wdata_items_seen == d_noc_in_awlen));
	  `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awuser_vc_is_legal,                d_noc_in_awvalid |-> d_noc_in_awuservc < mnm_pkg::MNM_DNOC_AWW_NUM_VC);
 

    //------------------------------------------------------------------------------
    //-- AXI R Channel --
    //------------------------------------------------------------------------------

		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_rvalids_in_burst_are_consecutive, d_noc_in_rvalid && !d_noc_in_rlast |=> d_noc_in_rvalid);
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_rids_in_burst_same_throughout,    d_noc_in_rvalid && !d_noc_in_rlast |=> $stable(d_noc_in_rid));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlens_in_burst_same_throughout,   d_noc_in_rvalid && !d_noc_in_rlast |=> $stable(d_noc_in_rlen));
		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_rusers_in_burst_same_throughout,  d_noc_in_rvalid && !d_noc_in_rlast |=> $stable(d_noc_in_ruser));

		// track number of beats seen so far in a R burst
		logic [1-1:0] d_noc_in_rdata_items_seen;  // Need to confirm size

		always_ff @(posedge clk or negedge reset_n) begin
			if (!reset_n) begin
				d_noc_in_rdata_items_seen <= '0;
			end
			else if (d_noc_in_rvalid) begin
				if (d_noc_in_rlast) begin
					d_noc_in_rdata_items_seen <= '0;
				end
				else begin
					d_noc_in_rdata_items_seen <= d_noc_in_rdata_items_seen + 2'b01;
				end
			end
		end

		`SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlast_as_expected,                d_noc_in_rvalid |-> d_noc_in_rlast == (d_noc_in_rdata_items_seen == d_noc_in_rlen));
    `SV_ASSERT (FVPH_RTR_FV_am_dnoc_ruser_vc_is_legal,                d_noc_in_rvalid |-> d_noc_in_ruservc < mnm_pkg::MNM_DNOC_R_NUM_VC);

	endgenerate

endmodule