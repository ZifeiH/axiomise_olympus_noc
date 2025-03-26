/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_checker.sv
// This file contains mnm fbaxi checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_fbaxi_checker # (
  parameter NUM_VC  = 11
) (
  // d_noc
  input   mnm_pkg::data_noc_t         d_noc_out,
  input   logic                       d_noc_out_valid,

  // System Signals
  input   logic                       clk,
  input   logic                       reset_n

);

  `ifdef ASSERT_OFF
    `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
  `endif

  `include "mnm_dnoc_output_signal_defines.sv"

	//------------------------------------------------------------------------------
	//-- FBAXI Checker --
	//------------------------------------------------------------------------------
  generate
    
    // ttl 
    // Couldn't find d_noc_out.ttl
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_at_least_1,     d_noc_out_valid |-> d_noc_out.ttl != '0);
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_within_maximum, d_noc_out_valid |-> d_noc_out.ttl <= mnm_pkg::MNM_NOC_TTL_DEFAULT);
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_same_throughout_burst,  d_noc_out_valid && !dnoc_last |=> $stable(d_noc_out.ttl));

    localparam TOTAL_NUM_VC_WIDTH = $clog2(NUM_VC + 1);
    wire [TOTAL_NUM_VC_WIDTH-1:0] dnoc_payload_vc;
    assign dnoc_payload_vc = (d_noc_out.channel == mnm_pkg::DNOC_CHANNEL_E_READ) ? TOTAL_NUM_VC_WIDTH'('d0)
                                                                                  : TOTAL_NUM_VC_WIDTH'('d1) + d_noc_out_vc;

    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_vc_same_throughout_burst, d_noc_out_valid && !d_noc_out_last |=> $stable(dnoc_payload_vc));

    // AXI AW+W channel
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awvalids_in_burst_are_consecutive, d_noc_out_awvalid && !d_noc_out_wlast |=> d_noc_out_awvalid);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlens_in_burst_same_throughout,   d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awlen));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddrs_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awaddr));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awids_in_burst_same_throughout,    d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awid));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awusers_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awuser));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wusers_in_burst_same_throughout,   d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_wuser));

    // track number of beats seen so far in a AW+W burst
    logic [1-1:0] d_noc_out_wdata_items_seen;  // Need to confirm size

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        d_noc_out_wdata_items_seen <= '0;
      end
      else if (d_noc_out_awvalid) begin
        if (d_noc_out_wlast) begin
          d_noc_out_wdata_items_seen <= '0;
        end
        else begin
          d_noc_out_wdata_items_seen <= d_noc_out_wdata_items_seen + 2'b01;
        end
      end
    end

    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wlast_as_expected,                  d_noc_out_awvalid |-> d_noc_out_wlast == (d_noc_out_wdata_items_seen == d_noc_out_awlen));

    // A burst must not cross a 4kbyte boundary
    wire [mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:0] d_noc_out_awaddr_at_burst_end;
    assign d_noc_out_awaddr_at_burst_end = d_noc_out_awaddr + (d_noc_out_awlen << d_noc_out_awsize); 
    
    if (mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH > 12) begin : addr_width_more_than_12
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddr_burst_within_4kb_boundary, d_noc_out_awvalid |-> d_noc_out_awaddr[mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:12] == d_noc_out_awaddr_at_burst_end[mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:12]);
    end

    // Don't need this yet, will be part of routing
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsrcid_coords_within_grid, d_noc_out_awvalid |-> (d_noc_out_awsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_awsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
    //                                                                                    (d_noc_out_awsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_awsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awtgtid_coords_within_grid, d_noc_out_awvalid |-> (d_noc_out_awtgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_awtgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
    //                                                                                    (d_noc_out_awtgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_awtgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));

    // Couldn't find d_noc_out.payload.daxi_combo_aw_w.w.strb
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_wstrb_enc_value_is_legal,            d_noc_out_awvalid && awhost |-> wstrb_enc);
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_beat_offset_in_burst_same_throughout, d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_beat_offset));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsize_in_burst_same_throughout,            d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awsize));
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_subf_in_burst_same_throughout,        d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_subf));
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_rord_in_burst_same_throughout,        d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_rord));
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_size_field_value_is_legal,           d_noc_out_awvalid && awhost |-> d_noc_out_awsize != 3'b111);

    // Couldn't find d_noc_out_awuser_reduction_type
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_reduction_type_value_is_legal,       d_noc_out_awvalid |-> d_noc_out_awuser_reduction_type inside {4'b0000, 4'b0100, 4'b0101, 4'b0110, 4'b1000,
    //                                                                                                                                            4'b1001, 4'b1010, 4'b1100, 4'b1101, 4'b1110});
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_vc_is_legal,                         d_noc_out_awvalid |-> d_noc_out_awuservc < WRITE_VCS);

    // AXI R channel
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rvalids_in_burst_are_consecutive, d_noc_out_rvalid && !d_noc_out_rlast |=> d_noc_out_rvalid);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rids_in_burst_same_throughout,    d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_rid));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlens_in_burst_same_throughout,   d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_rlen));
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rusers_in_burst_same_throughout,  d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_ruser));

    // track number of beats seen so far in a R burst
    logic [1-1:0] d_noc_out_rdata_items_seen;  // Need to confirm mapping

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        d_noc_out_rdata_items_seen <= '0;
      end
      else if (d_noc_out_rvalid) begin
        if (d_noc_out_rlast) begin
          d_noc_out_rdata_items_seen <= '0;
        end
        else begin
          d_noc_out_rdata_items_seen <= d_noc_out_rdata_items_seen + 2'b01;
        end
      end
    end

    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlast_as_expected,                d_noc_out_rvalid |-> d_noc_out_rlast == (d_noc_out_rdata_items_seen == d_noc_out_rlen));

    // Don't need this yet, will be part of routing
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rtgtid_coords_within_grid,        d_noc_out_rvalid |-> (d_noc_out_rtgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_rtgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
    //                                                                                         (d_noc_out_rtgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_rtgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    // Couldn't fine d_noc_out.payload.daxi_r.user.cc_lane & d_noc_out.payload.daxi_r.user.cc_dir
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_row,            d_noc_out_rvalid && (d_noc_out_rcc_dir == mnm_pkg::MNM_DAXI_RUSER_CC_DIR_WIDTH'('d1)) |-> (d_noc_out_rcc_lane < mnm_pkg::MNM_DAXI_RUSER_CC_LANE_WIDTH'('d13));
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_column,         d_noc_out_rvalid && (d_noc_out_rcc_dir == mnm_pkg::MNM_DAXI_RUSER_CC_DIR_WIDTH'('d0)) |-> (d_noc_out_rcc_lane < mnm_pkg::MNM_DAXI_RUSER_CC_LANE_WIDTH'('d6));


    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awcaches_in_burst_same_throughout, d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awcache)); // Couldn't find d_noc_out_awcache
    // `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlocks_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awlock));  // Couldn't find d_noc_out_awlock
    
  endgenerate

endmodule