module fbaxi_d_noc_checker
#(
  // used to restrict which VCs are checked
  parameter USES_READ_VCS  = 1,
  parameter USES_WRITE_VCS = 1
)
(
    // System Signals
  clk,   
  reset_n,
  
  // d_noc
  d_noc_out_valid,
  d_noc_out,

);

  `ifdef ASSERT_OFF
    `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
  `endif

  // System Signals
  input logic clk;
  input logic reset_n;

  // d_noc
  input logic d_noc_out_valid,
  input logic mnm_pkg::data_noc_t d_noc_out,
    
  `include "mnm_d_noc_output_signal_defines.sv"


  generate
    
    // ttl 
    // Couldn't find d_noc_out.ttl
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_ttl_always_at_least_1,     d_noc_out_valid |-> d_noc_out.ttl != '0);
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_ttl_always_within_maximum, d_noc_out_valid |-> d_noc_out.ttl <= mnm_pkg::MNM_NOC_TTL_DEFAULT);
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_ttl_same_throughout_burst,  d_noc_out_valid && !d_noc_last |=> $stable(d_noc_out.ttl));

    localparam TOTAL_NUM_VCS_WIDTH = $clog2(TOTAL_NUM_VCS + 1);
    wire [TOTAL_NUM_VCS_WIDTH-1:0] d_noc_payload_vc;
    assign d_noc_payload_vc = (d_noc_out.channel == cip_pkg::NOC_CHANNEL_E_READ) ? TOTAL_NUM_VCS_WIDTH'('d0)
                                                                                : TOTAL_NUM_VCS_WIDTH'('d1) + d_noc_out.payload.daxi_combo_aw_w.aw.user.vc;

    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_vc_same_throughout_burst, d_noc_out_valid && !d_noc_last |=> $stable(d_noc_payload_vc));

    // AXI AW+W channel
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awvalids_in_burst_are_consecutive, d_noc_out_awvalid && !d_noc_out_wlast |=> d_noc_out_awvalid);
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awlens_in_burst_same_throughout,   d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awlen));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awaddrs_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awaddr));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awcaches_in_burst_same_throughout, d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awcache)); // Couldn't find d_noc_out_awcache
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awlocks_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awlock));  // Couldn't find d_noc_out_awlock
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awids_in_burst_same_throughout,    d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_wid));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awusers_in_burst_same_throughout,  d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awuser));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_wusers_in_burst_same_throughout,   d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_wuser));


    // track number of beats seen so far in a AW+W burst
    logic [1-1:0] d_noc_wdata_items_seen;  // Need to confirm size

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        d_noc_wdata_items_seen <= '0;
      end
      else if (d_noc_out_awvalid) begin
        if (d_noc_out_wlast) begin
          d_noc_wdata_items_seen <= '0;
        end
        else begin
          d_noc_wdata_items_seen <= d_noc_wdata_items_seen + 2'b01;
        end
      end
    end

    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_wlast_as_expected,                  d_noc_out_awvalid |-> d_noc_out_wlast == (d_noc_wdata_items_seen == d_noc_out_awlen));

    // A burst must not cross a 4kbyte boundary
    wire [mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:0] d_noc_out_awaddr_at_burst_end;
    // assign d_noc_out_awaddr_at_burst_end = d_noc_out_awaddr + (d_noc_out_awlen << d_noc_out_awsize); // Couldn't find d_noc_out_awsize

    if (mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH > 12) begin : addr_width_more_than_12
      `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awaddr_burst_within_4kb_boundary, d_noc_out_awvalid |-> d_noc_out_awaddr[mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:12] == d_noc_out_awaddr_at_burst_end[mnm_pkg::MNM_DAXI_AW_ADDR_WIDTH-1:12]);
    end
    // Do we need to check z-coord as well?
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awsrcid_coords_within_grid, d_noc_out_awvalid |-> (d_noc_out_awsrcid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_awsrcid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                                                                                       (d_noc_out_awsrcid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_awsrcid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awtgtid_coords_within_grid, d_noc_out_awvalid |-> (d_noc_out_awtgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_awtgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                                                                                       (d_noc_out_awtgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_awtgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));

    // Couldn't find d_noc_out.payload.daxi_combo_aw_w.w.strb
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awhost_wstrb_enc_value_is_legal,            d_noc_out_awvalid && awhost |-> wstrb_enc);
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_wstrb_beat_offset_in_burst_same_throughout, d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_beat_offset));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awsize_in_burst_same_throughout,            d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(d_noc_out_awsize));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_wstrb_subf_in_burst_same_throughout,        d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_subf));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_wstrb_rord_in_burst_same_throughout,        d_noc_out_awvalid && !d_noc_out_wlast |=> $stable(wstrb_rord));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awhost_size_field_value_is_legal,           d_noc_out_awvalid && awhost |-> d_noc_out_awsize != 3'b111);

    // Couldn't find d_noc_out_awuser_reduction_type
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awuser_reduction_type_value_is_legal,       d_noc_out_awvalid |-> d_noc_out_awuser_reduction_type inside {4'b0000, 4'b0100, 4'b0101, 4'b0110, 4'b1000,
    //                                                                                                                                            4'b1001, 4'b1010, 4'b1100, 4'b1101, 4'b1110});
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_awuser_vc_is_legal,                         d_noc_out_awvalid |-> d_noc_out_awuservc < WRITE_VCS);

    // AXI R channel

    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rvalids_in_burst_are_consecutive, d_noc_out_rvalid && !d_noc_out_rlast |=> d_noc_out_rvalid);
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rids_in_burst_same_throughout,    d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_rid));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rlens_in_burst_same_throughout,   d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_rlen));
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rusers_in_burst_same_throughout,  d_noc_out_rvalid && !d_noc_out_rlast |=> $stable(d_noc_out_ruser));

    // track number of beats seen so far in a R burst
    logic [1-1:0] d_noc_rdata_items_seen;  // Need to confirm mapping

    always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
        d_noc_rdata_items_seen <= '0;
      end
      else if (d_noc_out_rvalid) begin
        if (d_noc_out_rlast) begin
          d_noc_rdata_items_seen <= '0;
        end
        else begin
          d_noc_rdata_items_seen <= d_noc_rdata_items_seen + 2'b01;
        end
      end
    end

    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rlast_as_expected,                d_noc_out_rvalid |-> d_noc_out_rlast == (d_noc_rdata_items_seen == d_noc_out_rlen));

    // Do we need to check z-coord as well?
    `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rtgtid_coords_within_grid,        d_noc_out_rvalid |-> (d_noc_out_rtgtid.xcoord >= mnm_pkg::MNM_RTR_GRID_COORD_X_START-1) && (d_noc_out_rtgtid.xcoord <= mnm_pkg::MNM_RTR_GRID_COORD_X_END+1) &&
                                                                                            (d_noc_out_rtgtid.ycoord >= mnm_pkg::MNM_RTR_GRID_COORD_Y_START-1) && (d_noc_out_rtgtid.ycoord <= mnm_pkg::MNM_RTR_GRID_COORD_Y_END+1));
    // Couldn't fine d_noc_out.payload.daxi_r.user.cc_lane & d_noc_out.payload.daxi_r.user.cc_dir
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rcc_lane_is_legal_row,            d_noc_out_rvalid && (d_noc_out_rcc_dir == mnm_pkg::MNM_DAXI_RUSER_CC_DIR_WIDTH'('d1)) |-> (d_noc_out_rcc_lane < mnm_pkg::MNM_DAXI_RUSER_CC_LANE_WIDTH'('d13));
    // `SV_ASSERT (FVPH_RTR_FV_as_d_noc_rcc_lane_is_legal_column,         d_noc_out_rvalid && (d_noc_out_rcc_dir == mnm_pkg::MNM_DAXI_RUSER_CC_DIR_WIDTH'('d0)) |-> (d_noc_out_rcc_lane < mnm_pkg::MNM_DAXI_RUSER_CC_LANE_WIDTH'('d6));

  endgenerate

endmodule