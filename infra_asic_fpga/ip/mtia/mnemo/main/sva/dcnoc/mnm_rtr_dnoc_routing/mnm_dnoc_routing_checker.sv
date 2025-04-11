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

    `include "../mnm_rtr_lib/mnm_dnoc_input_signal_defines.sv"
    `include "../mnm_rtr_lib/mnm_dnoc_output_signal_defines.sv"

    logic [NUM_VC-1:0] is_x_first;
    
    logic off_chip_2s;
    logic [NUM_VC-1:0] _2e;
    logic [NUM_VC-1:0] _2w;
    logic [NUM_VC-1:0] _2s;
    logic [NUM_VC-1:0] _2n;
    logic [NUM_VC-1:0] _2peg;
    logic [NUM_VC-1:0] _2llc;

    // If the chip_id.y does not match the router’s rtr_location.chip_id.y, the router first routes south to the correct Mnemo. 
    assign off_chip_2s = (d_noc_in_tgtid.chip_id.y != rtr_location.chip_id.y);

    assign _2peg       = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.z == '1)? ((d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord)) : '0);
    assign _2llc       = off_chip_2s? '0 : ((d_noc_in_tgtid.chip_id.z == rtr_location.chip_id.z) && (d_noc_in_tgtid.xcoord == rtr_location.xcoord) && (d_noc_in_tgtid.ycoord == rtr_location.ycoord));
    
    for (genvar vc = 0; vc < (mnm_pkg::MNM_DNOC_R_NUM_VC + mnm_pkg::MNM_DNOC_AWW_NUM_VC) ; vc ++ ) begin

      assign is_x_first[vc] = !is_y_first[vc];

      assign _2e[vc]     = off_chip_2s? '0   : (is_x_first[vc]? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) : 
                           (is_y_first[vc]?   ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord > rtr_location.xcoord) :  '0 ) : '0));

      assign _2w[vc]     = off_chip_2s? '0   : (is_x_first[vc]? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) : 
                           (is_y_first[vc]?   ((d_noc_in_tgtid.ycoord == rtr_location.ycoord)? (d_noc_in_tgtid.xcoord < rtr_location.xcoord) :  '0 ) : '0));

      assign _2s[vc]     = off_chip_2s? '1   : (is_y_first[vc]? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) : 
                           (is_x_first[vc]?   ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord > rtr_location.ycoord) :  '0 ) : '0));

      assign _2n[vc]     = off_chip_2s? '0   : (is_y_first[vc]? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) : 
                           (is_x_first[vc]?   ((d_noc_in_tgtid.xcoord == rtr_location.xcoord)? (d_noc_in_tgtid.ycoord < rtr_location.ycoord) :  '0 ) : '0));

    if (vc < mnm_pkg::MNM_DNOC_R_NUM_VC)  begin: r_checker
    
      if ((d_noc_out_lane == north0) || (d_noc_out_lane == north1))      begin: r_2n_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2n (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2n[vc]),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if ((d_noc_out_lane == east0) || (d_noc_out_lane == east1))   begin: r_2e_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2e (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2e[vc]),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if ((d_noc_out_lane == south0) || (d_noc_out_lane == south1)) begin: r_2s_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2s (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2s[vc]),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if ((d_noc_out_lane == west0) || (d_noc_out_lane == west1))   begin: r_2w_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2w (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2w[vc]),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if ((d_noc_out_lane == llc0) || (d_noc_out_lane == llc1))     begin: r_2llc_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2llc (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2llc),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if (d_noc_out_lane == peg)                                    begin: r_2peg_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_r_2peg (

          .data_in    (d_noc_in.payload.daxi_r.data[0]),
          .in_valid   (d_noc_in_rvalid  && d_noc_in_vc == vc && _2peg),

          .data_out   (d_noc_out.payload.daxi_r.data[0]),
          .out_valid  (d_noc_out_rvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end
    
    end
      
    else begin: aww_checker
      if ((d_noc_out_lane == north0) || (d_noc_out_lane == north1))      begin: aww_2n_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2n (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2n[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end

      else if ((d_noc_out_lane == east0) || (d_noc_out_lane == east1))   begin: aww_2e_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2e (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2e[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end  

      else if ((d_noc_out_lane == south0) || (d_noc_out_lane == south1)) begin: aww_2s_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2s (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2s[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end 

      else if ((d_noc_out_lane == west0) || (d_noc_out_lane == west1))   begin: aww_2w_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2w (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2w[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end 

      else if ((d_noc_out_lane == llc0) || (d_noc_out_lane == llc1))     begin: aww_2llc_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2llc (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2llc[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

          .clk        (clk),
          .reset_n    (reset_n)
        );
      end 

      else if (d_noc_out_lane == peg)                                    begin: aww_2peg_checker
        transaction_tracker_sva # (
          .DATA_WIDTH(1),
          .CHECKER_DEPTH(64)
        ) transaction_tracker_sva_aww_2peg (

          .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
          .in_valid   (d_noc_in_awvalid  && d_noc_in_vc == vc && _2peg[vc]),

          .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
          .out_valid  (d_noc_out_awvalid && d_noc_out_vc == vc && d_noc_out_iid == d_noc_in_lane),

        .clk        (clk),
        .reset_n    (reset_n)
        );
      end 
    end
  end

endmodule