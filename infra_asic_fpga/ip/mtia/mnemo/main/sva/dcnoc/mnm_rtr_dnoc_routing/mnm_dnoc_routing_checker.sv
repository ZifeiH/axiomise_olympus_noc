/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_checker_sva.sv
//  This file contains irtr dnoc routing checks
/////////////////////////////////////////////////////////////////////////////////////////

module cip_rtr_dnoc_checker_sva # (

  parameter            DATA_WIDTH            = 1,
  parameter [5:0]      DIR_VALUE             = 0,
  parameter            IID                   = 0,
  parameter            DEST_NOC_ID           = 0,
  parameter            TGT_LANE              = 0,
  parameter            GEN_ADD_COVS          = 1,
  parameter            RTR_LOCATION_X_COORD  = 3,
  parameter            RTR_LOCATION_Y_COORD  = 4,
  parameter            RTR_LOCATION_CIP_ID   = 0,
  parameter            TYPE                  = "E2E"     
  
) (

  input   cip_pkg::data_noc_t           d_noc_in,
  input   logic                         d_noc_in_valid,
  
  input   cip_pkg::data_noc_t           d_noc_out,
  input   logic                         d_noc_out_valid,           

  input   logic                         clk,
  input   logic                         reset_n
    
);

    for (genvar vc = 0; vc < REQ_TOTAL_NUM_VC ; vc ++ ) begin
      transaction_tracker_sva # (
        .DATA_WIDTH(1),
        .CHECKER_DEPTH(64)
      ) cip_rtr_dnoc_aw_sva (
        .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
        .in_valid   (d_noc_in_valid && d_noc_in_vc == vc && dnoc_in_is_AW_W_channel && dnoc_tgt_dir_valid && (IS_X2L_INV2?d_noc_in_iid == IID:1)),
        .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
        .out_valid  (d_noc_out_valid && d_noc_out_vc == vc && dnoc_out_is_AW_channel && d_noc_out_iid == IID),
        .clk        (clk),
        .reset_n    (reset_n)
      );
    end

    for (genvar vc = 0; vc < REQ_TOTAL_NUM_VC ; vc ++ ) begin
      transaction_tracker_sva # (
        .DATA_WIDTH(1),
        .CHECKER_DEPTH(64)
      ) cip_rtr_dnoc_aw_sva (
        .data_in    (d_noc_in.payload.daxi_combo_aw_w.w.data[0]),
        .in_valid   (d_noc_in_valid && d_noc_in_vc == vc && dnoc_in_is_AW_W_channel && dnoc_tgt_dir_valid && (IS_X2L_INV2?d_noc_in_iid == IID:1)),
        .data_out   (d_noc_out.payload.daxi_combo_aw_w.w.data[0]),
        .out_valid  (d_noc_out_valid && d_noc_out_vc == vc && dnoc_out_is_AW_channel && d_noc_out_iid == IID),
        .clk        (clk),
        .reset_n    (reset_n)
      );
    end

endmodule
