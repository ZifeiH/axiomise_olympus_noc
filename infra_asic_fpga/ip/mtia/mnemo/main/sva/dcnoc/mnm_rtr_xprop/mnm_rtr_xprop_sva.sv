module mnm_rtr_xprop_sva # (
  parameter NUM_LANES = 11,
            NUM_VC = 11,
            VCID_W = 5,
            RX_DEPTH_W = 7,
            NUM_SHRD_CRD_GROUPS = 3,
            NUM_RSVD_CRD_GROUPS = 3,
            RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS),
            SEQN_W = 4,
            STUB = 0,
            REMOVE_LANE = {NUM_LANES{1'b0}}) 
(
  input logic                                                                                CORE_MEM_RST,
  input logic                                                                                clk,
  input rtr_dc_csr_pkg::registers_for_default_struct                                         csr_in,
  input rtr_dc_csr_pkg::registers_for_default_inputs_struct                                  csr_out,
  input logic                                                                                init_done,
  input mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_in,
  input logic                                                   [NUM_LANES-1:0]              noc_in_async_crd_release,
  input logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_in_credit_release_id,
  input logic                                                   [NUM_LANES-1:0]              noc_in_credit_release_valid,
  input logic                                                   [NUM_LANES-1:0]              noc_in_valid,
  input mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_out,
  input logic                                                   [NUM_LANES-1:0]              noc_out_async_crd_release,
  input logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_out_credit_release_id,
  input logic                                                   [NUM_LANES-1:0]              noc_out_credit_release_valid,
  input logic                                                   [NUM_LANES-1:0]              noc_out_valid,
  input mnm_pkg::mnm_grid_location_t                                                         rtr_location,
  input logic                                                   [NUM_LANES-1:0]              rx_wr_clk_in,
  input logic                                                   [NUM_LANES-1:0]              rx_wr_reset_n_in,
  input logic                                                                                soc_reset_n

);

  wire reset_n;
  assign reset_n = soc_reset_n;


  `SV_ASSERT (FVPH_as_not_unknow_csr_out, !$isunknown(csr_out));
  `SV_ASSERT (FVPH_as_not_unknow_init_done, !$isunknown(init_done));
  `SV_ASSERT (FVPH_as_not_unknow_noc_in_credit_release_id, !$isunknown(noc_in_credit_release_id));
  `SV_ASSERT (FVPH_as_not_unknow_noc_in_credit_release_valid, !$isunknown(noc_in_credit_release_valid));
  `SV_ASSERT (FVPH_as_not_unknow_noc_out, !$isunknown(noc_out));
  `SV_ASSERT (FVPH_as_not_unknow_noc_out_valid, !$isunknown(noc_out_valid));

  
endmodule