///////////////////////////////////////////////////
/// File: cip_mrtr_unoc_FBAXI_sva.sv
/// This file contains the instantiations for constraints on inputs and credit release, and flow control
///////////////////////////////////////////////////

module cip_mrtr_unoc_fbaxi_sva # (
  parameter RTR_GRID_COORD_Y_START = cip_pkg::CIP_RTR_GRID_COORD_Y_START,
            RTR_GRID_COORD_Y_END = cip_pkg::CIP_RTR_GRID_COORD_Y_END,
            RTR_GRID_COORD_X_START = cip_pkg::CIP_RTR_GRID_COORD_X_START,
            RTR_GRID_COORD_X_END = cip_pkg::CIP_RTR_GRID_COORD_X_END,
            STUB_FULL = 0,
            STUB_DCNOC = 0,
            STUB_MRTR = 0,
            RTR_TYPE = 2
) (
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_FROM_FI-1:0]                                           fi_mrtr_dnoc_valid,
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_FROM_FI-1:0]                                           fi_mrtr_cnoc_valid,
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_mrtr_unoc_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_FROM_FI-1:0]                                           fi_mrtr_dnoc,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_FROM_FI-1:0]                                           fi_mrtr_cnoc,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_mrtr_unoc,
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]    mrtr_fi_dnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]    mrtr_fi_cnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]    mrtr_fi_unoc_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_south_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_south_in_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_east_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_east_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_west_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_west_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_north_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_north_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_south_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_south_in,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_south_in_valid,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_west_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_east_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_north_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_south_in,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_south_out_credit_release,
  input   logic                                  [17:0]                                                                                                                 mrtr_dbg_rtr_gpio_sel_e,
  input   logic                                  [17:0]                                                                                                                 mrtr_dbg_rtr_gpio_sel_w,
  input   logic                                                                                                                                                         mrtr_interrupt_redundant_n_in,
  input   logic                                                                                                                                                         mrtr_interrupt_redundant_s_in,
  input   logic                                                                                                                                                         clk,
  input   logic                                                                                                                                                         irtr_soc_reset_n,
  input   logic                                                                                                                                                         soc_unoc_reset_n,
  input   cip_pkg::cip_grid_location_t                                                                                                                                  rtr_location,
  input   logic                                                                                                                                                         TEST__ASYNC_DISABLE,
  input   logic                                                                                                                                                         TEST__SPARE,
  input   logic                                                                                                                                                         test_mode,
  input   logic                                                                                                                                                         CORE_MEM_RST,
  input   cip_pe_pkg::pe_sync_update_t           [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_in,
  input   cip_pe_pkg::pe_sync_update_t           [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_in,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_in_valid,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_in_valid,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_out_rx_ready,
  input   logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_out_rx_ready,

  // outputs on RTL module (flipped to inputs for this TB)
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_TO_FI-1:0]                                             mrtr_fi_dnoc_valid,
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_TO_FI-1:0]                                             mrtr_fi_cnoc_valid,
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_TO_FI-1:0]                                             mrtr_fi_unoc_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_TO_FI-1:0]                                             mrtr_fi_dnoc,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_TO_FI-1:0]                                             mrtr_fi_cnoc,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_TO_FI-1:0]                                             mrtr_fi_unoc,
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_DNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]  fi_mrtr_dnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_CNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]  fi_mrtr_cnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_ME_IRTR_NUM_FI-1:0][cip_pkg::CIP_ME_IRTR_NUM_UNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]  fi_mrtr_unoc_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_south_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_south_out_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_east_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_east_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                    mrtr_d_noc_west_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                    mrtr_c_noc_west_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_north_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_north_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                    mrtr_d_noc_south_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                    mrtr_c_noc_south_out,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                           mrtr_d_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                           mrtr_c_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_south_out_valid,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_west_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                    mrtr_u_noc_east_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_north_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                    mrtr_u_noc_south_out,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                           mrtr_u_noc_south_in_credit_release,
  input  cip_rtr_pkg::cip_irtr_dbg_filter_t                                                                                                                            mrtr_dbg_filter_e,
  input  cip_rtr_pkg::cip_irtr_dbg_trace_t                                                                                                                             mrtr_dbg_trace_e,
  input  logic                                  [2:0]                                                                                                                  mrtr_interrupt_e,
  input  cip_rtr_pkg::cip_irtr_dbg_filter_t                                                                                                                            mrtr_dbg_filter_w,
  input  cip_rtr_pkg::cip_irtr_dbg_trace_t                                                                                                                             mrtr_dbg_trace_w,
  input  logic                                  [2:0]                                                                                                                  mrtr_interrupt_w,
  input  logic                                                                                                                                                         mrtr_disabled_pe_e,
  input  logic                                                                                                                                                         mrtr_disabled_pe_w,
  input  logic                                                                                                                                                         mrtr_interrupt_redundant_n_out,
  input  logic                                                                                                                                                         mrtr_interrupt_redundant_s_out,
  input  cip_pe_pkg::pe_sync_update_t           [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_out,
  input  cip_pe_pkg::pe_sync_update_t           [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_out,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_out_valid,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_out_valid,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_east_in_rx_ready,
  input  logic                                  [cip_pkg::CIP_PE_TOP_NUM_PE_Y-1:0]                                                                                     FT_pe_pe_sync_update_west_in_rx_ready

); 


  // Default Clocking and Reset scheme
  default clocking @(posedge clk);
  endclocking
  default disable iff (!soc_unoc_reset_n);


  logic reset_n;
  assign reset_n = soc_unoc_reset_n;


// -------------------------- Flow Control Constraints Instantiations ------------------------- 

    localparam FLOW_CONTROL_EAST    = 1;
    localparam FLOW_CONTROL_WEST    = 1;
    localparam FLOW_CONTROL_NORTH   = 1;
    localparam FLOW_CONTROL_SOUTH   = 1;
    localparam FLOW_CONTROL_LEAF0   = 1;
    localparam FLOW_CONTROL_LEAF1   = 1;

    localparam  CIP_ID              = 0;
    localparam  CIP_MRTR_XCOOD      = 3;
    localparam  CIP_MRTR_YCOOD      = 10;

        generate if (FLOW_CONTROL_EAST) begin : flow_control_east
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(EAST),
              .MAX_ALLOWED_REQS(max_reqs_east)        
            ) unoc_flow_control_east (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (mrtr_u_noc_east_in_valid[0])
            ); 
        end
        endgenerate

        generate if (FLOW_CONTROL_WEST) begin : flow_control_west        
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(WEST),
              .MAX_ALLOWED_REQS(max_reqs_west)        
            ) unoc_flow_control_west (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (mrtr_u_noc_west_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_NORTH) begin : flow_control_north    
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(NORTH),
              .MAX_ALLOWED_REQS(max_reqs_north)        
            ) unoc_flow_control_north (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (mrtr_u_noc_north_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_SOUTH) begin : flow_control_south
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(SOUTH),
              .MAX_ALLOWED_REQS(max_reqs_south)         
            ) unoc_flow_control_south (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (mrtr_u_noc_south_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_LEAF0) begin : flow_control_leaf0
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(LEAF0),
              .MAX_ALLOWED_REQS(max_reqs_leaf0)        
            ) unoc_flow_control_leaf0 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_mrtr_unoc_valid[0][0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_LEAF1) begin : flow_control_leaf1
            flow_control # (
              .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
              .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
              .RTR_LOCATION_CIP_ID(CIP_ID),
              .SIDE(LEAF1),
              .MAX_ALLOWED_REQS(max_reqs_leaf1)       
            ) unoc_flow_control_leaf1 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_mrtr_unoc_valid[1][0])
            );
        end
        endgenerate

  // -------------------------- Credit Release Constraints Instantiations -------------------------

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(NORTH),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_north_credit_release_sva (
      .u_noc_in(mrtr_u_noc_north_in[0]),
      .u_noc_in_credit_release(mrtr_u_noc_north_in_credit_release[0]),
      .u_noc_in_valid(mrtr_u_noc_north_in_valid[0]),

      .u_noc_out(mrtr_u_noc_north_out[0]),
      .u_noc_out_credit_release(mrtr_u_noc_north_out_credit_release[0]),
      .u_noc_out_valid(mrtr_u_noc_north_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(SOUTH),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_south_credit_release_sva (
      .u_noc_in(mrtr_u_noc_south_in[0]),
      .u_noc_in_credit_release(mrtr_u_noc_south_in_credit_release[0]),
      .u_noc_in_valid(mrtr_u_noc_south_in_valid[0]),

      .u_noc_out(mrtr_u_noc_south_out[0]),
      .u_noc_out_credit_release(mrtr_u_noc_south_out_credit_release[0]),
      .u_noc_out_valid(mrtr_u_noc_south_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(EAST),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_east_credit_release_sva (
      .u_noc_in(mrtr_u_noc_east_in[0]),
      .u_noc_in_credit_release(mrtr_u_noc_east_in_credit_release[0]),
      .u_noc_in_valid(mrtr_u_noc_east_in_valid[0]),

      .u_noc_out(mrtr_u_noc_east_out[0]),
      .u_noc_out_credit_release(mrtr_u_noc_east_out_credit_release[0]),
      .u_noc_out_valid(mrtr_u_noc_east_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(WEST),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_west_credit_release_sva (
      .u_noc_in(mrtr_u_noc_west_in[0]),
      .u_noc_in_credit_release(mrtr_u_noc_west_in_credit_release[0]),
      .u_noc_in_valid(mrtr_u_noc_west_in_valid[0]),

      .u_noc_out(mrtr_u_noc_west_out[0]),
      .u_noc_out_credit_release(mrtr_u_noc_west_out_credit_release[0]),
      .u_noc_out_valid(mrtr_u_noc_west_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(LEAF0),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_leaf0_credit_release_sva (
      .u_noc_in(fi_mrtr_unoc[0][0]),
      .u_noc_in_credit_release(fi_mrtr_unoc_credit_release[0][0]),
      .u_noc_in_valid(fi_mrtr_unoc_valid[0][0]),

      .u_noc_out(mrtr_fi_unoc[0][0]),
      .u_noc_out_credit_release(mrtr_fi_unoc_credit_release[0][0]),
      .u_noc_out_valid(mrtr_fi_unoc_valid[0][0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_mrtr_unoc_credit_release_sva #(
      .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
      .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
      .RTR_LOCATION_CIP_ID(CIP_ID),
      .SIDE(LEAF1),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_mrtr_unoc_leaf1_credit_release_sva (
      .u_noc_in(fi_mrtr_unoc[1][0]),
      .u_noc_in_credit_release(fi_mrtr_unoc_credit_release[1][0]),
      .u_noc_in_valid(fi_mrtr_unoc_valid[1][0]),

      .u_noc_out(mrtr_fi_unoc[1][0]),
      .u_noc_out_credit_release(mrtr_fi_unoc_credit_release[1][0]),
      .u_noc_out_valid(mrtr_fi_unoc_valid[1][0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  // -------------------------- FBAXI Input Constraints Instantiations -------------------------

  cip_mrtr_unoc_fbaxi_constraints #(
    .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
    .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
    .RTR_LOCATION_CIP_ID(CIP_ID),
    .SIDE                 (NORTH)
  ) cip_mrtr_unoc_north_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(mrtr_u_noc_north_in[0]),
    .u_noc_in_valid(mrtr_u_noc_north_in_valid[0]),
    .u_noc_out(mrtr_u_noc_north_out[0]),
    .u_noc_out_valid(mrtr_u_noc_north_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_mrtr_unoc_fbaxi_constraints #(
    .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
    .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
    .RTR_LOCATION_CIP_ID(CIP_ID),
    .SIDE(SOUTH)
  ) cip_mrtr_unoc_south_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(mrtr_u_noc_south_in[0]),
    .u_noc_in_valid(mrtr_u_noc_south_in_valid[0]),
    .u_noc_out(mrtr_u_noc_south_out[0]),
    .u_noc_out_valid(mrtr_u_noc_south_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_mrtr_unoc_fbaxi_constraints #(
    .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
    .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
    .RTR_LOCATION_CIP_ID(CIP_ID),
    .SIDE(EAST)
  ) cip_mrtr_unoc_east_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(mrtr_u_noc_east_in[0]),
    .u_noc_in_valid(mrtr_u_noc_east_in_valid[0]),
    .u_noc_out(mrtr_u_noc_east_out[0]),
    .u_noc_out_valid(mrtr_u_noc_east_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_mrtr_unoc_fbaxi_constraints #(
    .SIDE(WEST)
  ) cip_mrtr_unoc_west_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(mrtr_u_noc_west_in[0]),
    .u_noc_in_valid(mrtr_u_noc_west_in_valid[0]),
    .u_noc_out(mrtr_u_noc_west_out[0]),
    .u_noc_out_valid(mrtr_u_noc_west_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_mrtr_unoc_fbaxi_constraints #(
    .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
    .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
    .RTR_LOCATION_CIP_ID(CIP_ID),
    .SIDE(LEAF0)
    ) cip_mrtr_unoc_leaf0_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(fi_mrtr_unoc[0][0]),
    .u_noc_in_valid(fi_mrtr_unoc_valid[0][0]),
    .u_noc_out(mrtr_fi_unoc[0][0]),
    .u_noc_out_valid(mrtr_fi_unoc_valid[0][0]),
    .rtr_location(rtr_location)
  );

  cip_mrtr_unoc_fbaxi_constraints #(
    .RTR_LOCATION_X_COORD(CIP_MRTR_XCOOD),
    .RTR_LOCATION_Y_COORD(CIP_MRTR_YCOOD),
    .RTR_LOCATION_CIP_ID(CIP_ID),
    .SIDE(LEAF1)
    ) cip_mrtr_unoc_leaf1_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(fi_mrtr_unoc[1][0]),
    .u_noc_in_valid(fi_mrtr_unoc_valid[1][0]),
    .u_noc_out(mrtr_fi_unoc[1][0]),
    .u_noc_out_valid(mrtr_fi_unoc_valid[1][0]),
    .rtr_location(rtr_location)
  );


/////////////////////////////////////////////
/// General assumptions
/////////////////////////////////////////////

  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_cip_id_legal ,    rtr_location.cip_id == CIP_ID);  
  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_x_coord_legal,    rtr_location.xcoord == CIP_MRTR_XCOOD);
  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_y_coord_legal,    rtr_location.ycoord == CIP_MRTR_YCOOD); // not including y=10 here\

  `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__ASYNC_DISABLE_0_stable,  TEST__ASYNC_DISABLE == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__SPARE_0_stable,          TEST__SPARE == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_test_mode_0_stable,            test_mode == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_CORE_MEM_RST_0_stable,         CORE_MEM_RST == 0 );

  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_MRTR_CFG_DISABLED_PE0_stable,       ##1 $stable(`CIP_MRTR_CFG_DISABLED_PE0) );  
  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_MRTR_CFG_DISABLED_PE1_stable,       ##1 $stable(`CIP_MRTR_CFG_DISABLED_PE1) );


endmodule
