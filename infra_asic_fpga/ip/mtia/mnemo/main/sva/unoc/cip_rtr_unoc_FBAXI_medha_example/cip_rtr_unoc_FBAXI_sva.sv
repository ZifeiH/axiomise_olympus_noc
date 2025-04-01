///////////////////////////////////////////////////
/// File: cip_rtr_unoc_FBAXI_sva.sv
/// This file contains the instantiations for constraints on inputs and credit release, and flow control
///////////////////////////////////////////////////

module cip_rtr_unoc_FBAXI_sva # (
  parameter RTR_GRID_COORD_Y_START = cip_pkg::CIP_RTR_GRID_COORD_Y_START,
            RTR_GRID_COORD_Y_END = cip_pkg::CIP_RTR_GRID_COORD_Y_END,
            RTR_GRID_COORD_X_START = cip_pkg::CIP_RTR_GRID_COORD_X_START,
            RTR_GRID_COORD_X_END = cip_pkg::CIP_RTR_GRID_COORD_X_END,
            STUB_FULL = 0,
            STUB_DCNOC = 0,
            STUB_CRTR = 0,
            STUB_IRTR = 0,
            CIP_RTR_DRIVE_0 = 0
) (
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_FROM_FI-1:0]                                                fi_crtr_dnoc_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_FROM_FI-1:0]                                                fi_crtr_cnoc_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_crtr_unoc_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_FROM_FI-1:0]                                                fi_crtr_dnoc,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_FROM_FI-1:0]                                                fi_crtr_cnoc,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_crtr_unoc,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_TO_FI-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]         crtr_fi_dnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_TO_FI-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]         crtr_fi_cnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_TO_FI-1:0][cip_pkg::CIP_CRTR_UNOC_TOTAL_NUM_VC-1:0]    crtr_fi_unoc_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_FROM_FI-1:0]                                                fi_irtr_dnoc_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_FROM_FI-1:0]                                                fi_irtr_cnoc_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_irtr_unoc_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_FROM_FI-1:0]                                                fi_irtr_dnoc,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_FROM_FI-1:0]                                                fi_irtr_cnoc,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_FROM_FI-1:0]                                           fi_irtr_unoc,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]         irtr_fi_dnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]         irtr_fi_cnoc_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_TO_FI-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]    irtr_fi_unoc_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_south_in_valid,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_south_in_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_east_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_east_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_west_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_west_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_north_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_north_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_south_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_south_in,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_south_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_south_in_valid,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_east_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_east_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_west_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_west_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_north_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_north_in,
  input   cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_south_in,
  input   cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_south_in,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_south_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_west_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_east_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_north_in_valid,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_south_in_valid,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_west_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_east_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_north_in,
  input   cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_south_in,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_west_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_east_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_north_out_credit_release,
  input   logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_south_out_credit_release,
  input   logic                                  [17:0]                                                                                                                crtr_dbg_rtr_gpio_sel_e,
  input   logic                                  [17:0]                                                                                                                crtr_dbg_rtr_gpio_sel_w,
  input   logic                                                                                                                                                        crtr_interrupt_redundant_n_in,
  input   logic                                                                                                                                                        crtr_interrupt_redundant_s_in,
  input   logic                                  [17:0]                                                                                                                irtr_dbg_rtr_gpio_sel_e,
  input   logic                                  [17:0]                                                                                                                irtr_dbg_rtr_gpio_sel_w,
  input   logic                                                                                                                                                        irtr_interrupt_redundant_n_in,
  input   logic                                                                                                                                                        irtr_interrupt_redundant_s_in,
  input   logic                                                                                                                                                        clk,
  input   logic                                                                                                                                                        crtr_soc_reset_n,
  input   logic                                                                                                                                                        irtr_soc_reset_n,
  input   logic                                                                                                                                                        soc_unoc_reset_n,
  input   cip_pkg::cip_grid_location_t                                                                                                                                 rtr_location,
  input   logic                                                                                                                                                        TEST__ASYNC_DISABLE,
  input   logic                                                                                                                                                        TEST__SPARE,
  input   logic                                                                                                                                                        test_mode,
  input   logic                                                                                                                                                        CORE_MEM_RST,
  input   cip_pe_pkg::pe_sync_update_t                                                                                                                                 crtr_FT_pe_pe_sync_update_west_in,
  input   logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_in_valid,
  input   logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_out_credit_release,
  input   logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_out_rx_ready,
  input   cip_pe_pkg::pe_sync_update_t                                                                                                                                 irtr_FT_pe_pe_sync_update_east_in,
  input   logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_in_valid,
  input   logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_out_credit_release,
  input   logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_out_rx_ready,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_TO_FI-1:0]                                                  crtr_fi_dnoc_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_TO_FI-1:0]                                                  crtr_fi_cnoc_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_TO_FI-1:0]                                             crtr_fi_unoc_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_TO_FI-1:0]                                                  crtr_fi_dnoc,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_TO_FI-1:0]                                                  crtr_fi_cnoc,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_TO_FI-1:0]                                             crtr_fi_unoc,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_DNOC_FROM_FI-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]       fi_crtr_dnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI-1:0][cip_pkg::CIP_CRTR_NUM_CNOC_FROM_FI-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]       fi_crtr_cnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_CRTR_NUM_UNOC_FROM_FI-1:0][cip_pkg::CIP_CRTR_UNOC_TOTAL_NUM_VC-1:0]  fi_crtr_unoc_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_TO_FI-1:0]                                                  irtr_fi_dnoc_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_TO_FI-1:0]                                                  irtr_fi_cnoc_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_TO_FI-1:0]                                             irtr_fi_unoc_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_TO_FI-1:0]                                                  irtr_fi_dnoc,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_TO_FI-1:0]                                                  irtr_fi_cnoc,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_TO_FI-1:0]                                             irtr_fi_unoc,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_DNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]       fi_irtr_dnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI-1:0][cip_pkg::CIP_IRTR_NUM_CNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]       fi_irtr_cnoc_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_FI_UNOC-1:0][cip_pkg::CIP_IRTR_NUM_UNOC_FROM_FI-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]  fi_irtr_unoc_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_south_out_valid,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_south_out_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_east_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_east_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0]                                                                                   crtr_d_noc_west_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0]                                                                                   crtr_c_noc_west_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_north_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_north_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0]                                                                                   crtr_d_noc_south_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0]                                                                                   crtr_c_noc_south_out,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]                                          crtr_d_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_CRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC-1:0]                                          crtr_c_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_south_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_south_out_valid,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_east_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_east_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0]                                                                                   irtr_d_noc_west_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0]                                                                                   irtr_c_noc_west_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_north_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_north_out,
  input  cip_pkg::data_noc_t                    [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0]                                                                                   irtr_d_noc_south_out,
  input  cip_pkg::control_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0]                                                                                   irtr_c_noc_south_out,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_DNOC-1:0][cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC-1:0]                                          irtr_d_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_CNOC-1:0][cip_pkg::CIP_IRTR_CNOC_TOTAL_NUM_VC-1:0]                                          irtr_c_noc_south_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_west_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_east_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_north_out_valid,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_south_out_valid,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_west_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0]                                                                                   irtr_u_noc_east_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_north_out,
  input  cip_pkg::utility_noc_t                 [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0]                                                                                   irtr_u_noc_south_out,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_west_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_EW_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_east_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_north_in_credit_release,
  input  logic                                  [cip_pkg::CIP_IRTR_NUM_NS_UNOC-1:0][cip_pkg::CIP_IRTR_UNOC_TOTAL_NUM_VC-1:0]                                          irtr_u_noc_south_in_credit_release,
  input  cip_rtr_pkg::cip_crtr_dbg_filter_t                                                                                                                           crtr_dbg_filter_e,
  input  cip_rtr_pkg::cip_crtr_dbg_trace_t                                                                                                                            crtr_dbg_trace_e,
  input  logic                                  [2:0]                                                                                                                 crtr_interrupt_e,
  input  cip_rtr_pkg::cip_crtr_dbg_filter_t                                                                                                                           crtr_dbg_filter_w,
  input  cip_rtr_pkg::cip_crtr_dbg_trace_t                                                                                                                            crtr_dbg_trace_w,
  input  logic                                  [2:0]                                                                                                                 crtr_interrupt_w,
  input  logic                                                                                                                                                        crtr_interrupt_redundant_n_out,
  input  logic                                                                                                                                                        crtr_interrupt_redundant_s_out,
  input  cip_rtr_pkg::cip_irtr_dbg_filter_t                                                                                                                           irtr_dbg_filter_e,
  input  cip_rtr_pkg::cip_irtr_dbg_trace_t                                                                                                                            irtr_dbg_trace_e,
  input  logic                                  [2:0]                                                                                                                 irtr_interrupt_e,
  input  cip_rtr_pkg::cip_irtr_dbg_filter_t                                                                                                                           irtr_dbg_filter_w,
  input  cip_rtr_pkg::cip_irtr_dbg_trace_t                                                                                                                            irtr_dbg_trace_w,
  input  logic                                  [2:0]                                                                                                                 irtr_interrupt_w,
  input  logic                                                                                                                                                        irtr_disabled_pe_e,
  input  logic                                                                                                                                                        irtr_disabled_pe_w,
  input  logic                                                                                                                                                        irtr_interrupt_redundant_n_out,
  input  logic                                                                                                                                                        irtr_interrupt_redundant_s_out,
  input  cip_pe_pkg::pe_sync_update_t                                                                                                                                 crtr_FT_pe_pe_sync_update_west_out,
  input  logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_out_valid,
  input  logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_in_credit_release,
  input  logic                                                                                                                                                        crtr_FT_pe_pe_sync_update_west_in_rx_ready,
  input  cip_pe_pkg::pe_sync_update_t                                                                                                                                 irtr_FT_pe_pe_sync_update_east_out,
  input  logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_out_valid,
  input  logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_in_credit_release,
  input  logic                                                                                                                                                        irtr_FT_pe_pe_sync_update_east_in_rx_ready

); 


  // Default Clocking and Reset scheme
  default clocking @(posedge clk);
  endclocking
  default disable iff (!soc_unoc_reset_n);

  `define ck @(posedge clk) disable iff (!soc_unoc_reset_n )

  // `include "fbaxi_unoc_configs.sv"


  logic reset_n;
  assign reset_n = soc_unoc_reset_n;


// Rate Control Flow 

    localparam FLOW_CONTROL_EAST    = 1;
    localparam FLOW_CONTROL_WEST    = 1;
    localparam FLOW_CONTROL_NORTH   = 1;
    localparam FLOW_CONTROL_SOUTH   = 1;
    localparam FLOW_CONTROL_LEAF0   = 1;
    localparam FLOW_CONTROL_LEAF1   = 1;


        generate if (FLOW_CONTROL_EAST) begin : flow_control_east
            flow_control # (max_reqs_east        
            ) unoc_flow_control_east (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_u_noc_east_in_valid[0])
            ); 
        end
        endgenerate

        generate if (FLOW_CONTROL_WEST) begin : flow_control_west        
            flow_control # (max_reqs_west        
            ) unoc_flow_control_west (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_u_noc_west_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_NORTH) begin : flow_control_north    
            flow_control # (max_reqs_north        
            ) unoc_flow_control_north (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_u_noc_north_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_SOUTH) begin : flow_control_south
            flow_control # (max_reqs_south        
            ) unoc_flow_control_south (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_u_noc_south_in_valid[0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_LEAF0) begin : flow_control_leaf0
            flow_control # (max_reqs_leaf0        
            ) unoc_flow_control_leaf0 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_crtr_unoc_valid[0][0])
            );
        end
        endgenerate

        generate if (FLOW_CONTROL_LEAF1) begin : flow_control_leaf1
            flow_control # (max_reqs_leaf1       
            ) unoc_flow_control_leaf1 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_irtr_unoc_valid[0][0])
            );
        end
        endgenerate



  cip_rtr_unoc_credit_release_sva #(
      .SIDE(NORTH),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_north_credit_release_sva (
      .u_noc_in(irtr_u_noc_north_in[0]),
      .u_noc_in_credit_release(irtr_u_noc_north_in_credit_release[0]),
      .u_noc_in_valid(irtr_u_noc_north_in_valid[0]),

      .u_noc_out(irtr_u_noc_north_out[0]),
      .u_noc_out_credit_release(irtr_u_noc_north_out_credit_release[0]),
      .u_noc_out_valid(irtr_u_noc_north_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_credit_release_sva #(
      .SIDE(SOUTH),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_south_credit_release_sva (
      .u_noc_in(irtr_u_noc_south_in[0]),
      .u_noc_in_credit_release(irtr_u_noc_south_in_credit_release[0]),
      .u_noc_in_valid(irtr_u_noc_south_in_valid[0]),

      .u_noc_out(irtr_u_noc_south_out[0]),
      .u_noc_out_credit_release(irtr_u_noc_south_out_credit_release[0]),
      .u_noc_out_valid(irtr_u_noc_south_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_credit_release_sva #(
      .SIDE(EAST),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_east_credit_release_sva (
      .u_noc_in(irtr_u_noc_east_in[0]),
      .u_noc_in_credit_release(irtr_u_noc_east_in_credit_release[0]),
      .u_noc_in_valid(irtr_u_noc_east_in_valid[0]),

      .u_noc_out(irtr_u_noc_east_out[0]),
      .u_noc_out_credit_release(irtr_u_noc_east_out_credit_release[0]),
      .u_noc_out_valid(irtr_u_noc_east_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_credit_release_sva #(
      .SIDE(WEST),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_west_credit_release_sva (
      .u_noc_in(irtr_u_noc_west_in[0]),
      .u_noc_in_credit_release(irtr_u_noc_west_in_credit_release[0]),
      .u_noc_in_valid(irtr_u_noc_west_in_valid[0]),

      .u_noc_out(irtr_u_noc_west_out[0]),
      .u_noc_out_credit_release(irtr_u_noc_west_out_credit_release[0]),
      .u_noc_out_valid(irtr_u_noc_west_out_valid[0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_credit_release_sva #(
      .SIDE(LEAF0),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_leaf0_credit_release_sva (
      .u_noc_in(fi_crtr_unoc[0][0]),
      .u_noc_in_credit_release(fi_crtr_unoc_credit_release[0][0]),
      .u_noc_in_valid(fi_crtr_unoc_valid[0][0]),

      .u_noc_out(crtr_fi_unoc[0][0]),
      .u_noc_out_credit_release(crtr_fi_unoc_credit_release[0][0]),
      .u_noc_out_valid(crtr_fi_unoc_valid[0][0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_credit_release_sva #(
      .SIDE(LEAF1),
      .RTR_MINI_REQUESTER_NUM_VC(cip_pkg::CIP_UNOC_TOTAL_NUM_VC)
  ) cip_rtr_unoc_leaf1_credit_release_sva (
      .u_noc_in(fi_irtr_unoc[0][0]),
      .u_noc_in_credit_release(fi_irtr_unoc_credit_release[0][0]),
      .u_noc_in_valid(fi_irtr_unoc_valid[0][0]),

      .u_noc_out(irtr_fi_unoc[0][0]),
      .u_noc_out_credit_release(irtr_fi_unoc_credit_release[0][0]),
      .u_noc_out_valid(irtr_fi_unoc_valid[0][0]),

      .clk(clk),
      .reset_n(reset_n)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(NORTH)
  ) u_noc_north_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(irtr_u_noc_north_in[0]),
    .u_noc_in_valid(irtr_u_noc_north_in_valid[0]),
    .u_noc_out(irtr_u_noc_north_out[0]),
    .u_noc_out_valid(irtr_u_noc_north_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(SOUTH)
  ) u_noc_south_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(irtr_u_noc_south_in[0]),
    .u_noc_in_valid(irtr_u_noc_south_in_valid[0]),
    .u_noc_out(irtr_u_noc_south_out[0]),
    .u_noc_out_valid(irtr_u_noc_south_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(EAST)
  ) u_noc_east_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(irtr_u_noc_east_in[0]),
    .u_noc_in_valid(irtr_u_noc_east_in_valid[0]),
    .u_noc_out(irtr_u_noc_east_out[0]),
    .u_noc_out_valid(irtr_u_noc_east_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(WEST)
  ) u_noc_west_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(irtr_u_noc_west_in[0]),
    .u_noc_in_valid(irtr_u_noc_west_in_valid[0]),
    .u_noc_out(irtr_u_noc_west_out[0]),
    .u_noc_out_valid(irtr_u_noc_west_out_valid[0]),
    .rtr_location(rtr_location)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(LEAF0)
    ) u_noc_leaf0_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(fi_crtr_unoc[0][0]),
    .u_noc_in_valid(fi_crtr_unoc_valid[0][0]),
    .u_noc_out(crtr_fi_unoc[0][0]),
    .u_noc_out_valid(crtr_fi_unoc_valid[0][0]),
    .rtr_location(rtr_location)
  );

  cip_rtr_unoc_fbaxi_constraints #(
    .SIDE(LEAF1)
    ) u_noc_leaf1_constraints (
    .clk(clk),
    .reset_n(reset_n),
    .u_noc_in(fi_irtr_unoc[0][0]),
    .u_noc_in_valid(fi_irtr_unoc_valid[0][0]),
    .u_noc_out(irtr_fi_unoc[0][0]),
    .u_noc_out_valid(irtr_fi_unoc_valid[0][0]),
    .rtr_location(rtr_location)
  );


/////////////////////////////////////////////
/// End
/////////////////////////////////////////////

/////////////////////////////////////////////
/// General assumptions
/////////////////////////////////////////////

  localparam  CIP_ID        = 0;
  localparam  CIP_RTR_XCOOD = 3;
  localparam  CIP_RTR_YCOOD = 4;

  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_cip_id_legal ,    rtr_location.cip_id == CIP_ID);  
  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_x_coord_legal,    rtr_location.xcoord == CIP_RTR_XCOOD);
  `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_y_coord_legal,    rtr_location.ycoord == CIP_RTR_YCOOD); // not including y=10 here\

  `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__ASYNC_DISABLE_0_stable,  TEST__ASYNC_DISABLE == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__SPARE_0_stable,          TEST__SPARE == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_test_mode_0_stable,            test_mode == 0 );
  `SV_ASSERT  ( FVPH_RTR_FV_am_CORE_MEM_RST_0_stable,         CORE_MEM_RST == 0 );

  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_CFG_DISABLED_PE0_stable,       ##1 $stable(`CIP_IRTR_CFG_DISABLED_PE0) );  
  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_CFG_DISABLED_PE1_stable,       ##1 $stable(`CIP_IRTR_CFG_DISABLED_PE1) );
  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_CRTR_CFG_DISABLED_PE0_stable,       ##1 $stable(`CIP_CRTR_CFG_DISABLED_PE0) );  
  `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_CRTR_CFG_DISABLED_PE1_stable,       ##1 $stable(`CIP_CRTR_CFG_DISABLED_PE1) );

endmodule