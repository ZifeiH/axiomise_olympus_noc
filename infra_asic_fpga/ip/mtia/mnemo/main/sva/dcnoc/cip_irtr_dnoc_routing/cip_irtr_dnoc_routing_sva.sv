/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_routing_sva.sv
//  This file contains irtr dnoc routing sva
/////////////////////////////////////////////////////////////////////////////////////////
module cip_irtr_dnoc_routing_sva # (
  parameter STUB_FULL = 0,
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

  logic   reset_n;
  assign  reset_n = soc_unoc_reset_n;

//------------------------------------------------------------------------------
//-- Router location  --
//------------------------------------------------------------------------------

    localparam  rtr_location_x_coord          = 3;
    localparam  rtr_location_y_coord          = 4;
    localparam  rtr_location_cip_id           = 0;

    localparam  IO_SHIFT_RULE                 = ((rtr_location_y_coord-CIP_RTR_GRID_COORD_Y_START) % 4);

    `define  is_north_edge_RTR               (rtr_location_y_coord == cip_pkg::CIP_RTR_GRID_COORD_Y_START)
    `define  is_south_edge_RTR               (rtr_location_y_coord == cip_pkg::CIP_RTR_GRID_COORD_Y_END-1)   
    `define  is_west_edge_RTR                (rtr_location_x_coord == cip_pkg::CIP_RTR_GRID_COORD_X_START) 
    `define  is_east_edge_RTR                (rtr_location_x_coord == (cip_pkg::CIP_RTR_GRID_COORD_X_END-1)) 
    `define  is_ne_corner_RTR                ((`is_north_edge_RTR) && (`is_east_edge_RTR))
    `define  is_nw_corner_RTR                ((`is_north_edge_RTR) && (`is_west_edge_RTR))
    `define  is_se_corner_RTR                ((`is_south_edge_RTR) && (`is_east_edge_RTR))
    `define  is_sw_corner_RTR                ((`is_south_edge_RTR) && (`is_west_edge_RTR))
    `define  is_cntr_RTR                    !((`is_north_edge_RTR) || (`is_south_edge_RTR) || (`is_west_edge_RTR) || (`is_east_edge_RTR))

//------------------------------------------------------------------------------
//-- General Assumption --
//----------------------------------------∂--------------------------------------

    `ifdef FORMAL

      `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_stable,                    rtr_location.xcoord == rtr_location_x_coord && rtr_location.ycoord ==  rtr_location_y_coord && rtr_location.cip_id == rtr_location_cip_id);
                
      `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__ASYNC_DISABLE_0_stable,            TEST__ASYNC_DISABLE == 0 );
                
      `SV_ASSERT  ( FVPH_RTR_FV_am_TEST__SPARE_0_stable,                    TEST__SPARE == 0 );
                
      `SV_ASSERT  ( FVPH_RTR_FV_am_test_mode_0_stable,                      test_mode == 0 );
                
      `SV_ASSERT  ( FVPH_RTR_FV_am_CORE_MEM_RST_0_stable,                   CORE_MEM_RST == 0 );
      
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_CFG_DISABLED_PE0_stable,       ##1 $stable(`CIP_IRTR_CFG_DISABLED_PE0) );  
      
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_CFG_DISABLED_PE1_stable,       ##1 $stable(`CIP_IRTR_CFG_DISABLED_PE1) );
      
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_CRTR_CFG_DISABLED_PE0_stable,       ##1 $stable(`CIP_CRTR_CFG_DISABLED_PE0) );  
      
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_CRTR_CFG_DISABLED_PE1_stable,       ##1 $stable(`CIP_CRTR_CFG_DISABLED_PE1) );
            
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc0_stable_west     ,      ##1 $stable(`CIP_IRTR_WEST_CSR.tx_dwrr_src_weights_dnoc_vc0_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc0_stable_east     ,      ##1 $stable(`CIP_IRTR_EAST_CSR.tx_dwrr_src_weights_dnoc_vc0_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc0_stable_north    ,      ##1 $stable(`CIP_IRTR_NORTH_CSR.tx_dwrr_src_weights_dnoc_vc0_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc0_stable_south    ,      ##1 $stable(`CIP_IRTR_SOUTH_CSR.tx_dwrr_src_weights_dnoc_vc0_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc1_stable_west     ,      ##1 $stable(`CIP_IRTR_WEST_CSR.tx_dwrr_src_weights_dnoc_vc1_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc1_stable_east     ,      ##1 $stable(`CIP_IRTR_EAST_CSR.tx_dwrr_src_weights_dnoc_vc1_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc1_stable_north    ,      ##1 $stable(`CIP_IRTR_NORTH_CSR.tx_dwrr_src_weights_dnoc_vc1_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc1_stable_south    ,      ##1 $stable(`CIP_IRTR_SOUTH_CSR.tx_dwrr_src_weights_dnoc_vc1_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc2_stable_west     ,      ##1 $stable(`CIP_IRTR_WEST_CSR.tx_dwrr_src_weights_dnoc_vc2_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc2_stable_east     ,      ##1 $stable(`CIP_IRTR_EAST_CSR.tx_dwrr_src_weights_dnoc_vc2_output )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc2_stable_north    ,      ##1 $stable(`CIP_IRTR_NORTH_CSR.tx_dwrr_src_weights_dnoc_vc2_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_src_weight_vc2_stable_south    ,      ##1 $stable(`CIP_IRTR_SOUTH_CSR.tx_dwrr_src_weights_dnoc_vc2_output)); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_vc_weight_stable_west          ,      ##1 $stable(`CIP_IRTR_WEST_CSR.dwrr_vc_weights_dnoc_output    )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_vc_weight_stable_east          ,      ##1 $stable(`CIP_IRTR_EAST_CSR.dwrr_vc_weights_dnoc_output    )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_vc_weight_stable_north         ,      ##1 $stable(`CIP_IRTR_NORTH_CSR.dwrr_vc_weights_dnoc_output  )); 
      `SV_ASSERT  ( FVPH_RTR_FV_am_CIP_IRTR_vc_weight_stable_south         ,      ##1 $stable(`CIP_IRTR_SOUTH_CSR.dwrr_vc_weights_dnoc_output  )); 

    `endif


    `ifdef FORMAL
    // Assigning unique ids
        generate
            for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC; num_of_nocs++ ) begin: dnoc_east_intf_constrains
                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (EAST),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_east_intf_constrains (

                    .d_noc_in                       (irtr_d_noc_east_in[num_of_nocs]),
                    .d_noc_in_credit_release        (irtr_d_noc_east_in_credit_release[num_of_nocs]),
                    .d_noc_in_valid                 (irtr_d_noc_east_in_valid[num_of_nocs]),
    
                    .d_noc_out                      (irtr_d_noc_east_out[num_of_nocs]),
                    .d_noc_out_credit_release       (irtr_d_noc_east_out_credit_release[num_of_nocs]),
                    .d_noc_out_valid                (irtr_d_noc_east_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );

            end
            for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC; num_of_nocs++ ) begin: dnoc_west_intf_constrains
                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (WEST),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_west_intf_constrains (

                    .d_noc_in                       (irtr_d_noc_west_in[num_of_nocs]),
                    .d_noc_in_credit_release        (irtr_d_noc_west_in_credit_release[num_of_nocs]),
                    .d_noc_in_valid                 (irtr_d_noc_west_in_valid[num_of_nocs]),
    
                    .d_noc_out                      (irtr_d_noc_west_out[num_of_nocs]),
                    .d_noc_out_credit_release       (irtr_d_noc_west_out_credit_release[num_of_nocs]),
                    .d_noc_out_valid                (irtr_d_noc_west_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );
            end

            for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC; num_of_nocs++ ) begin: dnoc_north_intf_constrains

                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (NORTH),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_north_intf_constrains (

                    .d_noc_in                       (irtr_d_noc_north_in[num_of_nocs]),
                    .d_noc_in_credit_release        (irtr_d_noc_north_in_credit_release[num_of_nocs]),
                    .d_noc_in_valid                 (irtr_d_noc_north_in_valid[num_of_nocs]),
    
                    .d_noc_out                      (irtr_d_noc_north_out[num_of_nocs]),
                    .d_noc_out_credit_release       (irtr_d_noc_north_out_credit_release[num_of_nocs]),
                    .d_noc_out_valid                (irtr_d_noc_north_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );

            end

            for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC; num_of_nocs++ ) begin: dnoc_south_intf_constrains

                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (SOUTH),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_south_intf_constrains (

                    .d_noc_in                       (irtr_d_noc_south_in[num_of_nocs]),
                    .d_noc_in_credit_release        (irtr_d_noc_south_in_credit_release[num_of_nocs]),
                    .d_noc_in_valid                 (irtr_d_noc_south_in_valid[num_of_nocs]),
    
                    .d_noc_out                      (irtr_d_noc_south_out[num_of_nocs]),
                    .d_noc_out_credit_release       (irtr_d_noc_south_out_credit_release[num_of_nocs]),
                    .d_noc_out_valid                (irtr_d_noc_south_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );            
                
                end

            for (genvar num_of_nocs=0; num_of_nocs<NUM_DNOC_FROM_FI; num_of_nocs++) begin: dnoc_leaf0_intf_constrains

                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (LEAF0),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_leaf0_intf_constrains (

                    .d_noc_in                       (fi_irtr_dnoc[0][num_of_nocs]),
                    .d_noc_in_credit_release        (fi_irtr_dnoc_credit_release[0][num_of_nocs]),
                    .d_noc_in_valid                 (fi_irtr_dnoc_valid[0][num_of_nocs]),
    
                    .d_noc_out                      (irtr_fi_dnoc[0][0]),
                    .d_noc_out_credit_release       (irtr_fi_dnoc_credit_release[0][0]),
                    .d_noc_out_valid                (irtr_fi_dnoc_valid[0][0]),
    
                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );      
            end

            for (genvar num_of_nocs=0; num_of_nocs<NUM_DNOC_FROM_FI; num_of_nocs++) begin: dnoc_leaf1_intf_constrains

                cip_rtr_dnoc_intf_constrains #(

                    .SIDE                           (LEAF1),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) cip_irtr_dnoc_leaf1_intf_constrains (

                    .d_noc_in                       (fi_irtr_dnoc[1][num_of_nocs]),
                    .d_noc_in_credit_release        (fi_irtr_dnoc_credit_release[1][num_of_nocs]),
                    .d_noc_in_valid                 (fi_irtr_dnoc_valid[1][num_of_nocs]),
    
                    .d_noc_out                      (irtr_fi_dnoc[1][0]),
                    .d_noc_out_credit_release       (irtr_fi_dnoc_credit_release[1][0]),
                    .d_noc_out_valid                (irtr_fi_dnoc_valid[1][0]),
    
                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );      
            end

        endgenerate
    `endif    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------
`ifdef FORMAL
    generate if (FLOW_CONTROL_EAST) begin: flow_ctrl_east
        for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC; num_of_nocs++) begin: flow_ctrl_east_lanes
            cip_rtr_flow_control # (max_reqs_east[num_of_nocs]       
            ) cip_rtr_flow_control_east (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_d_noc_east_in_valid[num_of_nocs])
            );           
        end     
    end    
    endgenerate

    generate if (FLOW_CONTROL_WEST) begin: flow_ctrl_west
        for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC; num_of_nocs++) begin: flow_ctrl_west_lanes
            cip_rtr_flow_control # (max_reqs_west[num_of_nocs]       
            ) cip_rtr_flow_control_west (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_d_noc_west_in_valid[num_of_nocs])
            );           
        end     
    end    
    endgenerate

    generate if (FLOW_CONTROL_NORTH) begin: flow_ctrl_north
        for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC; num_of_nocs++) begin: flow_ctrl_north_lanes
            cip_rtr_flow_control # (max_reqs_north[num_of_nocs]       
            ) cip_rtr_flow_control_north (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_d_noc_north_in_valid[num_of_nocs])
            );           
        end     
    end    
    endgenerate

    generate if (FLOW_CONTROL_SOUTH) begin: flow_ctrl_south
        for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC; num_of_nocs++) begin: flow_ctrl_south_lanes
            cip_rtr_flow_control # (max_reqs_south[num_of_nocs]       
            ) cip_rtr_flow_control_south (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (irtr_d_noc_south_in_valid[num_of_nocs])
            );           
        end     
    end    
    endgenerate

    generate if (FLOW_CONTROL_LEAF0) begin: flow_ctrl_leaf0
            cip_rtr_flow_control # (max_reqs_leaf0      
            ) cip_rtr_flow_control_leaf0 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_irtr_dnoc_valid[0][0])
            );           
    end    
    endgenerate

    generate if (FLOW_CONTROL_LEAF1) begin: flow_ctrl_leaf1
            cip_rtr_flow_control # (max_reqs_leaf1       
            ) cip_rtr_flow_control_leaf0 (
                .clk                            (clk),
                .reset_n                        (reset_n),
                .valid                          (fi_irtr_dnoc_valid[1][0])
            );           
    end    
    endgenerate
`endif


//------------------------------------------------------------------------------
//-- Checker files --
//------------------------------------------------------------------------------

//-- e2e Routing Checks --

    `ifndef NO_ROUTING

        `include "cip_irtr_dnoc_e2e_sva.sv"

    `endif

    `ifndef ONLY_E2E

        //-- FIFO/Arb/Peroformance checks --
        
        `ifdef GEN_SUB_BLOCK_CHECKS

            if (`is_cntr_RTR && rtr_location_cip_id==0) begin: sub_block_checks
            
                `include "cip_irtr_dnoc_sub_block_checks.sv"
            
            end
        
        `endif

        //-- invariants for centre only --

        `ifdef INVARIANTS

            if (`is_cntr_RTR && rtr_location_cip_id==0) begin: invariants

                `include "cip_irtr_dnoc_inv1_sva.sv"

                `include "cip_irtr_dnoc_inv2_sva.sv"

            end

        `endif

    `endif



endmodule