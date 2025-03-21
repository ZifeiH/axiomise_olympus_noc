///////////////////////////////////////////////////
/// File: cip_rtr_unoc_FBAXI_macros.sv
/// This file contains macro defines
///////////////////////////////////////////////////

`ifdef ASSERT_OFF
`define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
`endif

`define UNOC_RTR                            CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE
`define UNOC_IRTR                           `UNOC_RTR.main_center_irtr.u_cip_rtr_center_irtr.u_cip_rtr_unoc
`define UNOC_CRTR                           `UNOC_RTR.main_center_crtr.u_cip_rtr_center_crtr.u_cip_rtr_unoc
`define UNOC_IRTR_CNTR                      `UNOC_IRTR.u_cip_rtr_u_center
`define UNOC_CRTR_CNTR                      `UNOC_CRTR.u_cip_rtr_u_center

`define UNOC_IRTR_N_RX                      `UNOC_IRTR.u_cip_rtr_u_north.u_cip_rtr_u_pair_north.u_cip_rtr_u_rx
`define UNOC_IRTR_S_RX                      `UNOC_IRTR.u_cip_rtr_u_south.u_cip_rtr_u_pair_south.u_cip_rtr_u_rx
`define UNOC_IRTR_E_RX                      `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_east.u_cip_rtr_u_rx
`define UNOC_IRTR_W_RX                      `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_west.u_cip_rtr_u_rx
`define UNOC_CRTR_FI0_RX                    `UNOC_CRTR_CNTR.u_cip_rtr_u_pair_fi_0.u_cip_rtr_u_rx
`define UNOC_IRTR_FI1_RX                    `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_fi_1.u_cip_rtr_u_rx

`define UNOC_IRTR_N_RX_TX_ERR_O             `UNOC_IRTR_N_RX.tx_err_o

`define UNOC_IRTR_N_TX                      `UNOC_IRTR.u_cip_rtr_u_north.u_cip_rtr_u_pair_north.u_cip_rtr_u_tx
`define UNOC_IRTR_S_TX                      `UNOC_IRTR.u_cip_rtr_u_south.u_cip_rtr_u_pair_south.u_cip_rtr_u_tx
`define UNOC_IRTR_E_TX                      `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_east.u_cip_rtr_u_tx
`define UNOC_IRTR_W_TX                      `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_west.u_cip_rtr_u_tx
`define UNOC_CRTR_FI0_TX                    `UNOC_CRTR_CNTR.u_cip_rtr_u_pair_fi_0.u_cip_rtr_u_tx
`define UNOC_IRTR_FI1_TX                    `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_fi_1.u_cip_rtr_u_tx

`define UNOC_IRTR_CFG                       `UNOC_IRTR_CNTR.u_cip_rtr_u_cfg
`define UNOC_IRTR_CFG_SCW                   `UNOC_IRTR_CFG.u_cip_rtr_u_cfg_scw
`define SCW_CACHE_FULL                      `UNOC_IRTR_CFG_SCW.scw_cache_full

`define UNOC_CRTR_CFG                       `UNOC_CRTR_CNTR.u_cip_rtr_u_cfg


`define UNOC_NORTH_RX_OUT_VALID             `UNOC_IRTR.u_cip_rtr_u_north.u_cip_rtr_u_pair_north.rx2tx_valid_o
`define UNOC_SOUTH_RX_OUT_VALID             `UNOC_IRTR.u_cip_rtr_u_south.u_cip_rtr_u_pair_south.rx2tx_valid_o
`define UNOC_EAST_RX_OUT_VALID              `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_east.rx2tx_valid_o
`define UNOC_WEST_RX_OUT_VALID              `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_west.rx2tx_valid_o
`define UNOC_LEAF0_RX_OUT_VALID             `UNOC_CRTR_CNTR.u_cip_rtr_u_pair_fi_0.rx2tx_valid_o
`define UNOC_LEAF1_RX_OUT_VALID             `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_fi_1.rx2tx_valid_o

`define UNOC_NORTH_RX_OUT                   `UNOC_IRTR.u_cip_rtr_u_north.u_cip_rtr_u_pair_north.rx2tx_pyld_o
`define UNOC_SOUTH_RX_OUT                   `UNOC_IRTR.u_cip_rtr_u_south.u_cip_rtr_u_pair_south.rx2tx_pyld_o
`define UNOC_EAST_RX_OUT                    `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_east.rx2tx_pyld_o
`define UNOC_WEST_RX_OUT                    `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_west.rx2tx_pyld_o
`define UNOC_LEAF0_RX_OUT                   `UNOC_CRTR_CNTR.u_cip_rtr_u_pair_fi_0.rx2tx_pyld_o
`define UNOC_LEAF1_RX_OUT                   `UNOC_IRTR_CNTR.u_cip_rtr_u_pair_fi_1.rx2tx_pyld_o

