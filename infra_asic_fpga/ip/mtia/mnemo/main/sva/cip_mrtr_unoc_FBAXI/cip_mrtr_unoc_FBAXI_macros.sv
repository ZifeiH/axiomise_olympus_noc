///////////////////////////////////////////////////
/// File: cip_mrtr_unoc_FBAXI_macros.sv
/// This file contains macro defines
///////////////////////////////////////////////////

`define UNOC_MRTR                           `ME_TOP.main_center_mrtr.u_cip_me_rtr_center.u_cip_rtr_unoc
`define UNOC_MRTR_CNTR                      `UNOC_MRTR.u_cip_rtr_u_center
`define UNOC_MRTR_NORTH                     `UNOC_MRTR.u_cip_rtr_u_north
`define UNOC_MRTR_SOUTH                     `UNOC_MRTR.u_cip_rtr_u_south

`define UNOC_MRTR_N_RX                      `UNOC_MRTR_NORTH.u_cip_rtr_u_pair_north.u_cip_rtr_u_rx
`define UNOC_MRTR_S_RX                      `UNOC_MRTR_SOUTH.u_cip_rtr_u_pair_south.u_cip_rtr_u_rx
`define UNOC_MRTR_E_RX                      `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_east.u_cip_rtr_u_rx
`define UNOC_MRTR_W_RX                      `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_west.u_cip_rtr_u_rx
`define UNOC_MRTR_FI0_RX                    `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_fi_0.u_cip_rtr_u_rx
`define UNOC_MRTR_FI1_RX                    `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_fi_1.u_cip_rtr_u_rx

`define UNOC_MRTR_N_TX                      `UNOC_MRTR_NORTH.u_cip_rtr_u_pair_north.u_cip_rtr_u_tx
`define UNOC_MRTR_S_TX                      `UNOC_MRTR_SOUTH.u_cip_rtr_u_pair_south.u_cip_rtr_u_tx
`define UNOC_MRTR_E_TX                      `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_east.u_cip_rtr_u_tx
`define UNOC_MRTR_W_TX                      `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_west.u_cip_rtr_u_tx
`define UNOC_MRTR_FI0_TX                    `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_fi_0.u_cip_rtr_u_tx
`define UNOC_MRTR_FI1_TX                    `UNOC_MRTR_CNTR.u_cip_rtr_u_pair_fi_1.u_cip_rtr_u_tx

`define UNOC_MRTR_CFG                       `UNOC_MRTR_CNTR.u_cip_rtr_u_cfg
