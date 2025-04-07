/////////////////////////////////////////////////////////////////////////////////////////
// File: macro_defines.sv
// This file contains cip router macro defins
/////////////////////////////////////////////////////////////////////////////////////////

`ifdef ASSERT_OFF
  `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
`endif

`define PARTNER_IX                                    ((num_of_nocs%4==0||num_of_nocs%4==1)?LEAF1:LEAF0)
`define LOCAL_IX                                      ((num_of_nocs%4==0||num_of_nocs%4==1)?LEAF0:LEAF1)
`define PARTNER_LANE(num_of_nocs)                     ((num_of_nocs%4==0||num_of_nocs%4==1)?(num_of_nocs+2):(num_of_nocs-2))

`define CIP_CRTR_CENTER                               CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr
`define CIP_IRTR_CENTER                               CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr

`define CIP_CRTR_NORTH                                CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_crtr.u_cip_rtr_north_crtr.main
`define CIP_IRTR_NORTH                                CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_irtr.u_cip_rtr_north_irtr.main
        
`define CIP_CRTR_SOUTH                                CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_crtr.u_cip_rtr_south_crtr.main
`define CIP_IRTR_SOUTH                                CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_irtr.u_cip_rtr_south_irtr.main
        
`define CIP_CRTR_EAST                                 `CIP_CRTR_CENTER.dcnoc.u_cip_rtr_east_crtr
`define CIP_IRTR_EAST                                 `CIP_IRTR_CENTER.dcnoc.u_cip_rtr_east_irtr
        
`define CIP_CRTR_WEST                                 `CIP_CRTR_CENTER.dcnoc.u_cip_rtr_west_crtr
`define CIP_IRTR_WEST                                 `CIP_IRTR_CENTER.dcnoc.u_cip_rtr_west_irtr

`define CIP_CRTR_CFG_DISABLED_PE0                     `CIP_CRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip0
`define CIP_CRTR_CFG_DISABLED_PE1                     `CIP_CRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip1
        
`define CIP_IRTR_CFG_DISABLED_PE0                     `CIP_IRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip0
`define CIP_IRTR_CFG_DISABLED_PE1                     `CIP_IRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip1
        
`define CIP_CRTR_UNOC_VC_WEIGHTS                      `CIP_CRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.u_cip_rtr_unoc_csr.dwrr_vc_weights_unoc_output
`define CIP_IRTR_UNOC_VC_WEIGHTS                      `CIP_IRTR_CENTER.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.u_cip_rtr_unoc_csr.dwrr_vc_weights_unoc_output
        
`define CIP_CRTR_NORTH_CSR                            CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_crtr.u_cip_rtr_north_crtr.u_cip_rtr_north_csr
`define CIP_IRTR_NORTH_CSR                            CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_irtr.u_cip_rtr_north_irtr.u_cip_rtr_north_csr
`define CIP_CRTR_SOUTH_CSR                            CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_crtr.u_cip_rtr_south_crtr.u_cip_rtr_south_csr
`define CIP_IRTR_SOUTH_CSR                            CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_irtr.u_cip_rtr_south_irtr.u_cip_rtr_south_csr
`define CIP_CRTR_EAST_CSR                             `CIP_CRTR_CENTER.dcnoc.u_cip_rtr_east_crtr.u_cip_rtr_east_csr
`define CIP_IRTR_EAST_CSR                             `CIP_IRTR_CENTER.dcnoc.u_cip_rtr_east_irtr.u_cip_rtr_east_csr
`define CIP_CRTR_WEST_CSR                             `CIP_CRTR_CENTER.dcnoc.u_cip_rtr_west_crtr.u_cip_rtr_west_csr
`define CIP_IRTR_WEST_CSR                             `CIP_IRTR_CENTER.dcnoc.u_cip_rtr_west_irtr.u_cip_rtr_west_csr

    // define hierarchical paths to internal TLY input signals

    `define CRTR_NORTH_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_crtr.u_cip_rtr_north_crtr.u_cip_rtr_tly_top
    `define CRTR_SOUTH_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_crtr.u_cip_rtr_south_crtr.u_cip_rtr_tly_top
    `define CRTR_WEST_TLY   CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.dcnoc.u_cip_rtr_west_crtr.u_cip_rtr_tly_top
    `define CRTR_EAST_TLY   CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.dcnoc.u_cip_rtr_east_crtr.u_cip_rtr_tly_top
    `define CRTR_LEAF0_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.dcnoc.u_cip_rtr_west_crtr.u_cip_rtr_tly_top_leaf
    `define CRTR_LEAF1_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.dcnoc.u_cip_rtr_east_crtr.u_cip_rtr_tly_top_leaf

    `define CNOC_CRTR_NORTH_RX(num_of_nocs)                     `CIP_CRTR_NORTH.c_rx_lane[num_of_nocs].c_noc_rx_north.u_cip_rtr_rx_core_crtr
    `define CNOC_CRTR_SOUTH_RX(num_of_nocs)                     `CIP_CRTR_SOUTH.c_rx_lane[num_of_nocs].c_noc_rx_south.u_cip_rtr_rx_core_crtr
    `define CNOC_CRTR_EAST_RX(num_of_nocs)                      `CIP_CRTR_EAST.c_rx_lane[num_of_nocs].c_noc_rx_east.u_cip_rtr_rx_core_crtr
    `define CNOC_CRTR_WEST_RX(num_of_nocs)                      `CIP_CRTR_WEST.c_rx_lane[num_of_nocs].c_noc_rx_west.u_cip_rtr_rx_core_crtr
    `define CNOC_CRTR_LEAF0_RX(num_of_nocs)                     `CIP_CRTR_WEST.c_leaf_rx[num_of_nocs].c_noc_rx_leaf.u_cip_rtr_rx_core_crtr
    `define CNOC_CRTR_LEAF1_RX(num_of_nocs)                     `CIP_CRTR_EAST.c_leaf_rx[num_of_nocs].c_noc_rx_leaf.u_cip_rtr_rx_core_crtr

    `define CNOC_CRTR_NORTH_TX(num_of_nocs)                     `CIP_CRTR_NORTH.c_tx_lane[num_of_nocs].c_noc_tx_north.u_cip_rtr_tx_core_crtr
    `define CNOC_CRTR_SOUTH_TX(num_of_nocs)                     `CIP_CRTR_SOUTH.c_tx_lane[num_of_nocs].c_noc_tx_south.u_cip_rtr_tx_core_crtr
    `define CNOC_CRTR_EAST_TX(num_of_nocs)                      `CIP_CRTR_EAST.c_tx_lane[num_of_nocs].c_noc_tx_east.u_cip_rtr_tx_core_crtr
    `define CNOC_CRTR_WEST_TX(num_of_nocs)                      `CIP_CRTR_WEST.c_tx_lane[num_of_nocs].c_noc_tx_west.u_cip_rtr_tx_core_crtr
    `define CNOC_CRTR_LEAF0_TX(num_of_nocs)                     `CIP_CRTR_WEST.c_leaf_tx[num_of_nocs].c_noc_tx_leaf0.u_cip_rtr_tx_core_crtr
    `define CNOC_CRTR_LEAF1_TX(num_of_nocs)                     `CIP_CRTR_EAST.c_leaf_tx[num_of_nocs].c_noc_tx_leaf1.u_cip_rtr_tx_core_crtr

    `define DNOC_CRTR_NORTH_RX(num_of_nocs)                     `CIP_CRTR_NORTH.d_rx_lane[num_of_nocs].d_noc_rx_north.u_cip_rtr_rx_core_crtr
    `define DNOC_CRTR_SOUTH_RX(num_of_nocs)                     `CIP_CRTR_SOUTH.d_rx_lane[num_of_nocs].d_noc_rx_south.u_cip_rtr_rx_core_crtr
    `define DNOC_CRTR_EAST_RX(num_of_nocs)                      `CIP_CRTR_EAST.d_rx_lane[num_of_nocs].d_noc_rx_east.u_cip_rtr_rx_core_crtr
    `define DNOC_CRTR_WEST_RX(num_of_nocs)                      `CIP_CRTR_WEST.d_rx_lane[num_of_nocs].d_noc_rx_west.u_cip_rtr_rx_core_crtr
    `define DNOC_CRTR_LEAF0_RX(num_of_nocs)                     `CIP_CRTR_WEST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_crtr
    `define DNOC_CRTR_LEAF1_RX(num_of_nocs)                     `CIP_CRTR_EAST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_crtr

    `define DNOC_CRTR_NORTH_TX(num_of_nocs)                     `CIP_CRTR_NORTH.d_tx_lane[num_of_nocs].d_noc_tx_north.u_cip_rtr_tx_core_crtr
    `define DNOC_CRTR_SOUTH_TX(num_of_nocs)                     `CIP_CRTR_SOUTH.d_tx_lane[num_of_nocs].d_noc_tx_south.u_cip_rtr_tx_core_crtr
    `define DNOC_CRTR_EAST_TX(num_of_nocs)                      `CIP_CRTR_EAST.d_tx_lane[num_of_nocs].d_noc_tx_east.u_cip_rtr_tx_core_crtr
    `define DNOC_CRTR_WEST_TX(num_of_nocs)                      `CIP_CRTR_WEST.d_tx_lane[num_of_nocs].d_noc_tx_west.u_cip_rtr_tx_core_crtr
    `define DNOC_CRTR_LEAF0_TX(num_of_nocs)                     `CIP_CRTR_WEST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf0.u_cip_rtr_tx_core_crtr
    `define DNOC_CRTR_LEAF1_TX(num_of_nocs)                     `CIP_CRTR_EAST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf1.u_cip_rtr_tx_core_crtr

    `define IRTR_NORTH_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_irtr.u_cip_rtr_north_irtr.u_cip_rtr_tly_top
    `define IRTR_SOUTH_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_irtr.u_cip_rtr_south_irtr.u_cip_rtr_tly_top
    `define IRTR_WEST_TLY   CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.dcnoc.u_cip_rtr_west_irtr.u_cip_rtr_tly_top
    `define IRTR_EAST_TLY   CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.dcnoc.u_cip_rtr_east_irtr.u_cip_rtr_tly_top
    `define IRTR_LEAF0_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.dcnoc.u_cip_rtr_west_irtr.u_cip_rtr_tly_top_leaf
    `define IRTR_LEAF1_TLY  CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.dcnoc.u_cip_rtr_east_irtr.u_cip_rtr_tly_top_leaf

    `define CNOC_IRTR_NORTH_RX(num_of_nocs)                     `CIP_IRTR_NORTH.c_rx_lane[num_of_nocs].c_noc_rx_north.u_cip_rtr_rx_core_irtr
    `define CNOC_IRTR_SOUTH_RX(num_of_nocs)                     `CIP_IRTR_SOUTH.c_rx_lane[num_of_nocs].c_noc_rx_south.u_cip_rtr_rx_core_irtr
    `define CNOC_IRTR_EAST_RX(num_of_nocs)                      `CIP_IRTR_EAST.c_rx_lane[num_of_nocs].c_noc_rx_east.u_cip_rtr_rx_core_irtr
    `define CNOC_IRTR_WEST_RX(num_of_nocs)                      `CIP_IRTR_WEST.c_rx_lane[num_of_nocs].c_noc_rx_west.u_cip_rtr_rx_core_irtr
    `define CNOC_IRTR_LEAF0_RX(num_of_nocs)                     `CIP_IRTR_WEST.c_leaf_rx[num_of_nocs].c_noc_rx_leaf.u_cip_rtr_rx_core_irtr
    `define CNOC_IRTR_LEAF1_RX(num_of_nocs)                     `CIP_IRTR_EAST.c_leaf_rx[num_of_nocs].c_noc_rx_leaf.u_cip_rtr_rx_core_irtr

    `define CNOC_IRTR_NORTH_TX(num_of_nocs)                     `CIP_IRTR_NORTH.c_tx_lane[num_of_nocs].c_noc_tx_north.u_cip_rtr_tx_core_irtr
    `define CNOC_IRTR_SOUTH_TX(num_of_nocs)                     `CIP_IRTR_SOUTH.c_tx_lane[num_of_nocs].c_noc_tx_south.u_cip_rtr_tx_core_irtr
    `define CNOC_IRTR_EAST_TX(num_of_nocs)                      `CIP_IRTR_EAST.c_tx_lane[num_of_nocs].c_noc_tx_east.u_cip_rtr_tx_core_irtr
    `define CNOC_IRTR_WEST_TX(num_of_nocs)                      `CIP_IRTR_WEST.c_tx_lane[num_of_nocs].c_noc_tx_west.u_cip_rtr_tx_core_irtr
    `define CNOC_IRTR_LEAF0_TX(num_of_nocs)                     `CIP_IRTR_WEST.c_leaf_tx[num_of_nocs].c_noc_tx_leaf0.u_cip_rtr_tx_core_irtr
    `define CNOC_IRTR_LEAF1_TX(num_of_nocs)                     `CIP_IRTR_EAST.c_leaf_tx[num_of_nocs].c_noc_tx_leaf1.u_cip_rtr_tx_core_irtr
 
    `define DNOC_IRTR_NORTH_RX(num_of_nocs)                     `CIP_IRTR_NORTH.d_rx_lane[num_of_nocs].d_noc_rx_north.u_cip_rtr_rx_core_irtr
    `define DNOC_IRTR_SOUTH_RX(num_of_nocs)                     `CIP_IRTR_SOUTH.d_rx_lane[num_of_nocs].d_noc_rx_south.u_cip_rtr_rx_core_irtr
    `define DNOC_IRTR_EAST_RX(num_of_nocs)                      `CIP_IRTR_EAST.d_rx_lane[num_of_nocs].d_noc_rx_east.u_cip_rtr_rx_core_irtr
    `define DNOC_IRTR_WEST_RX(num_of_nocs)                      `CIP_IRTR_WEST.d_rx_lane[num_of_nocs].d_noc_rx_west.u_cip_rtr_rx_core_irtr
    `define DNOC_IRTR_LEAF0_RX(num_of_nocs)                     `CIP_IRTR_WEST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr
    `define DNOC_IRTR_LEAF1_RX(num_of_nocs)                     `CIP_IRTR_EAST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr

    `define DNOC_IRTR_NORTH_TX(num_of_nocs)                     `CIP_IRTR_NORTH.d_tx_lane[num_of_nocs].d_noc_tx_north.u_cip_rtr_tx_core_irtr
    `define DNOC_IRTR_SOUTH_TX(num_of_nocs)                     `CIP_IRTR_SOUTH.d_tx_lane[num_of_nocs].d_noc_tx_south.u_cip_rtr_tx_core_irtr
    `define DNOC_IRTR_EAST_TX(num_of_nocs)                      `CIP_IRTR_EAST.d_tx_lane[num_of_nocs].d_noc_tx_east.u_cip_rtr_tx_core_irtr
    `define DNOC_IRTR_WEST_TX(num_of_nocs)                      `CIP_IRTR_WEST.d_tx_lane[num_of_nocs].d_noc_tx_west.u_cip_rtr_tx_core_irtr
    `define DNOC_IRTR_LEAF0_TX(num_of_nocs)                     `CIP_IRTR_WEST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf0.u_cip_rtr_tx_core_irtr
    `define DNOC_IRTR_LEAF1_TX(num_of_nocs)                     `CIP_IRTR_EAST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf1.u_cip_rtr_tx_core_irtr
