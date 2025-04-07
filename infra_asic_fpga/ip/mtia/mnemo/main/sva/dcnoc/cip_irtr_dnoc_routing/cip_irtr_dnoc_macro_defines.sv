/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_macro_defines.sv
//  This file contains irtr dnoc macros
/////////////////////////////////////////////////////////////////////////////////////////
//------------------------------------------------------------------------------
//-- sub block checks defines  --
//------------------------------------------------------------------------------

    `define CIP_IRTR_NORTH_RX(num_of_nocs)                     `CIP_IRTR_NORTH.d_rx_lane[num_of_nocs].d_noc_rx_north.u_cip_rtr_rx_core_irtr
    `define CIP_IRTR_SOUTH_RX(num_of_nocs)                     `CIP_IRTR_SOUTH.d_rx_lane[num_of_nocs].d_noc_rx_south.u_cip_rtr_rx_core_irtr
    `define CIP_IRTR_EAST_RX(num_of_nocs)                      `CIP_IRTR_EAST.d_rx_lane[num_of_nocs].d_noc_rx_east.u_cip_rtr_rx_core_irtr
    `define CIP_IRTR_WEST_RX(num_of_nocs)                      `CIP_IRTR_WEST.d_rx_lane[num_of_nocs].d_noc_rx_west.u_cip_rtr_rx_core_irtr
    `define CIP_IRTR_LEAF0_RX(num_of_nocs)                     `CIP_IRTR_WEST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr
    `define CIP_IRTR_LEAF1_RX(num_of_nocs)                     `CIP_IRTR_EAST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr

    `define CIP_IRTR_NORTH_TX(num_of_nocs)                     `CIP_IRTR_NORTH.d_tx_lane[num_of_nocs].d_noc_tx_north.u_cip_rtr_tx_core_irtr
    `define CIP_IRTR_SOUTH_TX(num_of_nocs)                     `CIP_IRTR_SOUTH.d_tx_lane[num_of_nocs].d_noc_tx_south.u_cip_rtr_tx_core_irtr
    `define CIP_IRTR_EAST_TX(num_of_nocs)                      `CIP_IRTR_EAST.d_tx_lane[num_of_nocs].d_noc_tx_east.u_cip_rtr_tx_core_irtr
    `define CIP_IRTR_WEST_TX(num_of_nocs)                      `CIP_IRTR_WEST.d_tx_lane[num_of_nocs].d_noc_tx_west.u_cip_rtr_tx_core_irtr
    `define CIP_IRTR_LEAF0_TX(num_of_nocs)                     `CIP_IRTR_WEST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf0.u_cip_rtr_tx_core_irtr
    `define CIP_IRTR_LEAF1_TX(num_of_nocs)                     `CIP_IRTR_EAST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf1.u_cip_rtr_tx_core_irtr

    `define IRTR_DNOC_NORTH_RX_VC_BUF(num_of_nocs,vc)          `CIP_IRTR_NORTH.d_rx_lane[num_of_nocs].d_noc_rx_north.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_buf
    `define IRTR_DNOC_SOUTH_RX_VC_BUF(num_of_nocs,vc)          `CIP_IRTR_SOUTH.d_rx_lane[num_of_nocs].d_noc_rx_south.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_buf
    `define IRTR_DNOC_EAST_RX_VC_BUF(num_of_nocs,vc)           `CIP_IRTR_EAST.d_rx_lane[num_of_nocs].d_noc_rx_east.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_buf
    `define IRTR_DNOC_WEST_RX_VC_BUF(num_of_nocs,vc)           `CIP_IRTR_WEST.d_rx_lane[num_of_nocs].d_noc_rx_west.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_buf

    `define IRTR_DNOC_LEAF0_RX_FIFO(num_of_nocs,vc)            `CIP_IRTR_WEST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_fifo
    `define IRTR_DNOC_LEAF1_RX_FIFO(num_of_nocs,vc)            `CIP_IRTR_EAST.d_leaf_rx[num_of_nocs].d_noc_rx_leaf.u_cip_rtr_rx_core_irtr.vc_loop[vc].genblk1.genblk1.vc_fifo

    `define IRTR_DNOC_SOUTH_TX_FIFO(num_of_nocs,dir,vc)        `CIP_IRTR_SOUTH.d_tx_lane[num_of_nocs].d_noc_tx_south.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo
    `define IRTR_DNOC_NORTH_TX_FIFO(num_of_nocs,dir,vc)        `CIP_IRTR_NORTH.d_tx_lane[num_of_nocs].d_noc_tx_north.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo
    `define IRTR_DNOC_EAST_TX_FIFO(num_of_nocs,dir,vc)         `CIP_IRTR_EAST.d_tx_lane[num_of_nocs].d_noc_tx_east.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo
    `define IRTR_DNOC_WEST_TX_FIFO(num_of_nocs,dir,vc)         `CIP_IRTR_WEST.d_tx_lane[num_of_nocs].d_noc_tx_west.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo

    `define IRTR_DNOC_LEAF0_TX_FIFO(num_of_nocs,dir,vc)        `CIP_IRTR_WEST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf0.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo
    `define IRTR_DNOC_LEAF1_TX_FIFO(num_of_nocs,dir,vc)        `CIP_IRTR_EAST.d_leaf_tx[num_of_nocs].d_noc_tx_leaf1.u_cip_rtr_tx_core_irtr.dir_in[dir].genblk2[vc].genblk2.tx_vc_fifo


//------------------------------------------------------------------------------
//-- Routing invariants  --
//------------------------------------------------------------------------------
    `define DCNOC_TO_LEAF0_LANE                                (((num_of_nocs%4==0) || (num_of_nocs%4==1)) ? num_of_nocs:num_of_nocs-2)
    `define DCNOC_TO_LEAF1_LANE                                (((num_of_nocs%4==2) || (num_of_nocs%4==3)) ? num_of_nocs:num_of_nocs+2)
     
    `define DCNOC_SOUTH_TO_LEAF0_LANE                          (((((num_of_nocs+1)%4)%4==0) || (((num_of_nocs+1)%4)%4==1)) ? ((num_of_nocs+1)%4):((num_of_nocs+1)%4)-2)
    `define DCNOC_SOUTH_TO_LEAF1_LANE                          (((((num_of_nocs+1)%4)%4==2) || (((num_of_nocs+1)%4)%4==3)) ? ((num_of_nocs+1)%4):((num_of_nocs+1)%4)+2)

//------------------------------------------------------------------------------
//-- for fifo checks  --
//------------------------------------------------------------------------------
    `define IS_REQUEST_VC                                       (vc>=RESP_TOTAL_NUM_VC)          
    `define rx_only_requestor                                   (SRC_DIR == NORTH || SRC_DIR == SOUTH) && (LANE ==1||LANE==3) && `IS_REQUEST_VC;
 