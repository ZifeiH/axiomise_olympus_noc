/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_rtr_unoc_FBAXI_bind.sv
// This file bind UNOC FBAXI testbench with rtl
/////////////////////////////////////////////////////////////////////////////////////////

module mnm_rtr_unoc_fbaxi_bind;
      
  //crtr
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_fi_crtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(fi_crtr_unoc_valid[0][0]),
    .unoc_resp_bundle(fi_crtr_unoc[0][0]),

    .unoc_req_valid(crtr_fi_unoc_valid[0][0]),
    .unoc_req_bundle(crtr_fi_unoc[0][0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_fi_crtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(crtr_fi_unoc_valid[0][0]),
    .unoc_resp_bundle(crtr_fi_unoc[0][0]),

    .unoc_req_valid(fi_crtr_unoc_valid[0][0]),
    .unoc_req_bundle(fi_crtr_unoc[0][0]),


    .rtr_location(rtr_location)
  );

//irtr
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_fi_irtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(fi_irtr_unoc_valid[0][0]),
    .unoc_resp_bundle(fi_irtr_unoc[0][0]),

    .unoc_req_valid(irtr_fi_unoc_valid[0][0]),
    .unoc_req_bundle(irtr_fi_unoc[0][0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_fi_irtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_fi_unoc_valid[0][0]),
    .unoc_resp_bundle(irtr_fi_unoc[0][0]),

    .unoc_req_valid(fi_irtr_unoc_valid[0][0]),
    .unoc_req_bundle(fi_irtr_unoc[0][0]),


    .rtr_location(rtr_location)
  );


  //unoc_east    
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_east_rtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_east_in_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_east_in[0]),

    .unoc_req_valid(irtr_u_noc_east_out_valid[0]),
    .unoc_req_bundle(irtr_u_noc_east_out[0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_east_rtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_east_out_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_east_out[0]),

    .unoc_req_valid(irtr_u_noc_east_in_valid[0]),
    .unoc_req_bundle(irtr_u_noc_east_in[0]),


    .rtr_location(rtr_location)
  );


  //unoc_west
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_west_rtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_west_in_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_west_in[0]),

    .unoc_req_valid(irtr_u_noc_west_out_valid[0]),
    .unoc_req_bundle(irtr_u_noc_west_out[0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_west_rtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_west_out_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_west_out[0]),

    .unoc_req_valid(irtr_u_noc_west_in_valid[0]),
    .unoc_req_bundle(irtr_u_noc_west_in[0]),


    .rtr_location(rtr_location)
  );

  //unoc_south
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_south_rtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_south_in_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_south_in[0]),

    .unoc_req_valid(irtr_u_noc_south_out_valid[0]),
    .unoc_req_bundle(irtr_u_noc_south_out[0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_south_rtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_south_out_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_south_out[0]),

    .unoc_req_valid(irtr_u_noc_south_in_valid[0]),
    .unoc_req_bundle(irtr_u_noc_south_in[0]),


    .rtr_location(rtr_location)
  );


  //unoc_north
  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1)
  )
  u_unoc_north_rtr_master_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_north_in_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_north_in[0]),

    .unoc_req_valid(irtr_u_noc_north_out_valid[0]),
    .unoc_req_bundle(irtr_u_noc_north_out[0]),


    .rtr_location(rtr_location)
  );

  bind mnm_rtr fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0)
  )
  u_unoc_north_rtr_slave_e2e
  (
    .clk(clk),
    .reset_n(soc_unoc_reset_n),

    .unoc_resp_valid(irtr_u_noc_north_out_valid[0]),
    .unoc_resp_bundle(irtr_u_noc_north_out[0]),

    .unoc_req_valid(irtr_u_noc_north_in_valid[0]),
    .unoc_req_bundle(irtr_u_noc_north_in[0]),


    .rtr_location(rtr_location)
  );


 bind mnm_rtr mnm_rtr_unoc_FBAXI_sva #(
        .STUB_FULL       (STUB_FULL),
        .STUB_DCNOC      (STUB_DCNOC),
        .STUB_CRTR       (STUB_CRTR),
        .STUB_IRTR       (STUB_IRTR),
        .MNM_RTR_DRIVE_0 (MNM_RTR_DRIVE_0) 
  ) u_mnm_rtr_unoc_FBAXI_sva  (.*);

/////////////////
//// RX
/////////////////

  bind `UNOC_IRTR_N_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_north_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o && !`UNOC_IRTR_N_RX_TX_ERR_O),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_N_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_north_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_S_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_south_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_S_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_south_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_E_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_east_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_E_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_east_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_W_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_west_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_W_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_west_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_FI1_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_fi_1_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_FI1_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_fi_1_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_CRTR_FI0_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_fi_0_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(|tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(my_location)
  );

  bind `UNOC_CRTR_FI0_RX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_rx_unoc_fi_0_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(|tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),

    .rtr_location(my_location)
  );

/////////////////
//// TX
/////////////////

  bind `UNOC_IRTR_N_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_north_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_N_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_north_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_S_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_south_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_S_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_south_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_E_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_east_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_E_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_east_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_W_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_west_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_W_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_west_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_FI1_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_lf1_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_FI1_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_lf1_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_CRTR_FI0_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(1),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_lf0_master
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(rx_valid_i),
    .unoc_resp_bundle(rx_pyld_i),

    .unoc_req_valid(tx_valid_o),
    .unoc_req_bundle(tx_pyld_o),


    .rtr_location(rtr_location)
  );

  bind `UNOC_CRTR_FI0_TX fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .ASSERT_ONLY(1)
  )
  u_tx_unoc_lf0_slave
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(tx_valid_o),
    .unoc_resp_bundle(tx_pyld_o),

    .unoc_req_valid(rx_valid_i),
    .unoc_req_bundle(rx_pyld_i),


    .rtr_location(rtr_location)
  );

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2n_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[NORTH]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );
  

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2s_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[SOUTH]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2e_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[EAST]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2w_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[WEST]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2lf0_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[LEAF0]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_IRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_irtr2lf1_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[LEAF1]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );


  bind `UNOC_CRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_crtr2lf0_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[LEAF0]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

  bind `UNOC_CRTR_CFG fbaxi_unoc_protocol_checker
  #(
    .UNOC_MASTER(0),
    .CFG_CHK(1),
    .ASSERT_ONLY(1),
    .BURST_ON(0)
  )
  u_mnm_rtr_u_crtr2lf1_unoc_slave_e2e
  (
    .clk(clk),
    .reset_n(reset_n),

    .unoc_resp_valid(cfg_tx_valid_o[LEAF1]),
    .unoc_resp_bundle(cfg_tx_pyld_o),

    .unoc_req_valid(rx_cfg_valid_i),
    .unoc_req_bundle(rx_cfg_pyld_i),


    .rtr_location(my_location)
  );

`ifdef GEN_INVARIANTS
  `ifdef IS_CENTER_RTR

    // /////////////////////////////////
    // ///// TX INVARIANTS
    // /////////////////////////////////
    bind `UNOC_IRTR_N_TX unoc_tx_invariants
    #(.DIR(0))
    u_unoc_tx_invariants_north
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
      .cfifo_pop(cfifo_pop) ,
      .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );



    bind `UNOC_IRTR_S_TX unoc_tx_invariants
    #(.DIR(2))
    u_unoc_tx_invariants_south
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
       .cfifo_pop(cfifo_pop) ,
     .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );


    bind `UNOC_IRTR_W_TX unoc_tx_invariants
    #(.DIR(1))
    u_unoc_tx_invariants_west
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
       .cfifo_pop(cfifo_pop) ,
     .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );


    bind `UNOC_IRTR_E_TX unoc_tx_invariants
    #(.DIR(3))
    u_unoc_tx_invariants_east
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
       .cfifo_pop(cfifo_pop) ,
     .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );


    bind `UNOC_CRTR_FI0_TX unoc_tx_invariants
    #(.DIR(4))
    u_unoc_tx_invariants_fi0
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
       .cfifo_pop(cfifo_pop) ,
     .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );


    bind `UNOC_IRTR_FI1_TX unoc_tx_invariants
    #(.DIR(5))
    u_unoc_tx_invariants_fi1
    (
      .tx_valid_o(tx_valid_o)          ,
      .tx_pyld_o(tx_pyld_o)           ,
      .clk(clk)                 ,
      .reset_n(reset_n),
      .dfifo_empty(dfifo_empty) ,
      .dfifo_pop(dfifo_pop) ,
       .cfifo_pop(cfifo_pop) ,
     .cfifo_empty(cfifo_empty) ,
      .q_arb_grant(q_arb_grant) ,
      .q_arb_req(q_arb_req) ,
      .vc_arb_grant(vc_arb_grant) ,
      .pyld_tx_muxed(pyld_tx_muxed) ,
      .vc_arb_grant_r(vc_arb_grant_r)   
    );

  `endif
`endif

endmodule : mnm_rtr_unoc_fbaxi_bind
