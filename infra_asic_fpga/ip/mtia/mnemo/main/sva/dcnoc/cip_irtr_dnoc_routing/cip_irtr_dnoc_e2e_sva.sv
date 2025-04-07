/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_e2e_sva.sv
//  This file contains irtr dnoc e2e checks
////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- Source : East --
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//-- e2w --
//------------------------------------------------------------------------------


`ifdef FORMAL

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: e2w_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({EAST,WEST}),
      .IID(cip_rtr_pkg::IRTR_NOC_EAST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_e2w_e2e (

      .d_noc_in             (irtr_d_noc_east_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_east_in_valid[num_of_nocs] && irtr_d_noc_east_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_west_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_west_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- e2n --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: e2n_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({EAST,NORTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_EAST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_e2n_e2e (

      .d_noc_in             (irtr_d_noc_east_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_east_in_valid[num_of_nocs] && irtr_d_noc_east_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_north_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_north_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- e2s --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: e2s_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({EAST,SOUTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_EAST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_e2s_e2e (

      .d_noc_in             (irtr_d_noc_east_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_east_in_valid[num_of_nocs] && irtr_d_noc_east_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_south_out[3]),
      .d_noc_out_valid      (irtr_d_noc_south_out_valid[3]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- e2l0 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: e2l0_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({EAST,LEAF0}),
      .IID(cip_rtr_pkg::IRTR_NOC_EAST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_e2l0_e2e (

      .d_noc_in             (irtr_d_noc_east_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_east_in_valid[num_of_nocs] && irtr_d_noc_east_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[0][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[0][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- e2l1 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: e2l1_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({EAST,LEAF1}),
      .IID(cip_rtr_pkg::IRTR_NOC_EAST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_e2l1_e2e (

      .d_noc_in             (irtr_d_noc_east_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_east_in_valid[num_of_nocs] && irtr_d_noc_east_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[1][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[1][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- Source : West --
  //------------------------------------------------------------------------------

  //------------------------------------------------------------------------------
  //-- w2e --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: w2e_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({WEST,EAST}),
      .IID(cip_rtr_pkg::IRTR_NOC_WEST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_w2e_e2e (

      .d_noc_in             (irtr_d_noc_west_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_west_in_valid[num_of_nocs] && irtr_d_noc_west_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_east_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_east_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- w2n --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: w2n_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({WEST,NORTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_WEST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_w2n_e2e (

      .d_noc_in             (irtr_d_noc_west_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_west_in_valid[num_of_nocs] && irtr_d_noc_west_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_north_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_north_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- w2s --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: w2s_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({WEST,SOUTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_WEST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_w2s_e2e (

      .d_noc_in             (irtr_d_noc_west_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_west_in_valid[num_of_nocs] && irtr_d_noc_west_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_south_out[3]),
      .d_noc_out_valid      (irtr_d_noc_south_out_valid[3]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- w2l0 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: w2l0_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({WEST,LEAF0}),
      .IID(cip_rtr_pkg::IRTR_NOC_WEST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_w2l0_e2e (

      .d_noc_in             (irtr_d_noc_west_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_west_in_valid[num_of_nocs] && irtr_d_noc_west_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[0][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[0][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- w2l1 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: w2l1_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({WEST,LEAF1}),
      .IID(cip_rtr_pkg::IRTR_NOC_WEST0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_w2l1_e2e (

      .d_noc_in             (irtr_d_noc_west_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_west_in_valid[num_of_nocs] && irtr_d_noc_west_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[1][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[1][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- Source : North --
  //------------------------------------------------------------------------------

  //------------------------------------------------------------------------------
  //-- n2e --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: n2e_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({NORTH,EAST}),
      .IID(cip_rtr_pkg::IRTR_NOC_NORTH0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_n2e_e2e (

      .d_noc_in             (irtr_d_noc_north_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_north_in_valid[num_of_nocs] && irtr_d_noc_north_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_east_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_east_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- n2w --
  //------------------------------------------------------------------------------
 
  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: n2w_e2e_checker

    cip_rtr_dnoc_checker_sva # (

        .DATA_WIDTH(1),
        .DIR_VALUE({NORTH,WEST}),
        .IID(cip_rtr_pkg::IRTR_NOC_NORTH0+num_of_nocs),
        .RTR_LOCATION_X_COORD(rtr_location_x_coord),
        .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
        .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

      ) cip_rtr_dnoc_checker_sva_n2w_e2e (

        .d_noc_in             (irtr_d_noc_north_in[num_of_nocs]),
        .d_noc_in_valid       (irtr_d_noc_north_in_valid[num_of_nocs] && irtr_d_noc_north_in[num_of_nocs].ttl > 1),

        .d_noc_out            (irtr_d_noc_west_out[num_of_nocs]),
        .d_noc_out_valid      (irtr_d_noc_west_out_valid[num_of_nocs]),

        .clk                  (clk),
        .reset_n              (reset_n)
          
      );

  end

  //------------------------------------------------------------------------------
  //-- n2s --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: n2s_e2e_checker

      cip_rtr_dnoc_checker_sva # (

        .DATA_WIDTH(1),
        .DIR_VALUE({NORTH,SOUTH}),
        .IID(cip_rtr_pkg::IRTR_NOC_NORTH0+num_of_nocs),
        .RTR_LOCATION_X_COORD(rtr_location_x_coord),
        .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
        .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

      ) cip_rtr_dnoc_checker_sva_n2s_e2e (

        .d_noc_in             (irtr_d_noc_north_in[num_of_nocs]),
        .d_noc_in_valid       (irtr_d_noc_north_in_valid[num_of_nocs] && irtr_d_noc_north_in[num_of_nocs].ttl > 1),

        .d_noc_out            (irtr_d_noc_south_out[(num_of_nocs+3)%4]),
        .d_noc_out_valid      (irtr_d_noc_south_out_valid[(num_of_nocs+3)%4]),

        .clk                  (clk),
        .reset_n              (reset_n)
          
      );

  end

  //------------------------------------------------------------------------------
  //-- n2l0 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: n2l0_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({NORTH,LEAF0}),
      .IID(cip_rtr_pkg::IRTR_NOC_NORTH0+num_of_nocs),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_n2l0_e2e (

      .d_noc_in             (irtr_d_noc_north_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_north_in_valid[num_of_nocs] && irtr_d_noc_north_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[0][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[0][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- n2l1 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: n2l1_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({NORTH,LEAF1}),
      .IID(cip_rtr_pkg::IRTR_NOC_NORTH0+num_of_nocs),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_n2l1_e2e (

      .d_noc_in             (irtr_d_noc_north_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_north_in_valid[num_of_nocs] && irtr_d_noc_north_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[1][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[1][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- Source : South --
  //------------------------------------------------------------------------------

  //------------------------------------------------------------------------------
  //-- s2e --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: s2e_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({SOUTH,EAST}),
      .IID(cip_rtr_pkg::IRTR_NOC_SOUTH0+3),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_s2e_e2e (

      .d_noc_in             (irtr_d_noc_south_in[3]),
      .d_noc_in_valid       (irtr_d_noc_south_in_valid[3] && irtr_d_noc_south_in[3].ttl > 1),

      .d_noc_out            (irtr_d_noc_east_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_east_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- s2w --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: s2w_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({SOUTH,WEST}),
      .IID(cip_rtr_pkg::IRTR_NOC_SOUTH0+3),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_s2w_e2e (

      .d_noc_in             (irtr_d_noc_south_in[3]),
      .d_noc_in_valid       (irtr_d_noc_south_in_valid[3] && irtr_d_noc_south_in[3].ttl > 1),

      .d_noc_out            (irtr_d_noc_west_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_west_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- s2n --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: s2n_e2e_checker


    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({SOUTH,NORTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_SOUTH0+num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_s2n_e2e (

      .d_noc_in             (irtr_d_noc_south_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_south_in_valid[num_of_nocs] && irtr_d_noc_south_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_d_noc_north_out[(num_of_nocs+1)%4]),
      .d_noc_out_valid      (irtr_d_noc_north_out_valid[(num_of_nocs+1)%4]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- s2l0 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: s2l0_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({SOUTH,LEAF0}),
      .IID(cip_rtr_pkg::IRTR_NOC_SOUTH0+num_of_nocs),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_s2l0_e2e (

      .d_noc_in             (irtr_d_noc_south_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_south_in_valid[num_of_nocs] && irtr_d_noc_south_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[0][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[0][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- s2l1 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: s2l1_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({SOUTH,LEAF1}),
      .IID(cip_rtr_pkg::IRTR_NOC_SOUTH0+num_of_nocs),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_s2l1_e2e (

      .d_noc_in             (irtr_d_noc_south_in[num_of_nocs]),
      .d_noc_in_valid       (irtr_d_noc_south_in_valid[num_of_nocs] && irtr_d_noc_south_in[num_of_nocs].ttl > 1),

      .d_noc_out            (irtr_fi_dnoc[1][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[1][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- Source : Leaf0 --
  //------------------------------------------------------------------------------

  //------------------------------------------------------------------------------
  //-- l02e --
  //------------------------------------------------------------------------------
  
  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: l02e_e2e_checker
    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF0,EAST}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF0),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_l02e_e2e (

      .d_noc_in             (fi_irtr_dnoc[0][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[0][0] && fi_irtr_dnoc[0][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_east_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_east_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end


  //------------------------------------------------------------------------------
  //-- l02w --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: l02w_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF0,WEST}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF0),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_l02w_e2e (

      .d_noc_in             (fi_irtr_dnoc[0][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[0][0] && fi_irtr_dnoc[0][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_west_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_west_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
    // end
  end

  //------------------------------------------------------------------------------
  //-- l02n --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: l02n_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF0,NORTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF0),
      .DEST_NOC_ID((IO_SHIFT_RULE+num_of_nocs)%4),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_l02n_e2e (

      .d_noc_in             (fi_irtr_dnoc[0][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[0][0] && fi_irtr_dnoc[0][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_north_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_north_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
    
  end

  //------------------------------------------------------------------------------
  //-- l02s --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: l02s_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF0,SOUTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF0),
      .DEST_NOC_ID((IO_SHIFT_RULE+num_of_nocs)%4),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_l02s_e2e (

      .d_noc_in             (fi_irtr_dnoc[0][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[0][0] && fi_irtr_dnoc[0][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_south_out[(num_of_nocs+3)%4]),
      .d_noc_out_valid      (irtr_d_noc_south_out_valid[(num_of_nocs+3)%4]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
  end

  //------------------------------------------------------------------------------
  //-- l02l1 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_DNOC_FROM_FI ; num_of_nocs++ ) begin: l02l1_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF0,LEAF1}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF0),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_l02l1_e2e (

      .d_noc_in             (fi_irtr_dnoc[0][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[0][0] && fi_irtr_dnoc[0][0].ttl > 1), 

      .d_noc_out            (irtr_fi_dnoc[1][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[1][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
  end

  //------------------------------------------------------------------------------
  //-- Source : Leaf1 --
  //------------------------------------------------------------------------------

  //------------------------------------------------------------------------------
  //-- l12e --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: l12e_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF1,EAST}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF1),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_l12e_e2e (

      .d_noc_in             (fi_irtr_dnoc[1][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[1][0] && fi_irtr_dnoc[1][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_east_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_east_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- l12w --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_DNOC ; num_of_nocs++ ) begin: l12w_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF1,WEST}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF1),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_l12w_e2e (

      .d_noc_in             (fi_irtr_dnoc[1][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[1][0] && fi_irtr_dnoc[1][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_west_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_west_out_valid[num_of_nocs]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
  end

  //------------------------------------------------------------------------------
  //-- l12n --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: l12n_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF1,NORTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF1),
      .DEST_NOC_ID((IO_SHIFT_RULE+num_of_nocs)%4),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_l12n_e2e (

      .d_noc_in             (fi_irtr_dnoc[1][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[1][0] && fi_irtr_dnoc[1][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_north_out[num_of_nocs]),
      .d_noc_out_valid      (irtr_d_noc_north_out_valid[num_of_nocs]),


      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- l12s --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_DNOC ; num_of_nocs++ ) begin: l12s_e2e_checker

    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF1,SOUTH}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF1),
      .DEST_NOC_ID((IO_SHIFT_RULE+num_of_nocs)%4),
      .TGT_LANE(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)

    ) cip_rtr_dnoc_checker_sva_l12s_e2e (

      .d_noc_in             (fi_irtr_dnoc[1][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[1][0] && fi_irtr_dnoc[1][0].ttl > 1),

      .d_noc_out            (irtr_d_noc_south_out[(num_of_nocs+3)%4]),
      .d_noc_out_valid      (irtr_d_noc_south_out_valid[(num_of_nocs+3)%4]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );

  end

  //------------------------------------------------------------------------------
  //-- l12l0 --
  //------------------------------------------------------------------------------

  for (genvar num_of_nocs = 0; num_of_nocs<NUM_DNOC_FROM_FI ; num_of_nocs++ ) begin: l12l0_e2e_checker
    
    cip_rtr_dnoc_checker_sva # (

      .DATA_WIDTH(1),
      .DIR_VALUE({LEAF1,LEAF0}),
      .IID(cip_rtr_pkg::IRTR_NOC_LEAF1),
      .DEST_NOC_ID(num_of_nocs),
      .RTR_LOCATION_X_COORD(rtr_location_x_coord),
      .RTR_LOCATION_Y_COORD(rtr_location_y_coord),
      .RTR_LOCATION_CIP_ID(rtr_location_cip_id)


    ) cip_rtr_dnoc_checker_sva_l12l0_e2e (

      .d_noc_in             (fi_irtr_dnoc[1][0]),
      .d_noc_in_valid       (fi_irtr_dnoc_valid[1][0] && fi_irtr_dnoc[1][0].ttl > 1), 

      .d_noc_out            (irtr_fi_dnoc[0][0]),
      .d_noc_out_valid      (irtr_fi_dnoc_valid[0][0]),

      .clk                  (clk),
      .reset_n              (reset_n)
        
    );
  end

`endif