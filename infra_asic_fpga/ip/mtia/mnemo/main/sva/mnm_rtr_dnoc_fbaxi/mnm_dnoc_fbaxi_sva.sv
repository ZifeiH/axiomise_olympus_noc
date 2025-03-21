module mnm_rtr_dnoc_fbaxi_sva # (
  parameter STUB = 0
) (
  input   logic                                                                                                            CORE_MEM_RST,
  input   logic                                                                                                            clk,
  input   mnm_pkg::mnm_grid_location_t                                                                                     rtr_location,
  input   cmn_csr_axi64_pkg::csr_req_struct     [1:0]                                                                      rtr_rtr_csr_req_in,
  input   cmn_csr_axi64_pkg::csr_req_struct     [1:0]                                                                      rtr_rtr_csr_req_out,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_req_ready_in,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_req_ready_out,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_req_vld_in,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_req_vld_out,
  input   cmn_csr_axi64_pkg::csr_rsp_struct     [1:0]                                                                      rtr_rtr_csr_rsp_in,
  input   cmn_csr_axi64_pkg::csr_rsp_struct     [1:0]                                                                      rtr_rtr_csr_rsp_out,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_rsp_ready_in,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_rsp_ready_out,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_rsp_vld_in,
  input   logic                                 [1:0]                                                                      rtr_rtr_csr_rsp_vld_out,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_east_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_in_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_east_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_CNOC-1:0]                                   slice_c_noc_east_out_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]  slice_c_noc_llc_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_in_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]  slice_c_noc_llc_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_c_noc_llc_out_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_north_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_in_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_north_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_north_out_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_south_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_in_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]   slice_c_noc_south_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_CNOC-1:0]                                   slice_c_noc_south_out_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_east_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_in_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_east_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                                   slice_d_noc_east_out_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]  slice_d_noc_llc_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_in_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]  slice_d_noc_llc_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_d_noc_llc_out_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_north_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_in_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_north_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_north_out_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_in,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_south_in_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_in_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_in_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_out,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]   slice_d_noc_south_out_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_out_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                                   slice_d_noc_south_out_valid,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_hcb_rtr_c_noc,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_hcb_rtr_c_noc_credit_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]  slice_hcb_rtr_c_noc_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_hcb_rtr_c_noc_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0][29:0]                            slice_hcb_rtr_c_noc_dbg_status_bus,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_hcb_rtr_c_noc_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_hcb_rtr_d_noc,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_hcb_rtr_d_noc_credit_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]  slice_hcb_rtr_d_noc_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_hcb_rtr_d_noc_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0][29:0]                            slice_hcb_rtr_d_noc_dbg_status_bus,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_hcb_rtr_d_noc_valid,
  input   logic                                 [2:0]                                                                      slice_id,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_llc_rtr_c_noc_credit_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_llc_rtr_d_noc_credit_cdc_fifo_credit_return,
  input   mnm_pkg::control_noc_t                [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_rtr_hcb_c_noc,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0][mnm_pkg::MNM_CNOC_VC_WIDTH-1:0]  slice_rtr_hcb_c_noc_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_rtr_hcb_c_noc_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_rtr_hcb_c_noc_data_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_CNOC-1:0]                                  slice_rtr_hcb_c_noc_valid,
  input   mnm_pkg::data_noc_t                   [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_rtr_hcb_d_noc,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0][mnm_pkg::MNM_DNOC_VC_WIDTH-1:0]  slice_rtr_hcb_d_noc_credit_release,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_rtr_hcb_d_noc_credit_release_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_rtr_hcb_d_noc_data_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]                                  slice_rtr_hcb_d_noc_valid,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_CNOC-1:0]                                  slice_rtr_llc_c_noc_data_cdc_fifo_credit_return,
  input   logic                                 [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]                                  slice_rtr_llc_d_noc_data_cdc_fifo_credit_return,
  input   logic                                                                                                            soc_reset_n,
  input   logic                                                                                                            soc_unoc_reset_n
); 


//------------------------------------------------------------------------------
//-- Router location  --
//------------------------------------------------------------------------------
//   TODO: to setup the rtr locations
    localparam  rtr_location_x_coord          = 1;
    localparam  rtr_location_y_coord          = 1;
    localparam  rtr_location_cip_id           = 0;
    localparam  rtr_slice_id                  = 0;

//------------------------------------------------------------------------------
//-- General Assumption --
//------------------------------------------------------------------------------

    `ifdef FORMAL

      `SV_ASSERT  ( FVPH_RTR_FV_am_rtr_location_stable,  ##1 $stable(rtr_location));
      `SV_ASSERT  ( FVPH_RTR_FV_am_slice_id_stable    ,  ##1 $stable(slice_id));
 
    `endif

//------------------------------------------------------------------------------
//-- Interface Assumption --
//------------------------------------------------------------------------------

    `ifdef FORMAL
  
        generate
            for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_NOC; num_of_nocs++ ) begin: east_intf_constrains
                mnm_fbaxi_intf_constrains #(

                    .SIDE                           (EAST),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) mnm_rtr_east_intf_constrains (

                    .noc_in                         (slice_d_noc_east_in[num_of_nocs]),
                    .noc_in_valid                   (slice_d_noc_east_in_valid[num_of_nocs]),
                    .noc_in_credit_release          (slice[num_of_nocs]),
 
                    .noc_out                        (slice_d_noc_east_out[num_of_nocs]),
                    .noc_out_valid                  (slice_d_noc_east_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );

            end
            for (genvar num_of_nocs = 0; num_of_nocs<NUM_EW_NOC; num_of_nocs++ ) begin: west_intf_constrains
                mnm_fbaxi_intf_constrains #(

                    .SIDE                           (WEST),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) mnm_rtr_west_intf_constrains (

                    .noc_in                         (slice_d_noc_west_in[num_of_nocs]),
                    .noc_in_valid                   (slice_d_noc_west_in_valid[num_of_nocs]),
  
                    .noc_out                        (slice_d_noc_west_out[num_of_nocs]),
                    .noc_out_valid                  (slice_d_noc_west_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );
            end

            for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_NOC; num_of_nocs++ ) begin: north_intf_constrains

                mnm_fbaxi_intf_constrains #(

                    .SIDE                           (NORTH),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) mnm_rtr_north_intf_constrains (

                    .noc_in                         (slice_d_noc_north_in[num_of_nocs]),
                    .noc_in_valid                   (slice_d_noc_north_in_valid[num_of_nocs]),

                    .noc_out                        (slice_d_noc_north_out[num_of_nocs]),
                    .noc_out_valid                  (slice_d_noc_north_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );

            end

            for (genvar num_of_nocs = 0; num_of_nocs<NUM_NS_NOC; num_of_nocs++ ) begin: south_intf_constrains

                mnm_fbaxi_intf_constrains #(

                    .SIDE                           (SOUTH),
                    .num_of_nocs                    (num_of_nocs),
                    .RTR_LOCATION_X_COORD           (rtr_location_x_coord),
                    .RTR_LOCATION_Y_COORD           (rtr_location_y_coord),
                    .RTR_LOCATION_CIP_ID            (rtr_location_cip_id)

                ) mnm_rtr_south_intf_constrains (

                    .noc_in                         (slice_d_noc_south_in[num_of_nocs]),
                    .noc_in_valid                   (slice_d_noc_south_in_valid[num_of_nocs]),

                    .noc_out                        (slice_d_noc_south_out[num_of_nocs]),
                    .noc_out_valid                  (slice_d_noc_south_out_valid[num_of_nocs]),

                    .clk                            (clk),
                    .reset_n                        (reset_n)
                );            
                
                end

        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
