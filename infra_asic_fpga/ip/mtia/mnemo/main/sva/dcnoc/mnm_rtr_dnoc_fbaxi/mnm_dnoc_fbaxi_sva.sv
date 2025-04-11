module mnm_dnoc_fbaxi_sva # (
  parameter NUM_LANES = 11,
            NUM_VC = 11,
            VCID_W = 5,
            RX_DEPTH_W = 7,
            NUM_SHRD_CRD_GROUPS = 3,
            NUM_RSVD_CRD_GROUPS = 3,
            RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS),
            SEQN_W = 4,
            STUB = 0,
            REMOVE_LANE = {NUM_LANES{1'b0}}
) (
    input   logic                                                                                CORE_MEM_RST,
    input   logic                                                                                clk,
    input   rtr_dc_csr_pkg::registers_for_default_struct                                         csr_in,
    input   rtr_dc_csr_pkg::registers_for_default_inputs_struct                                  csr_out,
    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_in,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_in_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_valid,
    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_out,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_out_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_valid,
    input   mnm_pkg::mnm_grid_location_t                                                         rtr_location,
    input   logic                                                                                soc_reset_n


); 

  wire reset_n;
  assign reset_n = soc_reset_n;

//------------------------------------------------------------------------------
//-- CSR intf defines  --
//------------------------------------------------------------------------------

  `include "../mnm_rtr_lib/csr_signal_defines.sv"

//------------------------------------------------------------------------------
//-- Interface Assumption --
//------------------------------------------------------------------------------
  
`ifdef FORMAL

    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_stable              , $stable(rtr_location)                               );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_chip_id_fixed       , rtr_location.chip_id inside {3'b000, 3'b010}        );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_xcoord_fixed        , rtr_location.xcoord  inside {'d1, 'd2, 'd3, 'd4}    );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_ycoord_fixed        , rtr_location.ycoord  inside {'d1, 'd2, 'd3, 'd4}    );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_flip_fixed          , {rtr_location.orientation.flip_ew, rtr_location.orientation.flip_ns} inside {{1'b0, 1'b0},{1'b1, 1'b1}});

    `SV_ASSERT (FVPH_RTR_FV_am_vc_y_first_routing_fixed         , csr_cfg_vc_y_first_routing == 11'h1fc                   );
    `SV_ASSERT (FVPH_RTR_FV_am_dwrr_vc_weights_fixed            , csr_cfg_dwrr_vc_weights    == 88'h0202020202020202020202);

        generate
            
            begin: dwrr_vc_weights
            
            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: per_lane
                if (!REMOVE_LANE[lane]) begin
                    for (genvar vc = 0 ; vc < NUM_VC ; vc++) begin: per_vc
                
                        `SV_ASSERT (FVPH_RTR_FV_am_dwrr_src_weights_fixed  , csr_cfg_dwrr_src_weights[lane][vc] == 8'h02);
                
                    end 
                end
            
            end
            
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_constraints
                if (!REMOVE_LANE[lane]) begin

                    assign noc_in_config[lane].vc_rsvd_max     = csr_cfg_vc_rsvd_max_th[lane]    ;
                    assign noc_in_config[lane].vc_shrd_max     = csr_cfg_vc_shrd_max_th[lane]    ;
                    assign noc_in_config[lane].vc_grp_rsvd_en  = csr_cfg_vc_group_rsvd_en[lane]  ;
                    assign noc_in_config[lane].vc_grp_rsvd_id  = csr_cfg_vc_group_rsvd_id[lane]  ;
                    assign noc_in_config[lane].vc_grp_rsvd_max = csr_cfg_group_rsvd_max_th[lane]     ;
                    assign noc_in_config[lane].vc_grp_shrd_max = csr_cfg_group_shrd_max_th[lane] ;
                    assign noc_in_config[lane].vc_grp_shrd     = csr_cfg_vc_group_shrd[lane] ;
                    assign noc_in_config[lane].total_shrd_max  = csr_cfg_total_shrd_max_th[lane] ;
                    assign noc_in_config[lane].total_credits   = csr_cfg_total_credits[lane]     ; 

                    mnm_dnoc_intf_constraints #(
                        .NUM_VC                          (NUM_VC),
                        .LANE_NUM                        (lane)
                    ) mnm_dnoc_intf_constraints (

                        .d_noc_in                        (noc_in[lane]),
                        .d_noc_in_valid                  (noc_in_valid[lane]),
                        .csr_cfg                         (noc_in_config[lane]),
                        .d_noc_in_crd_rel_id             (noc_in_credit_release_id[lane]),
                        .d_noc_in_crd_rel_valid          (noc_in_credit_release_valid[lane]),
                        .d_noc_out                       (noc_out[lane]),
                        .d_noc_out_valid                 (noc_out_valid[lane]),
                        .d_noc_out_crd_rel_id            (noc_out_credit_release_id[lane]),
                        .d_noc_out_crd_rel_valid         (noc_out_credit_release_valid[lane]),

                        .noc_out_async_crd_release       (noc_out_async_crd_release[lane]),
                        .noc_in_async_crd_release        (noc_in_async_crd_release[lane]),
                        
                        .clk                             (clk),
                        .reset_n                         (reset_n)
                    );    
                end               
                
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_checkers
                if (!REMOVE_LANE[lane]) begin

                    mnm_dnoc_fbaxi_checker #(
                        .NUM_VC                           (NUM_VC)
                    ) mnm_dnoc_fbaxi_checker (

                        .d_noc_out                        (noc_out[lane]),
                        .d_noc_out_valid                  (noc_out_valid[lane]),

                        .clk                              (clk),
                        .reset_n                          (reset_n)

                    ); 
                end
            end
        endgenerate
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply


//------------------------------------------------------------------------------
//-- UARC checks  --
//------------------------------------------------------------------------------

  `include "mnm_dnoc_uarch_checks.sv"

//   `SV_ASSERT (test, main.north0_lane.rx_north0.rx_valid_i)
    `endif

endmodule
