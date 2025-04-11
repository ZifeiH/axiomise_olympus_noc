/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_routing_sva.sv
// This file contains 
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_routing_sva # (
  parameter NUM_LANES           = mnm_rtr_pkg::MNM_RTR_DNOC_SLICE_NUM_LANES,
            NUM_VC              = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC,
            VCID_W              = mnm_rtr_pkg::MNM_RTR_DNOC_VCID_W,
            RX_DEPTH_W          = mnm_rtr_pkg::MNM_RTR_DNOC_RX_DEPTH_W,
            NUM_SHRD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS,
            NUM_RSVD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS,
            RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS),
            SEQN_W              = mnm_rtr_pkg::MNM_RTR_SEQ_NUM_W,
            STUB                = 0,
            REMOVE_LANE         = {NUM_LANES{1'b0}}
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
//-- Router location  --
//------------------------------------------------------------------------------
//   TODO: to setup the rtr locations
    localparam  [3-1: 0]              rtr_location_x_coord          = 2;
    localparam  [3-1: 0]              rtr_location_y_coord          = 2;
    localparam  [1-1: 0]              rtr_location_cip_id_x         = 0;
    localparam  [1-1: 0]              rtr_location_cip_id_y         = 0;
    localparam  [1-1: 0]              rtr_location_cip_id_z         = 0;

    localparam  mnm_pkg::chip_id_t    current_cip_id                =  {rtr_location_cip_id_x,
                                                                        rtr_location_cip_id_y,
                                                                        rtr_location_cip_id_z};

    localparam                        rtr_slice_id                  = 0;

//------------------------------------------------------------------------------
//-- Interface Assumption --
//------------------------------------------------------------------------------
  
`ifdef FORMAL

    
    // Fix router location
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_cip_id_fixed , (rtr_location.chip_id == current_cip_id)                );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_xcoord_fixed , (rtr_location.xcoord  == rtr_location_x_coord)          );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_ycoord_fixed , (rtr_location.ycoord  == rtr_location_y_coord)          );
    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_flip_fixed   , {rtr_location.orientation.flip_ew, rtr_location.orientation.flip_ns} inside {{1'b0, 1'b0},{1'b1, 1'b1}});

    // 
    `SV_ASSERT (FVPH_RTR_FV_am_vc_y_first_routing_fixed  , csr_cfg_vc_y_first_routing == 11'h1fc                   );
    `SV_ASSERT (FVPH_RTR_FV_am_dwrr_vc_weights_fixed     , csr_cfg_dwrr_vc_weights    == 88'h0202020202020202020202);

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
                    assign noc_in_config[lane].vc_grp_rsvd_max = csr_cfg_group_rsvd_max_th[lane] ;
                    assign noc_in_config[lane].vc_grp_shrd_max = csr_cfg_group_shrd_max_th[lane] ;
                    assign noc_in_config[lane].vc_grp_shrd     = csr_cfg_vc_group_shrd[lane]     ;
                    assign noc_in_config[lane].total_shrd_max  = csr_cfg_total_shrd_max_th[lane] ;
                    assign noc_in_config[lane].total_credits   = csr_cfg_total_credits[lane]     ; 

                    mnm_dnoc_intf_constraints #(
                        .NUM_VC                          (NUM_VC),
                        .LANE_NUM                        (lane),
                        .VCID_W                          (VCID_W)
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

                        .d_noc_out_async_crd_release     (noc_out_async_crd_release[lane]),
                        .d_noc_in_async_crd_release      (noc_in_async_crd_release[lane]),

                        .rtr_location                    (rtr_location),
                        .is_y_first                      (csr_cfg_vc_y_first_routing),

                        .clk                             (clk),
                        .reset_n                         (reset_n)
                    );    
                end               
                
            end

            begin: checkers
            for (genvar in_lane = 0; in_lane < NUM_LANES; in_lane++ ) begin      
                if (!REMOVE_LANE[in_lane]) begin
                    for (genvar out_lane = 0; out_lane < NUM_LANES; out_lane++ ) begin
                        if (!REMOVE_LANE[out_lane]) begin
                            mnm_dnoc_routing_checker #(
                                .NUM_VC                           (NUM_VC),
                                .d_noc_in_lane                    (in_lane),
                                .d_noc_out_lane                   (out_lane)
                            ) mnm_dnoc_routing_checker(
                                .d_noc_in             (noc_in[in_lane]),
                                .d_noc_in_valid       (noc_in_valid[in_lane]),

                                .d_noc_out            (noc_out[out_lane]),
                                .d_noc_out_valid      (noc_out_valid[out_lane]),

                                .rtr_location         (rtr_location),
                                .is_y_first           (csr_cfg_vc_y_first_routing),

                                .clk                  (clk),
                                .reset_n              (reset_n)
                            );     
                        end
                    end
                end  
            end      
            end
        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
