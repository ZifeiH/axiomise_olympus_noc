/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_fbaxi_sva.sv
// This file contains 
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_cnoc_fbaxi_sva # (
  parameter NUM_LANES = mnm_rtr_pkg::MNM_RTR_CNOC_SLICE_NUM_LANES,
            NUM_VC = mnm_pkg::MNM_CNOC_TOTAL_NUM_VC,
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
    input   mnm_pkg::control_noc_t                                  [NUM_LANES-1:0]              noc_in,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_in_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_valid,
    input   mnm_pkg::control_noc_t                                  [NUM_LANES-1:0]              noc_out,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_out_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_valid,
    input   mnm_pkg::mnm_grid_location_t                                                         rtr_location,
    input   logic                                                                                soc_reset_n
); 

logic  reset_n;
assign reset_n = soc_reset_n;

//------------------------------------------------------------------------------
//-- CSR intf defines  --
//------------------------------------------------------------------------------
  `include "../mnm_rtr_lib/cnoc_csr_signal_defines.sv"

//------------------------------------------------------------------------------
//-- Router location  --
//------------------------------------------------------------------------------
//   TODO: to setup the rtr locations
    localparam  rtr_location_x_coord          = 1;
    localparam  rtr_location_y_coord          = 1;
    localparam  rtr_location_cip_id           = 0;
    localparam  rtr_slice_id                  = 0;

//------------------------------------------------------------------------------
//-- Interface Assumption --
//------------------------------------------------------------------------------
  
`ifdef FORMAL

    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_stable       , ##1 $stable(rtr_location)                               );
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
                    assign noc_in_config[lane].vc_grp_rsvd_max = csr_cfg_group_rsvd_max_th[lane]     ;
                    assign noc_in_config[lane].vc_grp_shrd_max = csr_cfg_group_shrd_max_th[lane] ;
                    assign noc_in_config[lane].vc_grp_shrd     = csr_cfg_vc_group_shrd[lane] ;
                    assign noc_in_config[lane].total_shrd_max  = csr_cfg_total_shrd_max_th[lane] ;
                    assign noc_in_config[lane].total_credits   = csr_cfg_total_credits[lane]     ; 

                    mnm_cnoc_intf_constraints #(
                        .NUM_VC                          (NUM_VC),
                        .LANE_NUM                        (lane),
                        .VCID_W                          (VCID_W)
                    ) mnm_cnoc_intf_constraints (

                        .c_noc_in                        (noc_in[lane]),
                        .c_noc_in_valid                  (noc_in_valid[lane]),
                        .csr_cfg                         (noc_in_config[lane]),
                        .c_noc_in_crd_rel_id             (noc_in_credit_release_id[lane]),
                        .c_noc_in_crd_rel_valid          (noc_in_credit_release_valid[lane]),
                        .c_noc_out                       (noc_out[lane]),
                        .c_noc_out_valid                 (noc_out_valid[lane]),
                        .c_noc_out_crd_rel_id            (noc_out_credit_release_id[lane]),
                        .c_noc_out_crd_rel_valid         (noc_out_credit_release_valid[lane]),

                        .noc_out_async_crd_release       (noc_out_async_crd_release[lane]),
                        .noc_in_async_crd_release        (noc_in_async_crd_release[lane]),
                        
                        .clk                             (clk),
                        .reset_n                         (reset_n)
                    );    
                end               
                
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_checkers
                if (!REMOVE_LANE[lane]) begin

                    mnm_cnoc_fbaxi_checker #(
                        .NUM_VC                           (NUM_VC)
                    ) mnm_cnoc_fbaxi_checker (

                        .c_noc_out                        (noc_out[lane]),
                        .c_noc_out_valid                  (noc_out_valid[lane]),

                        .clk                              (clk),
                        .reset_n                          (reset_n)

                    ); 
                end
            end
        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
