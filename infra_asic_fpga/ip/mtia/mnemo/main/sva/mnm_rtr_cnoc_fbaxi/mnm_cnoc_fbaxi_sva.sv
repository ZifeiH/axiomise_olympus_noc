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

        generate

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_constraints

                mnm_cnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_cnoc_fbaxi_intf_constraints (

                    .c_noc_in                         (noc_in[lane]),
                    .c_noc_in_valid                   (noc_in_valid[lane]),
                    // .c_noc_in_cfg                     (noc_in_config[lane]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_checker

                mnm_cnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_cnoc_fbaxi_intf_checker (

                    .c_noc_out                         (noc_out[lane]),
                    .c_noc_out_valid                   (noc_out_valid[lane]),
                    // .c_noc_out_cfg                     (noc_out_config[lane]),

                    .clk                               (clk),
                    .reset_n                           (reset_n)
                );          
                
            end

        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
