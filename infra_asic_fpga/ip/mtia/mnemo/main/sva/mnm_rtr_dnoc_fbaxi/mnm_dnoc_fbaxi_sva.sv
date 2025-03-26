/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_sva.sv
// This file contains 
/////////////////////////////////////////////////////////////////////////////////////////
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
    output  rtr_dc_csr_pkg::registers_for_default_inputs_struct                                  csr_out,
    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_in,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_async_crd_release,
    output  logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_in_credit_release_id,
    output  logic                                                   [NUM_LANES-1:0]              noc_in_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_valid,
    output  mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_out,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_out_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_credit_release_valid,
    output  logic                                                   [NUM_LANES-1:0]              noc_out_valid,
    input   mnm_pkg::mnm_grid_location_t                                                         rtr_location,
    input   logic                                                                                soc_reset_n
); 

    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]               slice_d_noc_hcb_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]               slice_d_noc_hcb_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]               slice_d_noc_hcb_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC-1:0]               slice_d_noc_hcb_out_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]               slice_d_noc_llc_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]               slice_d_noc_llc_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]               slice_d_noc_llc_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC-1:0]               slice_d_noc_llc_out_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_north_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_north_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_north_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_north_out_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_east_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_east_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_east_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_east_out_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_south_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_south_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_south_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC-1:0]                slice_d_noc_south_out_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_west_in;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_west_in_valid;
    mnm_pkg::data_noc_t                  [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_west_out;
    logic                                [mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC-1:0]                slice_d_noc_west_out_valid;

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

        assign { slice_d_noc_hcb_in  ,
                 slice_d_noc_llc_in  ,
                 slice_d_noc_west_in ,
                 slice_d_noc_south_in,
                 slice_d_noc_east_in ,
                 slice_d_noc_north_in} = noc_in;

        assign { slice_d_noc_hcb_in_valid  ,
                 slice_d_noc_llc_in_valid  ,
                 slice_d_noc_west_in_valid ,
                 slice_d_noc_south_in_valid,
                 slice_d_noc_east_in_valid ,
                 slice_d_noc_north_in_valid} = noc_in_valid;

        assign { slice_d_noc_hcb_out  ,
                 slice_d_noc_llc_out  ,
                 slice_d_noc_west_out ,
                 slice_d_noc_south_out,
                 slice_d_noc_east_out ,
                 slice_d_noc_north_out} = noc_out;

        assign { slice_d_noc_hcb_out_valid  ,
                 slice_d_noc_llc_out_valid  ,
                 slice_d_noc_west_out_valid ,
                 slice_d_noc_south_out_valid,
                 slice_d_noc_east_out_valid ,
                 slice_d_noc_north_out_valid} = noc_out_valid;
        
        generate

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC; noc_num++ ) begin: north_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_north_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_north_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_north_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC; noc_num++ ) begin: east_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_east_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_east_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_east_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC; noc_num++ ) begin: south_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_south_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_south_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_south_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC; noc_num++ ) begin: west_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_west_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_west_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_west_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC; noc_num++ ) begin: llc_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_llc_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_llc_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_llc_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC; noc_num++ ) begin: hcb_intf_constraints

                mnm_dnoc_fbaxi_intf_constraints #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_hcb_fbaxi_intf_constraints (

                    .d_noc_in                         (slice_d_noc_hcb_in[noc_num]),
                    .d_noc_in_valid                   (slice_d_noc_hcb_in_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC; noc_num++ ) begin: north_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_north_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_north_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_north_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC; noc_num++ ) begin: east_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_east_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_east_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_east_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC; noc_num++ ) begin: south_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_south_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_south_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_south_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC; noc_num++ ) begin: west_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_west_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_west_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_west_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC; noc_num++ ) begin: llc_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_llc_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_llc_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_llc_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

            for (genvar noc_num = 0; noc_num < mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC; noc_num++ ) begin: hcb_intf_checker

                mnm_dnoc_fbaxi_intf_checker #(
                    .NUM_VC                           (NUM_VC)
                ) mnm_dnoc_hcb_fbaxi_intf_checker (

                    .d_noc_out                        (slice_d_noc_hcb_out[noc_num]),
                    .d_noc_out_valid                  (slice_d_noc_hcb_out_valid[noc_num]),

                    .clk                              (clk),
                    .reset_n                          (reset_n)
                );          
                
            end

        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
