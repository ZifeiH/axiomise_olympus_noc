/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_crtr_dnoc_intf_constrains.sv
// This file contains crtr dnoc interface assumptions
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_rtr_dnoc_intf_constrains # (

            parameter   SIDE                               = 0,
            parameter   num_of_nocs                        = 0,
            parameter   RTR_LOCATION_X_COORD               = 3,
            parameter   RTR_LOCATION_Y_COORD               = 4,
            parameter   RTR_LOCATION_CIP_ID                = 0
) (

  input     cip_pkg::data_noc_t                            d_noc_in,
  input     logic   [CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]       d_noc_in_credit_release,
  input     logic                                          d_noc_in_valid,

  input     cip_pkg::data_noc_t                            d_noc_out,
  input     logic   [CIP_CRTR_DNOC_TOTAL_NUM_VC-1:0]       d_noc_out_credit_release,
  input     logic                                          d_noc_out_valid,

  input     logic                                          clk,
  input     logic                                          reset_n

);  


        mnm_rtr_dnoc_credit_release_sva #(

            .SIDE                           (SIDE),
            .GEN_RX_AW_W_ASM                (!EW_EDGE_LLC_TRAFFIC),
            .GEN_TX_R_ASM                   (!EW_EDGE_LLC_TRAFFIC && !NO_R_OUT),
            .GEN_RX_ASM                     (!VOID_LEAF_INPUT)

        ) mnm_rtr_dnoc_credit_checker_sva (
            .d_noc_in                       (d_noc_in),
            .d_noc_in_credit_release        (d_noc_in_credit_release),
            .d_noc_in_valid                 (d_noc_in_valid),

            .d_noc_out                      (d_noc_out),
            .d_noc_out_credit_release       (d_noc_out_credit_release),
            .d_noc_out_valid                (d_noc_out_valid),

            .clk                            (clk),
            .reset_n                        (reset_n)
        );
        
        mnm_rtr_dnoc_FBAXI_constraints # (

            .GEN_AW_W_ASM   (!EW_EDGE_LLC_TRAFFIC)

        ) dnoc_FBAXI_constraints 
        (
            .dnoc_bundle                    (d_noc_in),
            .dnoc_valid                     (d_noc_in_valid),

            .clk                            (clk),
            .reset_n                        (reset_n)  
        );
   
endmodule