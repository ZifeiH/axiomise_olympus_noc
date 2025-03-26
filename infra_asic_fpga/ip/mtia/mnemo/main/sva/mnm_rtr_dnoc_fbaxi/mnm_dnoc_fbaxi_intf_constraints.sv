/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_intf_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_fbaxi_intf_constraints # (
  parameter NUM_VC = 11
) (
  input     mnm_pkg::data_noc_t                            d_noc_in,
  input     logic                                          d_noc_in_valid,

  input     logic                                          clk,
  input     logic                                          reset_n
);  


        // mnm_rtr_dnoc_credit_release_sva #(

        //     .SIDE                           (SIDE),
        //     .GEN_RX_AW_W_ASM                (!EW_EDGE_LLC_TRAFFIC),
        //     .GEN_TX_R_ASM                   (!EW_EDGE_LLC_TRAFFIC && !NO_R_OUT),
        //     .GEN_RX_ASM                     (!VOID_LEAF_INPUT)

        // ) mnm_rtr_dnoc_credit_checker_sva (
        //     .d_noc_in                       (d_noc_in),
        //     .d_noc_in_credit_release        (d_noc_in_credit_release),
        //     .d_noc_in_valid                 (d_noc_in_valid),

        //     .d_noc_out                      (d_noc_out),
        //     .d_noc_out_credit_release       (d_noc_out_credit_release),
        //     .d_noc_out_valid                (d_noc_out_valid),

        //     .clk                            (clk),
        //     .reset_n                        (reset_n)
        // );
        
		mnm_dnoc_fbaxi_constraints # (

            .NUM_VC   (NUM_VC)

        ) dnoc_fbaxi_constraints 
        (
            .d_noc_in                    (d_noc_in),
            .d_noc_in_valid              (d_noc_in_valid),

            .clk                         (clk),
            .reset_n                     (reset_n)  
        );
   
endmodule