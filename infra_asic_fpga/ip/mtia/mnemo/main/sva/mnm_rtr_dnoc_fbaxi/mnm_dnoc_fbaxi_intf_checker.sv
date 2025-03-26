/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_intf_checker.sv
// This file contains mnm fbaxi checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_fbaxi_intf_checker # (
  parameter NUM_VC = 11
) (
  input     mnm_pkg::data_noc_t                            d_noc_out,
  input     logic                                          d_noc_out_valid,

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
        
		mnm_dnoc_fbaxi_checker # (

            .NUM_VC   (NUM_VC)

    ) dnoc_fbaxi_checker
        (
            .d_noc_out                    (d_noc_out),
            .d_noc_out_valid              (d_noc_out_valid),

            .clk                          (clk),
            .reset_n                      (reset_n)  
        );
   
endmodule