/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_fbaxi_intf_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_cnoc_fbaxi_intf_constraints # (
  parameter NUM_VC = 11
) (
  input     mnm_pkg::control_noc_t                         c_noc_in,
  input     logic                                          c_noc_in_valid,
  // input     logic                                          c_noc_in_config,

  input     logic                                          clk,
  input     logic                                          reset_n
);  
        // mnm_rtr_cnoc_credit_release_sva #(

        //     .SIDE                           (SIDE),
        //     .GEN_RX_AW_W_ASM                (!EW_EDGE_LLC_TRAFFIC),
        //     .GEN_TX_R_ASM                   (!EW_EDGE_LLC_TRAFFIC && !NO_R_OUT),
        //     .GEN_RX_ASM                     (!VOID_LEAF_INPUT)

        // ) mnm_rtr_cnoc_credit_checker_sva (
        //     .c_noc_in                       (c_noc_in),
        //     .c_noc_in_credit_release        (c_noc_in_credit_release),
        //     .c_noc_in_valid                 (c_noc_in_valid),

        //     .c_noc_out                      (c_noc_out),
        //     .c_noc_out_credit_release       (c_noc_out_credit_release),
        //     .c_noc_out_valid                (c_noc_out_valid),

        //     .clk                            (clk),
        //     .reset_n                        (reset_n)
        // );
        
		mnm_cnoc_fbaxi_constraints # (

            .NUM_VC   (NUM_VC)

        ) cnoc_fbaxi_constraints 
        (
            .c_noc_in                    (c_noc_in),
            .c_noc_in_valid              (c_noc_in_valid),

            .clk                         (clk),
            .reset_n                     (reset_n)  
        );
   
endmodule