///////////////////////////////////////////////////
/// File: cip_rtr_unoc_credit_release_sva.sv
/// This file contains the assumptions related to credit_release
///////////////////////////////////////////////////

module cip_rtr_unoc_credit_release_sva # (

            parameter   SIDE                       = 0,
            parameter   RTR_MINI_REQUESTER_NUM_VC  = cip_pkg::CIP_UNOC_TOTAL_NUM_VC,
            parameter   GEN_RX_ASM                 = 1,
            parameter   GEN_TX_ASM                 = 1
            
) (

  input     cip_pkg::utility_noc_t                         u_noc_in,
  input     logic   [RTR_MINI_REQUESTER_NUM_VC-1:0]        u_noc_in_credit_release,
  input     logic                                          u_noc_in_valid,

  input     cip_pkg::utility_noc_t                         u_noc_out,
  input     logic   [RTR_MINI_REQUESTER_NUM_VC-1:0]        u_noc_out_credit_release,
  input     logic                                          u_noc_out_valid,

  input     logic                                          clk,
  input     logic                                          reset_n

);

  `define read_req    cip_pkg::UNOC_CHANNEL_E_READ_REQ;
  `define write_req   cip_pkg::UNOC_CHANNEL_E_WRITE_REQ;
  `define write_resp  cip_pkg::UNOC_CHANNEL_E_WRITE_RESP;
  `define read_resp   cip_pkg::UNOC_CHANNEL_E_READ_RESP;

//------------------------------------------------------------------------------
//-- Credits for interfrace --
//------------------------------------------------------------------------------

    `include "cip_rtr_unoc_FBAXI_signal_defines.sv"

   localparam UNOC_AW_W_R_CRED_RX                    = (SIDE == cip_rtr_pkg::UNOC_DIR_WEST)    ?  cip_pkg::CIP_RTR_EW_INTF_AW_W_R_CREDITS_UNOC    : 
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_EAST)    ?  cip_pkg::CIP_RTR_EW_INTF_AW_W_R_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_NORTH)   ?  cip_pkg::CIP_RTR_NS_INTF_AW_W_R_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_SOUTH)   ?  cip_pkg::CIP_RTR_NS_INTF_AW_W_R_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_LEAF0)   ?  cip_pkg::CIP_RTR_FI_INTF_AW_W_R_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_LEAF1)   ?  cip_pkg::CIP_RTR_FI_INTF_AW_W_R_CREDITS_UNOC    :
                                                       '0;

   localparam UNOC_AR_B_CRED_RX                      = (SIDE == cip_rtr_pkg::UNOC_DIR_WEST)    ?  cip_pkg::CIP_RTR_EW_INTF_AR_B_CREDITS_UNOC    : 
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_EAST)    ?  cip_pkg::CIP_RTR_EW_INTF_AR_B_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_NORTH)   ?  cip_pkg::CIP_RTR_NS_INTF_AR_B_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_SOUTH)   ?  cip_pkg::CIP_RTR_NS_INTF_AR_B_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_LEAF0)   ?  cip_pkg::CIP_RTR_FI_INTF_AR_B_CREDITS_UNOC    :
                                                       (SIDE == cip_rtr_pkg::UNOC_DIR_LEAF1)   ?  cip_pkg::CIP_RTR_FI_INTF_AR_B_CREDITS_UNOC    :
                                                       '0;

//------------------------------------------------------------------------------
//-- Credit Based Flow Control Checker --
//------------------------------------------------------------------------------ 

    generate if (GEN_RX_ASM) begin: rx_credit_checker
        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_AR_NUM_VC; i++ ) begin: ar_req
            credit_counter_RX_sva # (

                .RX_CREDITS(UNOC_AR_B_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) rx_credit_checker (

                .noc_in_valid              (u_noc_in_valid && unoc_in_is_AR_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_in_credit_release     (u_noc_in_credit_release[i]),
                
                .noc_in_len                ('0),
                .noc_in_last               ('1),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_AWW_NUM_VC; i++ ) begin: aw_req
            credit_counter_RX_sva # (

                .RX_CREDITS(UNOC_AW_W_R_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) rx_credit_checker (

                .noc_in_valid              (u_noc_in_valid && unoc_in_is_AW_W_channel && u_noc_in_AW_W_vc == i),
                .noc_in_credit_release     (u_noc_in_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC]),
                
                .noc_in_len                (unoc_in_awlen),
                .noc_in_last               (unoc_in_wlast),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_R_NUM_VC; i++ ) begin: r_resp
            credit_counter_RX_sva # (

                .RX_CREDITS(UNOC_AW_W_R_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) rx_credit_checker (

                .noc_in_valid              (u_noc_in_valid && unoc_in_is_R_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_in_credit_release     (u_noc_in_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC+cip_pkg::CIP_UNOC_AWW_NUM_VC]),
                
                .noc_in_len                (unoc_in_rlen),
                .noc_in_last               (unoc_in_rlast),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_B_NUM_VC; i++ ) begin: b_resp
            credit_counter_RX_sva # (

                .RX_CREDITS(UNOC_AR_B_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) rx_credit_checker (

                .noc_in_valid              (u_noc_in_valid && unoc_in_is_B_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_in_credit_release     (u_noc_in_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC+cip_pkg::CIP_UNOC_AWW_NUM_VC+cip_pkg::CIP_UNOC_R_NUM_VC]),
                
                .noc_in_len                ('0),
                .noc_in_last               ('1),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

    end 
    endgenerate


    generate if (GEN_TX_ASM) begin: tx_credit_checker
        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_AR_NUM_VC; i++ ) begin: ar_req
            credit_counter_TX_sva # (

                .TX_CREDITS(UNOC_AR_B_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) tx_credit_checker (

                .noc_out_valid             (u_noc_out_valid && unoc_out_is_AR_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_out_credit_release    (u_noc_out_credit_release[i]),

                .noc_out_len               ('0),
                .noc_out_last              ('1),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_AWW_NUM_VC; i++ ) begin: aw_req
            credit_counter_TX_sva # (

                .TX_CREDITS(UNOC_AW_W_R_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) tx_credit_checker (

                .noc_out_valid             (u_noc_out_valid && unoc_out_is_AW_W_channel && u_noc_out_AW_W_vc == i ),
                .noc_out_credit_release    (u_noc_out_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC]),

                .noc_out_len               (unoc_out_awlen),
                .noc_out_last              (unoc_out_wlast),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_R_NUM_VC; i++ ) begin: r_resp
            credit_counter_TX_sva # (

                .TX_CREDITS(UNOC_AW_W_R_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) tx_credit_checker (

                .noc_out_valid             (u_noc_out_valid && unoc_out_is_R_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_out_credit_release    (u_noc_out_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC+cip_pkg::CIP_UNOC_AWW_NUM_VC]),
                
                .noc_out_len               (unoc_out_rlen),
                .noc_out_last              (unoc_out_rlast),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end

        for (genvar i = 0 ; i < cip_pkg::CIP_UNOC_B_NUM_VC; i++ ) begin: b_resp
            credit_counter_TX_sva # (

                .TX_CREDITS(UNOC_AR_B_CRED_RX),
                .LEN_WIDTH (cip_pkg::CIP_UAXI_ID_LEN_WIDTH)

            ) tx_credit_checker (

                .noc_out_valid             (u_noc_out_valid && unoc_out_is_B_channel), // Not gonna add if vc is only one ( && unoc_in_vc == i )
                .noc_out_credit_release    (u_noc_out_credit_release[i+cip_pkg::CIP_UNOC_AR_NUM_VC+cip_pkg::CIP_UNOC_AWW_NUM_VC+cip_pkg::CIP_UNOC_R_NUM_VC]),
                
                .noc_out_len               ('0),
                .noc_out_last              ('1),

                .clk                       (clk),
                .reset_n                   (reset_n)
            );
            end
        
    end
    endgenerate


  endmodule