/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_intf_checker.sv
// This file contains mnm fbaxi checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_intf_checker # (
  parameter NUM_VC = 11
) (
  input     mnm_pkg::data_noc_t                            d_noc_out,
  input     logic                                          d_noc_out_valid,

  input     logic                                          clk,
  input     logic                                          reset_n
);  

  `include "mnm_dnoc_output_signal_defines.sv"

		mnm_dnoc_fbaxi_checker # (

            .NUM_VC   (NUM_VC)

    ) dnoc_fbaxi_checker (
            .d_noc_out                    (d_noc_out),
            .d_noc_out_valid              (d_noc_out_valid),

            .clk                          (clk),
            .reset_n                      (reset_n)  
    );


    // credit_manager_constraints # (
    //    .NUM_VC(NUM_VC)
    // ) mnm_dnoc_credit_manager_constraints (
    //    .noc_out_len        (d_noc_out_is_AW_W_channel?d_noc_out_awlen:d_noc_out_rlen),
    //    .noc_out_vc         (d_noc_out_vc),
    //    .noc_out_last       (d_noc_out_last),
    //    .noc_out_vld        (d_noc_out_credit_release_id),
       
    //    .crd_rel_vld        (d_noc_out_crd_rel_valid),
    //    .crd_rel_id         (d_noc_out_crd_rel_id),
       
    //    .vc_rsvd_max        (d_noc_out_cfg.vc_rsvd_max),       
    //    .vc_shrd_max        (d_noc_out_cfg.vc_shrd_max),       
    //    .vc_grp_rsvd_en     (d_noc_out_cfg.vc_grp_rsvd_en) ,  
    //    .vc_grp_rsvd_id     (d_noc_out_cfg.vc_grp_rsvd_id) ,  
    //    .vc_grp_rsvd_max    (d_noc_out_cfg.vc_grp_rsvd_max),   
    //    .vc_grp_shrd_max    (d_noc_out_cfg.vc_grp_shrd_max),   
    //    .vc_grp_shrd        (d_noc_out_cfg.vc_grp_shrd),   
    //    .total_shrd_max     (d_noc_out_cfg.total_shrd_max) ,
    //    .total_credits      (d_noc_out_cfg.total_credits) ,
       
    //    .clk                (clk)    ,
    //    .reset_n            (reset_n)
    // );
   
endmodule