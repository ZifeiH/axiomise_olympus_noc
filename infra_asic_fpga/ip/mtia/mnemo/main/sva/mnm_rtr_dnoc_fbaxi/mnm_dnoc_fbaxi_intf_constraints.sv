/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_intf_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_fbaxi_intf_constraints # (
  parameter DIR    = 11,
  parameter NUM_VC = 11,
  parameter LANE_NUM = 0
) (
  input     mnm_pkg::data_noc_t                            d_noc_in,
  input     logic                                          d_noc_in_valid,
  input     credit_cfg_t                                   csr_cfg,
  input     logic                [$clog2(NUM_VC)-1:0]      d_noc_in_crd_rel_id,
  input     logic                                          d_noc_in_crd_rel_valid,

  input     mnm_pkg::data_noc_t                            d_noc_out,
  input     logic                                          d_noc_out_valid,
  input     credit_cfg_t                                   d_noc_out_cfg,
  input     logic                [$clog2(NUM_VC)-1:0]      d_noc_out_crd_rel_id,
  input     logic                                          d_noc_out_crd_rel_valid,

  input     logic                                          clk,
  input     logic                                          reset_n
);  

  `include "mnm_dnoc_input_signal_defines.sv"
  `include "mnm_dnoc_output_signal_defines.sv"

    `SV_ASSERT (FVPH_RTR_FV_am_noc_iid_tracking         ,   d_noc_in_iid     == LANE_NUM  );
    
    `SV_ASSERT(FVPH_RTR_FV_am_group_shrd_fixed         ,    csr_cfg.vc_grp_shrd == 33'h092492449  );

    `SV_ASSERT (FVPH_RTR_FV_am_vc_grp_rsvd_fixed        ,   csr_cfg.vc_grp_rsvd_en     == '0                     );
    `SV_ASSERT (FVPH_RTR_FV_am_total_shrd_max_fixed     ,   csr_cfg.total_shrd_max     == 8'h35                     );
    `SV_ASSERT (FVPH_RTR_FV_am_total_max_fixed          ,   csr_cfg.total_credits      == 8'h80                     );
    `SV_ASSERT (FVPH_RTR_FV_am_group_shrd_max_fixed     ,   csr_cfg.vc_grp_shrd_max    == 24'h353535                );
    `SV_ASSERT (FVPH_RTR_FV_am_group_rsvd_max_fixed     ,   csr_cfg.vc_grp_rsvd_max    == 24'h000000                );
    `SV_ASSERT (FVPH_RTR_FV_am_vc_shrd_max_fixed        ,   csr_cfg.vc_shrd_max        == 88'h3535353535353535353535);
    `SV_ASSERT (FVPH_RTR_FV_am_vc_rsvd_max_fixed        ,   csr_cfg.vc_rsvd_max        == 88'h0202020202020202020202);
     

		mnm_dnoc_fbaxi_constraints # (

            .NUM_VC   (NUM_VC)

      ) dnoc_fbaxi_constraints 
      (
          .d_noc_in                    (d_noc_in),
          .d_noc_in_valid              (d_noc_in_valid),
          .clk                         (clk),
          .reset_n                     (reset_n)  
      );

    credit_manager_constraints_input # () 
    
    mnm_dnoc_credit_manager_constraints_input (

       .noc_in_len         (d_noc_in_is_AW_W_channel?d_noc_in_awlen:d_noc_in_rlen),
       .noc_in_vc          (d_noc_in_read?d_noc_in_vc:(d_noc_in_vc+'d3)),
       .noc_in_last        (d_noc_in_last),
       .noc_in_vld         (d_noc_in_valid),
       .crd_rel_vld        (d_noc_in_crd_rel_valid),
       .crd_rel_id         (d_noc_in_crd_rel_id),
       
       .vc_rsvd_max        (csr_cfg.vc_rsvd_max),       
       .vc_shrd_max        (csr_cfg.vc_shrd_max),       
       .vc_grp_rsvd_en     (csr_cfg.vc_grp_rsvd_en) ,  
       .vc_grp_rsvd_id     (csr_cfg.vc_grp_rsvd_id) ,  
       .vc_grp_rsvd_max    (csr_cfg.vc_grp_rsvd_max),   
       .vc_grp_shrd_max    (csr_cfg.vc_grp_shrd_max),   
       .vc_grp_shrd        (csr_cfg.vc_grp_shrd),   
       .total_shrd_max     (csr_cfg.total_shrd_max) ,
       .total_credits      (csr_cfg.total_credits) ,
       
       .clk                (clk)    ,
       .reset_n            (reset_n)
    );

    credit_manager_constraints_output # (
       .NUM_VC(NUM_VC)
    ) mnm_dnoc_credit_manager_constraints_output (

       .noc_out_len         (d_noc_out_is_AW_W_channel?d_noc_out_awlen:d_noc_out_rlen),
       .noc_out_vc          (d_noc_out_read?d_noc_out_vc:(d_noc_out_vc+'d3)),
       .noc_out_last        (d_noc_out_last),
       .noc_out_vld         (d_noc_out_valid),
       .crd_rel_vld         (d_noc_out_crd_rel_valid),
       .crd_rel_id          (d_noc_out_crd_rel_id),
       
       .vc_rsvd_max         (csr_cfg.vc_rsvd_max),       
       .vc_shrd_max         (csr_cfg.vc_shrd_max),       
       .vc_grp_rsvd_en      (csr_cfg.vc_grp_rsvd_en) ,  
       .vc_grp_rsvd_id      (csr_cfg.vc_grp_rsvd_id) ,  
       .vc_grp_rsvd_max     (csr_cfg.vc_grp_rsvd_max),   
       .vc_grp_shrd_max     (csr_cfg.vc_grp_shrd_max),   
       .vc_grp_shrd         (csr_cfg.vc_grp_shrd),   
       .total_shrd_max      (csr_cfg.total_shrd_max) ,
       .total_credits       (csr_cfg.total_credits) ,
       
       .clk                (clk)    ,
       .reset_n            (reset_n)
    );
endmodule