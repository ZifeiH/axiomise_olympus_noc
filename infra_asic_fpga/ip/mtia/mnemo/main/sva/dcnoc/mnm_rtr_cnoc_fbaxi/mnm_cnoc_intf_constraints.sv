/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_intf_constraints.sv
// This file contains mnm fbaxi constraints
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_cnoc_intf_constraints # (
  parameter DIR    = 11,
  parameter NUM_VC = 11,
  parameter LANE_NUM = 0
) (
  input     mnm_pkg::control_noc_t                         c_noc_in,
  input     logic                                          c_noc_in_valid,
  input     credit_cfg_t                                   csr_cfg,
  input     logic                [VCID_W-1:0]              c_noc_in_crd_rel_id,
  input     logic                                          c_noc_in_crd_rel_valid,
  input     mnm_pkg::control_noc_t                         c_noc_out,
  input     logic                                          c_noc_out_valid,
  input     logic                [VCID_W-1:0]              c_noc_out_crd_rel_id,
  input     logic                                          c_noc_out_crd_rel_valid,

  input     logic                                          noc_out_async_crd_release,
  input     logic                                          noc_in_async_crd_release,

  input     logic                                          clk,
  input     logic                                          reset_n
);  

    `include "mnm_cnoc_input_signal_defines.sv"
    `include "mnm_cnoc_output_signal_defines.sv"

    `SV_ASSERT (FVPH_RTR_FV_am_noc_iid_tracking         ,   c_noc_in_iid     == LANE_NUM  );
    // TODO: need to remove once tb stable
    
    `SV_ASSERT(FVPH_RTR_FV_am_group_shrd_fixed          ,   csr_cfg.vc_grp_shrd == 33'h092492449  );
 
    `SV_ASSERT (FVPH_RTR_FV_am_vc_grp_rsvd_fixed        ,   csr_cfg.vc_grp_rsvd_en     == '0                     );
    `SV_ASSERT (FVPH_RTR_FV_am_total_shrd_max_fixed     ,   csr_cfg.total_shrd_max     == 7'h2e                     );
    `SV_ASSERT (FVPH_RTR_FV_am_total_max_fixed          ,   csr_cfg.total_credits      == 7'h68                     );
    `SV_ASSERT (FVPH_RTR_FV_am_group_shrd_max_fixed     ,   csr_cfg.vc_grp_shrd_max    == 21'h0b972e                );
    `SV_ASSERT (FVPH_RTR_FV_am_group_rsvd_max_fixed     ,   csr_cfg.vc_grp_rsvd_max    == 21'h000000                );
    `SV_ASSERT (FVPH_RTR_FV_am_vc_shrd_max_fixed        ,   csr_cfg.vc_shrd_max        == 77'h0b972e5cb972e5cb972e  );
    `SV_ASSERT (FVPH_RTR_FV_am_vc_rsvd_max_fixed        ,   csr_cfg.vc_rsvd_max        == 77'h00408102040810204081  );
     

		mnm_cnoc_fbaxi_constraints # (

            .NUM_VC   (NUM_VC)

      ) cnoc_fbaxi_constraints 
      (
          .c_noc_in                    (c_noc_in),
          .c_noc_in_valid              (c_noc_in_valid),
          .clk                         (clk),
          .reset_n                     (reset_n)  
      );

    credit_manager_constraints_input # () 
    
    mnm_cnoc_credit_manager_constraints_input (

       .noc_in_len         ('b0),
       .noc_in_vc          (c_noc_in_read?c_noc_in_vc:(c_noc_in_vc+(mnm_pkg::MNM_CNOC_AR_NUM_VC))),
       .noc_in_last        ('b1),
       .noc_in_vld         (c_noc_in_valid),
       .crd_rel_vld        (c_noc_in_crd_rel_valid),
       .crd_rel_id         (c_noc_in_crd_rel_id),
       
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
    ) mnm_cnoc_credit_manager_constraints_output (

       .noc_out_len         ('b0),
       .noc_out_vc          (c_noc_out_read?c_noc_out_vc:(c_noc_out_vc+(mnm_pkg::MNM_CNOC_AR_NUM_VC))),
       .noc_out_last        ('b1),
       .noc_out_vld         (c_noc_out_valid),
       .crd_rel_vld         (c_noc_out_crd_rel_valid),
       .crd_rel_id          (c_noc_out_crd_rel_id),
       
       .vc_rsvd_max         (csr_cfg.vc_rsvd_max),       
       .vc_shrd_max         (csr_cfg.vc_shrd_max),       
       .vc_grp_rsvd_en      (csr_cfg.vc_grp_rsvd_en) ,  
       .vc_grp_rsvd_id      (csr_cfg.vc_grp_rsvd_id) ,  
       .vc_grp_rsvd_max     (csr_cfg.vc_grp_rsvd_max),   
       .vc_grp_shrd_max     (csr_cfg.vc_grp_shrd_max),   
       .vc_grp_shrd         (csr_cfg.vc_grp_shrd),   
       .total_shrd_max      (csr_cfg.total_shrd_max) ,
       .total_credits       (csr_cfg.total_credits) ,
       
       .clk                 (clk)    ,
       .reset_n             (reset_n)
    );

    if (LANE_NUM >= 8) begin: async_credit_constraints
    credit_counter_TX_sva # (
    
        .TX_CREDITS(12)
    
    ) input_credit_constraints (
    
        .noc_out_valid               (c_noc_in_crd_rel_valid),
        .noc_out_credit_release      (noc_in_async_crd_release),
      
        .noc_out_len                 ('b0),
        .noc_out_last                ('b1),
    
        .clk                         (clk),
        .reset_n                     (reset_n)
    );

    credit_counter_TX_sva # (
    
        .TX_CREDITS(12)
    
    ) output_credit_constraints (
    
        .noc_out_valid                (c_noc_out_crd_rel_valid),
        .noc_out_credit_release       (noc_out_async_crd_release),
      
        .noc_out_len                  ('b0),
        .noc_out_last                 ('b1),
    
        .clk                          (clk),
        .reset_n                      (reset_n)
    );
    end

endmodule