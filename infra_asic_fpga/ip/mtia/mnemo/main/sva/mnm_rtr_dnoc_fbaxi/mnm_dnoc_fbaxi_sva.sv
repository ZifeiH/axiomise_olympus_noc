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
    input   rtr_dc_csr_pkg::registers_for_default_inputs_struct                                  csr_out,
    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_in,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_in_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_in_valid,
    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              noc_out,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  noc_out_credit_release_id,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_credit_release_valid,
    input   logic                                                   [NUM_LANES-1:0]              noc_out_valid,
    input   mnm_pkg::mnm_grid_location_t                                                         rtr_location,
    input   logic                                                                                soc_reset_n


); 

  wire reset_n;
  assign reset_n = soc_reset_n;

  credit_cfg_t    [NUM_LANES-1:0] noc_in_config;

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

  logic                       [NUM_VC-1:0][7:0]                                        csr_cfg_dwrr_vc_weights   ;
  logic                       [NUM_LANES-1:0][NUM_LANES-1:0][7:0]                      csr_cfg_dwrr_src_weights  ;
  logic                       [NUM_LANES-1:0][NUM_VC-1:0][RX_DEPTH_W-1:0]              csr_cfg_vc_rsvd_max_th    ;
  logic                       [NUM_LANES-1:0][NUM_VC-1:0][RX_DEPTH_W-1:0]              csr_cfg_vc_shrd_max_th    ;
  logic                       [NUM_LANES-1:0][NUM_VC-1:0]                              csr_cfg_vc_group_rsvd_en  ;
  logic                       [NUM_LANES-1:0][NUM_VC-1:0][RSVD_CRD_GROUP_ID_W-1:0]     csr_cfg_vc_group_rsvd_id  ;
  logic                       [NUM_LANES-1:0][NUM_VC-1:0][NUM_SHRD_CRD_GROUPS-1:0]     csr_cfg_vc_group_shrd     ;
  logic                       [NUM_LANES-1:0][NUM_RSVD_CRD_GROUPS-1:0][RX_DEPTH_W-1:0] csr_cfg_group_rsvd_max_th ;
  logic                       [NUM_LANES-1:0][NUM_SHRD_CRD_GROUPS-1:0][RX_DEPTH_W-1:0] csr_cfg_group_shrd_max_th ;
  logic                       [NUM_LANES-1:0][RX_DEPTH_W-1:0]                          csr_cfg_total_shrd_max_th ;
  logic                       [NUM_LANES-1:0][RX_DEPTH_W-1:0]                          csr_cfg_total_credits     ;
  logic                       [NUM_VC-1:0]                                             csr_cfg_vc_y_first_routing;


  assign csr_cfg_dwrr_vc_weights     = {csr_in.dwrr_aw_vc_weights, csr_in.dwrr_r_vc_weights};
  assign csr_cfg_vc_y_first_routing  = {csr_in.vc_routing_direction_cfg.aw_vc_cfg, csr_in.vc_routing_direction_cfg.r_vc_cfg};
  assign csr_cfg_vc_group_shrd       = {NUM_LANES{ {csr_in.dnoc_wr_vc_group_cfg.vc_shared_groups, csr_in.dnoc_rd_vc_group_cfg.vc_shared_groups}}};
  assign csr_cfg_vc_group_rsvd_en    = {NUM_LANES{ {csr_in.dnoc_wr_vc_group_cfg.vc_rsvd_group_en, csr_in.dnoc_rd_vc_group_cfg.vc_rsvd_group_en}}};
  assign csr_cfg_vc_group_rsvd_id    = {NUM_LANES{ {csr_in.dnoc_wr_vc_group_cfg.vc_rsvd_group, csr_in.dnoc_rd_vc_group_cfg.vc_rsvd_group}}};
  assign csr_cfg_dwrr_src_weights = {
    csr_in.tx_peg_dwrr_src_weights_dnoc.peg,
    csr_in.tx_peg_dwrr_src_weights_dnoc.llc,
    csr_in.tx_peg_dwrr_src_weights_dnoc.llc,
    csr_in.tx_peg_dwrr_src_weights_dnoc.west,
    csr_in.tx_peg_dwrr_src_weights_dnoc.west,
    csr_in.tx_peg_dwrr_src_weights_dnoc.south,
    csr_in.tx_peg_dwrr_src_weights_dnoc.south,
    csr_in.tx_peg_dwrr_src_weights_dnoc.east,
    csr_in.tx_peg_dwrr_src_weights_dnoc.east,
    csr_in.tx_peg_dwrr_src_weights_dnoc.north,
    csr_in.tx_peg_dwrr_src_weights_dnoc.north,
    csr_in.tx_llc_dwrr_src_weights_dnoc.peg,
    csr_in.tx_llc_dwrr_src_weights_dnoc.llc,
    csr_in.tx_llc_dwrr_src_weights_dnoc.llc,
    csr_in.tx_llc_dwrr_src_weights_dnoc.west,
    csr_in.tx_llc_dwrr_src_weights_dnoc.west,
    csr_in.tx_llc_dwrr_src_weights_dnoc.south,
    csr_in.tx_llc_dwrr_src_weights_dnoc.south,
    csr_in.tx_llc_dwrr_src_weights_dnoc.east,
    csr_in.tx_llc_dwrr_src_weights_dnoc.east,
    csr_in.tx_llc_dwrr_src_weights_dnoc.north,
    csr_in.tx_llc_dwrr_src_weights_dnoc.north,
    csr_in.tx_llc_dwrr_src_weights_dnoc.peg,
    csr_in.tx_llc_dwrr_src_weights_dnoc.llc,
    csr_in.tx_llc_dwrr_src_weights_dnoc.llc,
    csr_in.tx_llc_dwrr_src_weights_dnoc.west,
    csr_in.tx_llc_dwrr_src_weights_dnoc.west,
    csr_in.tx_llc_dwrr_src_weights_dnoc.south,
    csr_in.tx_llc_dwrr_src_weights_dnoc.south,
    csr_in.tx_llc_dwrr_src_weights_dnoc.east,
    csr_in.tx_llc_dwrr_src_weights_dnoc.east,
    csr_in.tx_llc_dwrr_src_weights_dnoc.north,
    csr_in.tx_llc_dwrr_src_weights_dnoc.north,
    csr_in.tx_west_dwrr_src_weights_dnoc.peg,
    csr_in.tx_west_dwrr_src_weights_dnoc.llc,
    csr_in.tx_west_dwrr_src_weights_dnoc.llc,
    csr_in.tx_west_dwrr_src_weights_dnoc.west,
    csr_in.tx_west_dwrr_src_weights_dnoc.west,
    csr_in.tx_west_dwrr_src_weights_dnoc.south,
    csr_in.tx_west_dwrr_src_weights_dnoc.south,
    csr_in.tx_west_dwrr_src_weights_dnoc.east,
    csr_in.tx_west_dwrr_src_weights_dnoc.east,
    csr_in.tx_west_dwrr_src_weights_dnoc.north,
    csr_in.tx_west_dwrr_src_weights_dnoc.north,
    csr_in.tx_west_dwrr_src_weights_dnoc.peg,
    csr_in.tx_west_dwrr_src_weights_dnoc.llc,
    csr_in.tx_west_dwrr_src_weights_dnoc.llc,
    csr_in.tx_west_dwrr_src_weights_dnoc.west,
    csr_in.tx_west_dwrr_src_weights_dnoc.west,
    csr_in.tx_west_dwrr_src_weights_dnoc.south,
    csr_in.tx_west_dwrr_src_weights_dnoc.south,
    csr_in.tx_west_dwrr_src_weights_dnoc.east,
    csr_in.tx_west_dwrr_src_weights_dnoc.east,
    csr_in.tx_west_dwrr_src_weights_dnoc.north,
    csr_in.tx_west_dwrr_src_weights_dnoc.north,
    csr_in.tx_south_dwrr_src_weights_dnoc.peg,
    csr_in.tx_south_dwrr_src_weights_dnoc.llc,
    csr_in.tx_south_dwrr_src_weights_dnoc.llc,
    csr_in.tx_south_dwrr_src_weights_dnoc.west,
    csr_in.tx_south_dwrr_src_weights_dnoc.west,
    csr_in.tx_south_dwrr_src_weights_dnoc.south,
    csr_in.tx_south_dwrr_src_weights_dnoc.south,
    csr_in.tx_south_dwrr_src_weights_dnoc.east,
    csr_in.tx_south_dwrr_src_weights_dnoc.east,
    csr_in.tx_south_dwrr_src_weights_dnoc.north,
    csr_in.tx_south_dwrr_src_weights_dnoc.north,
    csr_in.tx_south_dwrr_src_weights_dnoc.peg,
    csr_in.tx_south_dwrr_src_weights_dnoc.llc,
    csr_in.tx_south_dwrr_src_weights_dnoc.llc,
    csr_in.tx_south_dwrr_src_weights_dnoc.west,
    csr_in.tx_south_dwrr_src_weights_dnoc.west,
    csr_in.tx_south_dwrr_src_weights_dnoc.south,
    csr_in.tx_south_dwrr_src_weights_dnoc.south,
    csr_in.tx_south_dwrr_src_weights_dnoc.east,
    csr_in.tx_south_dwrr_src_weights_dnoc.east,
    csr_in.tx_south_dwrr_src_weights_dnoc.north,
    csr_in.tx_south_dwrr_src_weights_dnoc.north,
    csr_in.tx_east_dwrr_src_weights_dnoc.peg,
    csr_in.tx_east_dwrr_src_weights_dnoc.llc,
    csr_in.tx_east_dwrr_src_weights_dnoc.llc,
    csr_in.tx_east_dwrr_src_weights_dnoc.west,
    csr_in.tx_east_dwrr_src_weights_dnoc.west,
    csr_in.tx_east_dwrr_src_weights_dnoc.south,
    csr_in.tx_east_dwrr_src_weights_dnoc.south,
    csr_in.tx_east_dwrr_src_weights_dnoc.east,
    csr_in.tx_east_dwrr_src_weights_dnoc.east,
    csr_in.tx_east_dwrr_src_weights_dnoc.north,
    csr_in.tx_east_dwrr_src_weights_dnoc.north,
    csr_in.tx_east_dwrr_src_weights_dnoc.peg,
    csr_in.tx_east_dwrr_src_weights_dnoc.llc,
    csr_in.tx_east_dwrr_src_weights_dnoc.llc,
    csr_in.tx_east_dwrr_src_weights_dnoc.west,
    csr_in.tx_east_dwrr_src_weights_dnoc.west,
    csr_in.tx_east_dwrr_src_weights_dnoc.south,
    csr_in.tx_east_dwrr_src_weights_dnoc.south,
    csr_in.tx_east_dwrr_src_weights_dnoc.east,
    csr_in.tx_east_dwrr_src_weights_dnoc.east,
    csr_in.tx_east_dwrr_src_weights_dnoc.north,
    csr_in.tx_east_dwrr_src_weights_dnoc.north,
    csr_in.tx_north_dwrr_src_weights_dnoc.peg,
    csr_in.tx_north_dwrr_src_weights_dnoc.llc,
    csr_in.tx_north_dwrr_src_weights_dnoc.llc,
    csr_in.tx_north_dwrr_src_weights_dnoc.west,
    csr_in.tx_north_dwrr_src_weights_dnoc.west,
    csr_in.tx_north_dwrr_src_weights_dnoc.south,
    csr_in.tx_north_dwrr_src_weights_dnoc.south,
    csr_in.tx_north_dwrr_src_weights_dnoc.east,
    csr_in.tx_north_dwrr_src_weights_dnoc.east,
    csr_in.tx_north_dwrr_src_weights_dnoc.north,
    csr_in.tx_north_dwrr_src_weights_dnoc.north,
    csr_in.tx_north_dwrr_src_weights_dnoc.peg,
    csr_in.tx_north_dwrr_src_weights_dnoc.llc,
    csr_in.tx_north_dwrr_src_weights_dnoc.llc,
    csr_in.tx_north_dwrr_src_weights_dnoc.west,
    csr_in.tx_north_dwrr_src_weights_dnoc.west,
    csr_in.tx_north_dwrr_src_weights_dnoc.south,
    csr_in.tx_north_dwrr_src_weights_dnoc.south,
    csr_in.tx_north_dwrr_src_weights_dnoc.east,
    csr_in.tx_north_dwrr_src_weights_dnoc.east,
    csr_in.tx_north_dwrr_src_weights_dnoc.north,
    csr_in.tx_north_dwrr_src_weights_dnoc.north};
  assign csr_cfg_vc_rsvd_max_th = {
   csr_in.peg_dnoc_wr_vc_reserved_threshold, csr_in.peg_dnoc_rd_vc_reserved_threshold,
   csr_in.llc_dnoc_wr_vc_reserved_threshold, csr_in.llc_dnoc_rd_vc_reserved_threshold,
   csr_in.llc_dnoc_wr_vc_reserved_threshold, csr_in.llc_dnoc_rd_vc_reserved_threshold,
   csr_in.west_dnoc_wr_vc_reserved_threshold, csr_in.west_dnoc_rd_vc_reserved_threshold,
   csr_in.west_dnoc_wr_vc_reserved_threshold, csr_in.west_dnoc_rd_vc_reserved_threshold,
   csr_in.south_dnoc_wr_vc_reserved_threshold, csr_in.south_dnoc_rd_vc_reserved_threshold,
   csr_in.south_dnoc_wr_vc_reserved_threshold, csr_in.south_dnoc_rd_vc_reserved_threshold,
   csr_in.east_dnoc_wr_vc_reserved_threshold, csr_in.east_dnoc_rd_vc_reserved_threshold,
   csr_in.east_dnoc_wr_vc_reserved_threshold, csr_in.east_dnoc_rd_vc_reserved_threshold,
   csr_in.north_dnoc_wr_vc_reserved_threshold, csr_in.north_dnoc_rd_vc_reserved_threshold,
   csr_in.north_dnoc_wr_vc_reserved_threshold, csr_in.north_dnoc_rd_vc_reserved_threshold};
  assign csr_cfg_vc_shrd_max_th = {
   csr_in.peg_dnoc_wr_vc_shared_threshold, csr_in.peg_dnoc_rd_vc_shared_threshold,
   csr_in.llc_dnoc_wr_vc_shared_threshold, csr_in.llc_dnoc_rd_vc_shared_threshold,
   csr_in.llc_dnoc_wr_vc_shared_threshold, csr_in.llc_dnoc_rd_vc_shared_threshold,
   csr_in.west_dnoc_wr_vc_shared_threshold, csr_in.west_dnoc_rd_vc_shared_threshold,
   csr_in.west_dnoc_wr_vc_shared_threshold, csr_in.west_dnoc_rd_vc_shared_threshold,
   csr_in.south_dnoc_wr_vc_shared_threshold, csr_in.south_dnoc_rd_vc_shared_threshold,
   csr_in.south_dnoc_wr_vc_shared_threshold, csr_in.south_dnoc_rd_vc_shared_threshold,
   csr_in.east_dnoc_wr_vc_shared_threshold, csr_in.east_dnoc_rd_vc_shared_threshold,
   csr_in.east_dnoc_wr_vc_shared_threshold, csr_in.east_dnoc_rd_vc_shared_threshold,
   csr_in.north_dnoc_wr_vc_shared_threshold, csr_in.north_dnoc_rd_vc_shared_threshold,
   csr_in.north_dnoc_wr_vc_shared_threshold, csr_in.north_dnoc_rd_vc_shared_threshold};
  assign csr_cfg_group_rsvd_max_th = {
    csr_in.peg_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.llc_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.llc_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.west_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.west_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.south_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.south_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.east_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.east_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.north_dnoc_credit_groups_threshold.rsvd_group,
    csr_in.north_dnoc_credit_groups_threshold.rsvd_group};
  assign csr_cfg_group_shrd_max_th = {
    csr_in.peg_dnoc_credit_groups_threshold.shrd_group,
    csr_in.llc_dnoc_credit_groups_threshold.shrd_group,
    csr_in.llc_dnoc_credit_groups_threshold.shrd_group,
    csr_in.west_dnoc_credit_groups_threshold.shrd_group,
    csr_in.west_dnoc_credit_groups_threshold.shrd_group,
    csr_in.south_dnoc_credit_groups_threshold.shrd_group,
    csr_in.south_dnoc_credit_groups_threshold.shrd_group,
    csr_in.east_dnoc_credit_groups_threshold.shrd_group,
    csr_in.east_dnoc_credit_groups_threshold.shrd_group,
    csr_in.north_dnoc_credit_groups_threshold.shrd_group,
    csr_in.north_dnoc_credit_groups_threshold.shrd_group};
  assign csr_cfg_total_shrd_max_th = {
    csr_in.peg_dnoc_total_shared_threshold.shrd_total,
    csr_in.llc_dnoc_total_shared_threshold.shrd_total,
    csr_in.llc_dnoc_total_shared_threshold.shrd_total,
    csr_in.west_dnoc_total_shared_threshold.shrd_total,
    csr_in.west_dnoc_total_shared_threshold.shrd_total,
    csr_in.south_dnoc_total_shared_threshold.shrd_total,
    csr_in.south_dnoc_total_shared_threshold.shrd_total,
    csr_in.east_dnoc_total_shared_threshold.shrd_total,
    csr_in.east_dnoc_total_shared_threshold.shrd_total,
    csr_in.north_dnoc_total_shared_threshold.shrd_total,
    csr_in.north_dnoc_total_shared_threshold.shrd_total};
  assign csr_cfg_total_credits = {
    csr_in.peg_dnoc_link_stats.total_credits_available,
    csr_in.llc_dnoc_link_stats.total_credits_available,
    csr_in.llc_dnoc_link_stats.total_credits_available,
    csr_in.west_dnoc_link_stats.total_credits_available,
    csr_in.west_dnoc_link_stats.total_credits_available,
    csr_in.south_dnoc_link_stats.total_credits_available,
    csr_in.south_dnoc_link_stats.total_credits_available,
    csr_in.east_dnoc_link_stats.total_credits_available,
    csr_in.east_dnoc_link_stats.total_credits_available,
    csr_in.north_dnoc_link_stats.total_credits_available,
    csr_in.north_dnoc_link_stats.total_credits_available};

`ifdef FORMAL

    `SV_ASSERT (FVPH_RTR_FV_am_rtr_location_stable       , ##1 $stable(rtr_location)                               );
    `SV_ASSERT (FVPH_RTR_FV_am_vc_y_first_routing_fixed  , csr_cfg_vc_y_first_routing == 11'h1fc                   );
    `SV_ASSERT (FVPH_RTR_FV_am_dwrr_vc_weights_fixed     , csr_cfg_dwrr_vc_weights    == 88'h0202020202020202020202);

        generate
            
            begin: dwrr_vc_weights
            
            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: per_lane
                if (!REMOVE_LANE[lane]) begin
                    for (genvar vc = 0 ; vc < NUM_VC ; vc++) begin: per_vc
                
                        `SV_ASSERT (FVPH_RTR_FV_am_dwrr_src_weights_fixed  , csr_cfg_dwrr_src_weights[lane][vc] == 8'h02);
                
                    end 
                end
            
            end
            
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_constraints
                if (!REMOVE_LANE[lane]) begin

                    assign noc_in_config[lane].vc_rsvd_max     = csr_cfg_vc_rsvd_max_th[lane]    ;
                    assign noc_in_config[lane].vc_shrd_max     = csr_cfg_vc_shrd_max_th[lane]    ;
                    assign noc_in_config[lane].vc_grp_rsvd_en  = csr_cfg_vc_group_rsvd_en[lane]  ;
                    assign noc_in_config[lane].vc_grp_rsvd_id  = csr_cfg_vc_group_rsvd_id[lane]  ;
                    assign noc_in_config[lane].vc_grp_rsvd_max = csr_cfg_group_rsvd_max_th[lane]     ;
                    assign noc_in_config[lane].vc_grp_shrd_max = csr_cfg_group_shrd_max_th[lane] ;
                    assign noc_in_config[lane].vc_grp_shrd     = csr_cfg_vc_group_shrd[lane] ;
                    assign noc_in_config[lane].total_shrd_max  = csr_cfg_total_shrd_max_th[lane] ;
                    assign noc_in_config[lane].total_credits   = csr_cfg_total_credits[lane]     ; 

                    mnm_dnoc_fbaxi_intf_constraints #(
                        .NUM_VC                          (NUM_VC),
                        .LANE_NUM                        (lane)
                    ) mnm_dnoc_fbaxi_intf_constraints (

                        .d_noc_in                        (noc_in[lane]),
                        .d_noc_in_valid                  (noc_in_valid[lane]),
                        .csr_cfg                         (noc_in_config[lane]),
                        .d_noc_in_crd_rel_id             (noc_in_credit_release_id[lane]),
                        .d_noc_in_crd_rel_valid          (noc_in_credit_release_valid[lane]),
                        .d_noc_out                       (noc_out[lane]),
                        .d_noc_out_valid                 (noc_out_valid[lane]),
                        .d_noc_out_crd_rel_id            (noc_out_credit_release_id[lane]),
                        .d_noc_out_crd_rel_valid         (noc_out_credit_release_valid[lane]),
                        
                        .clk                             (clk),
                        .reset_n                         (reset_n)
                    );    
                end               
                
            end

            for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: intf_checkers
                if (!REMOVE_LANE[lane]) begin

                    mnm_dnoc_fbaxi_checker #(
                        .NUM_VC                           (NUM_VC)
                    ) mnm_dnoc_fbaxi_checker (

                        .d_noc_out                        (noc_out[lane]),
                        .d_noc_out_valid                  (noc_out_valid[lane]),

                        .clk                              (clk),
                        .reset_n                          (reset_n)

                    ); 
                end
            end
        endgenerate
    `endif
    
//------------------------------------------------------------------------------
//-- Flow Control --
//------------------------------------------------------------------------------

// If convergence needed will apply



endmodule
