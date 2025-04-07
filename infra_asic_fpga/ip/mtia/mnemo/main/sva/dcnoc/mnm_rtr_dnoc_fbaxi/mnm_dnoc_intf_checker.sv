/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_fbaxi_intf_checker.sv
// This file contains mnm fbaxi checker
/////////////////////////////////////////////////////////////////////////////////////////
module mnm_dnoc_intf_checker # (
  parameter NUM_LANES           = mnm_rtr_pkg::MNM_RTR_DNOC_SLICE_NUM_LANES,
            NUM_VC              = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC,
            VCID_W              = mnm_rtr_pkg::MNM_RTR_DNOC_VCID_W,
            RX_DEPTH_W          = mnm_rtr_pkg::MNM_RTR_DNOC_RX_DEPTH_W,
            NUM_SHRD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS,
            NUM_RSVD_CRD_GROUPS = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS,
            RSVD_CRD_GROUP_ID_W = $clog2(NUM_RSVD_CRD_GROUPS),
            REMOVE_LANE         = {NUM_LANES{1'b0}}
) (
    input   logic                                                                                reset_n,
    input   logic                                                                                clk,
    input   rtr_dc_csr_pkg::registers_for_default_struct                                         csr_in,
    input   rtr_dc_csr_pkg::registers_for_default_inputs_struct                                  csr_out,

    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              d_noc_in,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_in_valid,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  d_noc_in_crd_rel_id,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_in_crd_rel_valid,

    input   mnm_pkg::data_noc_t                                     [NUM_LANES-1:0]              d_noc_out,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_out_valid,
    input   logic                                                   [NUM_LANES-1:0][VCID_W-1:0]  d_noc_out_crd_rel_id,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_out_crd_rel_valid,

    input   mnm_pkg::mnm_grid_location_t                                                         d_noc_rtr_location,

    input   logic                                                   [NUM_LANES-1:0]              d_noc_in_async_crd_release,
    input   logic                                                   [NUM_LANES-1:0]              d_noc_out_async_crd_release

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

    assign { slice_d_noc_hcb_in  ,
             slice_d_noc_llc_in  ,
             slice_d_noc_west_in ,
             slice_d_noc_south_in,
             slice_d_noc_east_in ,
             slice_d_noc_north_in} = d_noc_in;

    assign { slice_d_noc_hcb_in_valid  ,
             slice_d_noc_llc_in_valid  ,
             slice_d_noc_west_in_valid ,
             slice_d_noc_south_in_valid,
             slice_d_noc_east_in_valid ,
             slice_d_noc_north_in_valid} = d_noc_in_valid;

    assign { slice_d_noc_hcb_out  ,
             slice_d_noc_llc_out  ,
             slice_d_noc_west_out ,
             slice_d_noc_south_out,
             slice_d_noc_east_out ,
             slice_d_noc_north_out} = d_noc_out;

    assign { slice_d_noc_hcb_out_valid  ,
             slice_d_noc_llc_out_valid  ,
             slice_d_noc_west_out_valid ,
             slice_d_noc_south_out_valid,
             slice_d_noc_east_out_valid ,
             slice_d_noc_north_out_valid} = d_noc_out_valid;
        


    // `SV_ASSERT (FVPH_RTR_FV_am_noc_iid_tracking         ,   d_noc_in_iid     == LANE_NUM  );
    // TODO: need to remove once tb stable
    // `SV_ASSERT (FVPH_RTR_FV_am_noc_rd_vc_valid_range    ,   d_noc_in_is_r_channel   |-> d_noc_in_vc < mnm_pkg::MNM_CNOC_R_NUM_VC   );
    // `SV_ASSERT (FVPH_RTR_FV_am_noc_wr_vc_valid_range    ,   d_noc_in_is_aww_channel |-> d_noc_in_vc < mnm_pkg::MNM_DNOC_AWW_NUM_VC );
    
	for (genvar lane = 0; lane < NUM_LANES; lane++ ) begin: fbaxi_intf_checkers
    	if (!REMOVE_LANE[lane]) begin
          	mnm_dnoc_fbaxi_checker #(
        		.NUM_VC                           (NUM_VC)
        	) mnm_dnoc_fbaxi_checker (

            .d_noc_out                        (d_noc_out[lane]),
            .d_noc_out_valid                  (d_noc_out_valid[lane]),

            .clk                              (clk),
            .reset_n                          (reset_n)

            ); 
        end
    end

    if (!REMOVE_LANE[north0] && !REMOVE_LANE[east0]) begin: n2e_checker
		mnm_dnoc_routing_checker #(
            .NUM_LANES                        (NUM_LANES),
            .NUM_VC                           (NUM_VC),
            .RX_DEPTH_W                       (RX_DEPTH_W),
            .NUM_SHRD_CRD_GROUPS              (NUM_SHRD_CRD_GROUPS),
            .NUM_RSVD_CRD_GROUPS              (NUM_RSVD_CRD_GROUPS),
            .RSVD_CRD_GROUP_ID_W              (RSVD_CRD_GROUP_ID_W)
        ) mnm_dnoc_routing_checker(
          	.d_noc_in             (d_noc_in[north0]),
          	.d_noc_in_valid       (d_noc_in_valid[north0]),

          	.d_noc_out            (d_noc_out[east0]),
         	.d_noc_out_valid      (d_noc_out_valid[east0]),

        	.clk                  (clk),
          	.reset_n              (reset_n)
    	);
	end
   
endmodule