/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_dnoc_FBAXI_constraints.sv
// This file contains cip router fbaxi constrains
/////////////////////////////////////////////////////////////////////////////////////////
module cip_rtr_dnoc_FBAXI_constraints # (
    parameter GEN_AW_W_ASM = 1,
    parameter GEN_R_ASM    = 1
) (

    input   cip_pkg::data_noc_t         d_noc_in,
    input   logic                       d_noc_in_valid,

    input   logic                       clk,
    input   logic                       reset_n
    
);

    `include "dnoc_properties.svh"

    //------------------------------------------------------------------------------
    //-- FBAXI Constraints --
    //------------------------------------------------------------------------------

    // AXI AW+W channel
    if (GEN_AW_W_ASM) begin: fbaxi_aw_channel

        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awvalids_in_burst_are_consecutive, d_noc_in_valid && d_noc_in_is_AW_W_channel .....);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awaddrs_in_burst_same_throughout,  awaddrs_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awcaches_in_burst_same_throughout, awcaches_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlocks_in_burst_same_throughout,  awlocks_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awids_in_burst_same_throughout,    awids_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlens_in_burst_same_throughout,   awlens_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awusers_in_burst_same_throughout,  awusers_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wusers_in_burst_same_throughout,   wusers_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wlast_as_expected,                 wlast_as_expected);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_ttl_in_burst_same_throughout,      dnoc_ttl_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_block_illegal_ext_awtgids,         !external_illegal_awtgids);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_block_illegal_aw_z_coord,          valid_aw_z_coord);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awtgtid_coords_within_grid,        awtgtid_coords_within_grid);

    end

    if (GEN_R_ASM) begin: fbaxi_r_channel

        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rvalids_in_burst_are_consecutive, rvalids_in_burst_are_consecutive);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rids_in_burst_same_throughout,    rids_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlens_in_burst_same_throughout,   rlens_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rusers_in_burst_same_throughout,  rusers_in_burst_same_throughout);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlast_as_expected,                rlast_as_expected);

        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rtgtid_coords_within_grid,        rtgtid_coords_within_grid);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rcc_opcode_is_legal,              rcc_opcode_is_legal);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rcc_lane_is_legal_row,            rcc_lane_is_legal_row);
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rcc_lane_is_legal_column,         rcc_lane_is_legal_column);

    end

endmodule