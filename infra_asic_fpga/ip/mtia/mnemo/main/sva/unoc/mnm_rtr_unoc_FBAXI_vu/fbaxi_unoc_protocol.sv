///////////////////////////////////////////////////
/// File: fbaxi_unoc_protocol.sv
/// UNOC FBAXI protocol checker
///////////////////////////////////////////////////

module fbaxi_unoc_protocol_checker #(
    parameter int unsigned UNOC_MASTER = 1,  // = 1: master, = 0: slave
    parameter int unsigned CFG_CHK = 0,

    parameter int unsigned ASSERT_ONLY = 0,  // What is the intention of this param ?

    parameter int unsigned BURST_ON = 1
) (
    // System Signals
    clk,
    reset_n,

    unoc_resp_valid,
    unoc_resp_bundle,

    unoc_req_valid,
    unoc_req_bundle,

    //other signals
    rtr_location
);

  // System Signals
  input logic clk;
  input logic reset_n;

  input logic unoc_resp_valid;
  // input [cip_pkg::CIP_UNOC_TOTAL_NUM_VC-1:0] unoc_resp_credit_release;
  input cip_pkg::utility_noc_t unoc_resp_bundle;

  input logic unoc_req_valid;
  // input [cip_pkg::CIP_UNOC_TOTAL_NUM_VC-1:0] unoc_req_credit_release;
  input cip_pkg::utility_noc_t unoc_req_bundle;

  input cip_pkg::cip_grid_location_t rtr_location;

  // `include "cip_rtr_unoc_FBAXI_macros.sv"
  `include "unoc_properties.svh"

  genvar k;
  generate
    if (UNOC_MASTER == 1) begin : unoc_is_master

      // AXI AW+W channel

      if (BURST_ON == 1) begin
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_awvalids_in_burst_are_consecutive,
                   wvalids_in_burst_are_consecutive);
      end

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_awsize_valid, awsize_valid);
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_wlast_as_expected, wlast_as_expected);
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_awstrb_bit_set_not_greater_than_awsize,
                  awstrb_bit_set_not_greater_than_awsize);
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_awstrb_match_alignment_from_addr,
                  awstrb_match_alignment_from_addr);
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_awvalid_followed_by_wvalid,
                  awvalid_followed_by_wvalid);

      // AXI AR channel
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_req_arsize_valid, arsize_valid);


      if (ASSERT_ONLY == 0) begin : am2
        //RESP channels
        // AXI R channel

        /*@ASM The beats of the burst should be kept consecutive under UNOC.w.strb section (Page-26) @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_resp_rvalids_in_burst_are_consecutive, rvalids_in_burst_are_consecutive);

        /*@ASM R id should be kept same through out the burst for protocol compliance @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_resp_rids_in_burst_same_throughout, rids_in_burst_same_throughout);

        /*@ASM R user should be kept same through out the burst for protocol compliance @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_resp_rusers_in_burst_same_throughout, rusers_in_burst_same_throughout);

        /*@ASM R last shoule be asserted when expected for protocol compliance @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_resp_rlast_as_expected, rlast_as_expected);

      end

    end else begin : unoc_is_slave

      if (ASSERT_ONLY == 0) begin : am2
        // AXI AW+W channel

        /*@ASM The beats of the burst should be kept consecutive under UNOC.w.strb section (Page-26) @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_awvalids_in_burst_are_consecutive,
                   awvalids_in_burst_are_consecutive);

        /*@ASM There should not be more strb bit set than the size indicates (Page-27)*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_awstrb_bit_set_not_greater_than_awsize,
                    awstrb_bit_set_not_greater_than_awsize);
        /*@ASM The location of the set strobe bits should match the alignment indicated by the address*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_awstrb_match_alignment_from_addr,
                  awstrb_match_alignment_from_addr);

        /*@ASM Aw size should be in valid range (Page-26) @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_awsize_valid, awsize_valid);

        `SV_ASSERT(FVPH_RTR_FV_am_unoc_awvalid_followed_by_wvalid,
                  awvalid_followed_by_wvalid);

        /*@ASM W last shoule be asserted when expected for protocol compliance @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_wlast_as_expected, wlast_as_expected);



        // AXI AR channel

        /*@ASM Ar size should be in valid range (Page-26) @*/
        `SV_ASSERT(FVPH_RTR_FV_am_unoc_req_arsize_valid, arsize_valid);
        
      end
      // AXI R channel
      if (BURST_ON == 1) begin : burst_on

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_resp_rvalids_in_burst_are_consecutive,
                   rvalids_in_burst_are_consecutive);
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_resp_rids_in_burst_same_throughout, rids_in_burst_same_throughout);
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_resp_rusers_in_burst_same_throughout,
                   rusers_in_burst_same_throughout);
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_resp_read_resp_ttl_in_burst_same_throughout,
                   read_resp_ttl_in_burst_same_throughout);
      end

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_resp_rlast_as_expected, rlast_as_expected);

    end
  endgenerate


endmodule  // fbaxi_unoc_protocol_checker
