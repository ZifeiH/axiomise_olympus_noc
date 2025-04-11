/////////////////////////////////////////////////////////////////////////////////////////
// File: ca_arb_checker_sva.sv
/////////////////////////////////////////////////////////////////////////////////////////
module ca_arb_checker_sva #(
    parameter N                     = 4,
    parameter LW                    = 4,
    parameter WW                    = 4,
    parameter ALLOW_GRANT_SWITCH    = 1,
    parameter GRANT_POWER_OPT       = 0,
    parameter ALLOW_GRANT_SWITCH_RR = 0,
    parameter N_RR                  = 0
)(
    input                  clk,     // clock
    input                  reset_n, // async reset

    input  [N-1:0]         rtr_dwrr_req,     // arbitration request
    input  [N-1:0][LW-1:0] rtr_dwrr_req_max_len, // arbitration request
    input  [N-1:0][LW-1:0] rtr_dwrr_req_len_cmp, // request length compensation
    input  [N-1:0][WW-1:0] rtr_dwrr_req_weights,//weights for each requestor
    input  [N-1:0]         rtr_dwrr_mask,        // 1 - gate the request 0 - allow the request to arbitrate
    input                  rtr_dwrr_starve,
    input                  rtr_dwrr_grant_accept,
    input [N-1:0]          rtr_dwrr_grant,    // one-hot grant
    input [$clog2(N)-1:0]  rtr_dwrr_grant_ix,
    input [WW:0]           rtr_dwrr_deficit_credit[N],

    input [N-1:0]          q_byp_arb_req     ,
    input [N-1:0]          q_byp_arb_grant   ,
    input [$clog2(N)-1:0]  q_byp_arb_grant_ix,
    input                  q_byp_arb_grant_accept

);

//------------------------------------------------------------------------------
//-- General spec check -- fb rr arbiter
//------------------------------------------------------------------------------
    fb_rr_arb_sva #( 
      .N                  (N_RR), 
      .ALLOW_GRANT_SWITCH (ALLOW_GRANT_SWITCH_RR) // TODO: use rtl params
    ) byp_rr_arb_checker ( 
      .clk               (clk                   ), 
      .reset_n           (reset_n               ), 
      .req               (q_byp_arb_req         ), 
      .grant_accept      (q_byp_arb_grant_accept), 
      .grant             (q_byp_arb_grant       ), 
      .grant_ix          (q_byp_arb_grant_ix    ) 
       
    ); 

//------------------------------------------------------------------------------
//-- fb_rtr_dwrr_arb check
//------------------------------------------------------------------------------
    fb_dw_rr_arb_sva #(

      .N                  (N  ),
      .LW                 (LW ),
      .WW                 (WW ),
      .ALLOW_GRANT_SWITCH (ALLOW_GRANT_SWITCH),
      .GRANT_POWER_OPT    (GRANT_POWER_OPT)

    ) fb_dw_rr_arb_checker (

      .req                (rtr_dwrr_req),
      .req_max_len        (rtr_dwrr_req_max_len),
      .req_len_cmp        (rtr_dwrr_req_len_cmp),
      .req_weights        (rtr_dwrr_req_weights),
      .mask               (rtr_dwrr_mask),
      .starve             (rtr_dwrr_starve),
      .grant_accept       (rtr_dwrr_grant_accept),
      .grant              (rtr_dwrr_grant),
      .grant_ix           (rtr_dwrr_grant_ix),
      .deficit_credit     (rtr_dwrr_deficit_credit),
     
      .clk                (clk),     
      .reset_n            (reset_n)

    );

endmodule

//------------------------------------------------------------------------------
//-- General spec check -- LRG arbiter
//------------------------------------------------------------------------------

// genvar k;

// generate

//   for (k=0; k<N; k++) begin : per_req

//     `SV_COVER (FVPL_RTR_FV_co_can_requst      , req[k]);

//     if (ALLOW_GRANT_SWITCH) begin: gnt_switch

//         `SV_ASSERT (FVPL_RTR_FV_as_req_stays_on_until_gnt_and_gnt_acpt  , req[k] && !mask[k]  && !(grant[k] && grant_accept) |=> req[k]);
//         `SV_ASSERT (FVPL_RTR_FV_as_req_len_stable_until_gnt_and_gnt_acpt, req[k] && !mask[k]  && !(grant[k] && grant_accept) |=> $stable(req_max_len[k]));

//     end else begin

//         `SV_ASSERT (FVPL_RTR_FV_as_req_stays_on_until_gnt             , req[k]   && !mask[k]  && !grant[k]     |=> req[k]  );
//         `SV_ASSERT (FVPL_RTR_FV_as_req_len_stable_on_until_gnt        , req[k]   && !mask[k]  && !grant[k]     |=> $stable(req_max_len[k]) );
//         `SV_ASSERT (FVPL_RTR_FV_as_gnt_stays_on_until_gnt_acpt        , grant[k] && !mask[k]  && !grant_accept |=> grant[k]);

//     end


//     `SV_ASSERT (FVPL_RTR_FV_as_fixed_cycles_check_per_req            , req[k]   |-> ##[0:11]     (grant[k] && grant_accept));
//     `SV_ASSERT (FVPL_RTR_FV_as_liveness_check_per_req                , req[k]   |-> s_eventually (grant[k] && grant_accept));

//   end

// endgenerate
  
//   `SV_ASSERT (FVPL_RTR_FV_as_no_gnt_when_no_req                     , !|req   |-> !(|grant || grant_accept));

//   `SV_ASSERT (FVPL_RTR_FV_as_onehot_gnt_when_req                    ,  |(req & ~mask) & !starve  |-> $onehot(grant));
