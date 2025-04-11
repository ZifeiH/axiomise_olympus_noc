/////////////////////////////////////////////////////////////////////////////////////////

// File: fb_dw_rr_arb_sva.sv
// - spaced req stays high until grant
// - if masked request has credit but spaced request not, starve will be asserted
// - when starve, the bypass arbiter will grant amonst the 1 beat spaced request

// - if ALLOW_GRANT_SWITCH, the arbiter will switch the grant regardless grant_accept or not
//      if 2 request competing, one request failed to have grant_accept, winner switch
//        -- means new winner shouldn't be the previous winner?

// - All requestors will get grant within 11 cycles

// Bypass arbiter (rr_arb):
// 1. request stays high until grant
// 2. request eventually grant

/////////////////////////////////////////////////////////////////////////////////////////

module fb_dw_rr_arb_sva #(
    parameter N   = 4,
              LW  = 4,
              WW  = 4,
              ALLOW_GRANT_SWITCH = 1,
              GRANT_POWER_OPT = 0
)(
    input  [N-1:0]         req,     // arbitration request
    input  [N-1:0][LW-1:0] req_max_len, // arbitration request
    input  [N-1:0][LW-1:0] req_len_cmp, // request length compensation
    input  [N-1:0][WW-1:0] req_weights,//weights for each requestor
    input  [N-1:0]         mask,        // 1 - gate the request 0 - allow the request to arbitrate
    input                  starve,
    input                  grant_accept,
    input [N-1:0]          grant,    // one-hot grant
    input [$clog2(N)-1:0]  grant_ix,
    input [WW:0]           deficit_credit[N],

    input                  clk,     // clock
    input                  reset_n // async reset
);

//------------------------------------------------------------------------------
//-- Function
//------------------------------------------------------------------------------
  function automatic logic [$clog2(N)-1:0] f_index_of_set_bit (
    input logic [N-1:0] vec
  );
    begin
      f_index_of_set_bit = '0;
      for (int i=0; i<N; i++) begin
        if (vec[i]) begin
          f_index_of_set_bit = i;
          break;
        end
      end
    end
  endfunction : f_index_of_set_bit


//------------------------------------------------------------------------------
//-- General spec check -- Side rtr_dw_rr arbiter
//------------------------------------------------------------------------------

  logic [N-1:0]         spaced_request_has_credits;
  logic [N-1:0]         masked_request_has_credits;
  logic [$clog2(N)-1:0] pre_grant_winner_ix;

  always_comb begin
    for (int k=0; k<N; k++) begin : per_req

      spaced_request_has_credits[k] = req[k] & !mask[k] & (deficit_credit[k] >= req_max_len[k]);
      masked_request_has_credits[k] = req[k] &  mask[k] & (deficit_credit[k] >= req_max_len[k]);

    end
  end

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin

      pre_grant_winner_ix <= '0;

    end else begin

      pre_grant_winner_ix <= f_index_of_set_bit (grant);

    end

  end

//------------------------------------------------------------------------------
//-- Grant switch aux--
//------------------------------------------------------------------------------

  logic   [$clog2(N+1):0] sym_reqstr_A, sym_reqstr_B;    
  logic   valid_request_A;
  logic   valid_request_B;
  logic   ready_to_see_B_req_while_granting_A;
  logic   seen_B_req_while_granting_A;
  logic   seen_B_grant;

  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_index_stable , ##1 $stable(sym_reqstr_A) );
  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_B_index_stable , ##1 $stable(sym_reqstr_B) );

  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_B_index_legal  , (sym_reqstr_B < N) );
  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_index_legal  , (sym_reqstr_A < N) );
  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_B_not_equal  , (sym_reqstr_A != sym_reqstr_B) );
 
  assign valid_request_A = req[sym_reqstr_A]   && !mask[sym_reqstr_A] ;
  assign valid_request_B = req[sym_reqstr_B]   && !mask[sym_reqstr_B] ;

  generate

    if (ALLOW_GRANT_SWITCH) begin
      `SV_ASSERT (FVPL_RTR_FV_as_gnt_switch_when_not_accept   , valid_request_A && valid_request_B && grant[sym_reqstr_A] && !grant_accept |=> f_index_of_set_bit (grant) != pre_grant_winner_ix);
    end

    for (genvar k=0; k<N; k++) begin : per_req

      `SV_COVER  (FVPL_RTR_FV_co_can_requst                         , req[k]                                                         );
      `SV_ASSERT (FVPL_RTR_FV_as_req_stays_on_until_gnt             , req[k] && !grant[k] && !starve |=> req[k]                      );
      `SV_ASSERT (FVPL_RTR_FV_as_req_len_stable_on_until_gnt        , req[k] && !grant[k] && !starve |=> $stable(req_max_len[k])     );

      `SV_ASSERT (FVPL_RTR_FV_as_grant_request_not_masked           , grant[k]            |->              !mask[k]                  );
      `SV_ASSERT (FVPL_RTR_FV_as_request_eventually_not_mask        , mask[k]             |-> s_eventually !mask[k]                  );
      `SV_ASSERT (FVPL_RTR_FV_as_fixed_cycles_check_per_req         , req[k]              |-> ##[0:11]     (grant[k] && grant_accept));
      `SV_ASSERT (FVPL_RTR_FV_as_liveness_check_per_req             , req[k]              |-> s_eventually (grant[k] && grant_accept));

      if (!ALLOW_GRANT_SWITCH) begin: gnt_switch_on

          `SV_ASSERT (FVPL_RTR_FV_as_gnt_stays_on_until_gnt_acpt    , grant[k] && !grant_accept |=> grant[k]);

      end 

    end

  endgenerate
  
  `SV_ASSERT (FVPL_RTR_FV_as_no_gnt_when_no_req                     , !|req   |-> !(|grant || grant_accept));

  `SV_ASSERT (FVPL_RTR_FV_as_onehot_gnt_when_req                    ,  |(req & ~mask) & !starve  |-> $onehot(grant));

  `SV_ASSERT (FVPL_RTR_FV_as_grant_ix_as_expected                   , |grant |-> grant_ix == f_index_of_set_bit (grant));

  `SV_ASSERT (FVPL_RTR_FV_as_stave_check                            , !|spaced_request_has_credits && |masked_request_has_credits |-> starve);

    // fb_rr_arb_sva #( 
    //   .N                  (N), 
    //   .ALLOW_GRANT_SWITCH (ALLOW_GRANT_SWITCH) // TODO: use rtl params
    // ) rr_arb_checker ( 
    //   .clk            (clk                   ), 
    //   .reset_n        (reset_n               ), 
    //   .req            (req         ), 
    //   .grant_accept   (grant_accept), 
    //   .grant          (grant       ), 
    //   .grant_ix       (grant_ix    ) 
       
    // ); 

endmodule