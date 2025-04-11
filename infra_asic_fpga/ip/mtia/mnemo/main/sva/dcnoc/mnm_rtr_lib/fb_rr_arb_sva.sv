/////////////////////////////////////////////////////////////////////////////////////////
// File: fb_rr_arb_sva.sv
// This file contains rr arb checks
/////////////////////////////////////////////////////////////////////////////////////////

module fb_rr_arb_sva #(
          parameter N                       = 4,  // number of requestors (6)
          parameter bit ALLOW_GRANT_SWITCH  = 0,
          parameter bit GRANT_POWER_OPT     = 0
)(
    input                                        clk,     // clock
    input                                        reset_n, // async reset
    input  [N-1:0]                               req,     // arbitration request
    input                                        grant_accept,
    input  [N-1:0]                               grant,    // one-hot grant
    input  [$clog2(N)-1:0]                       grant_ix

);

  logic   [$clog2(N+1):0] sym_reqstr_A, sym_reqstr_B;
  logic   valid_grant_A;
  logic   valid_grant_B;        
  logic   valid_request_B;
  logic   ready_to_see_B_req_while_granting_A;
  logic   seen_B_req_while_granting_A;
  logic   seen_B_grant;
  logic   arbit_window;
  logic   seen_arbit_window;

  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_index_stable , ##1 $stable(sym_reqstr_A) );
  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_B_index_stable , ##1 $stable(sym_reqstr_B) );

  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_B_index_legal  , (sym_reqstr_B < N) );
  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_index_legal  , (sym_reqstr_A < N) );

  `SV_ASSERT (FVPL_RTR_FV_am_reqstr_A_B_not_equal  , (sym_reqstr_A != sym_reqstr_B) );

  assign valid_request_B = req[sym_reqstr_B]; 
 
  assign ready_to_see_B_req_while_granting_A = valid_grant_A && valid_request_B && seen_arbit_window; 

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin

      seen_B_req_while_granting_A   <= 0;
      seen_B_grant                  <= 0;
      seen_arbit_window             <= 0;

    end
    else begin

      seen_B_req_while_granting_A                 <=  ready_to_see_B_req_while_granting_A || seen_B_req_while_granting_A;
      seen_B_grant                                <=  valid_grant_B || seen_B_grant;
      seen_arbit_window                           <=  arbit_window  || seen_arbit_window;

    end
  end

genvar k;

generate

  for (k=0; k<N; k++) begin : per_req

    `SV_COVER (FVPL_RTR_FV_co_can_requst      , req[k]);

    `SV_ASSERT (FVPL_RTR_FV_as_req_stays_on_until_grant		    , req[k] && !grant[k] |=> req[k]);

    `SV_ASSERT (FVPL_RTR_FV_as_liveness_check_per_req           , req[k]   |-> s_eventually (grant[k]));

  end

endgenerate

  `SV_COVER (FVPL_RTR_FV_co_requster_always_granted_fairly_v1       , ready_to_see_B_req_while_granting_A);

  `SV_ASSERT (FVPL_RTR_FV_as_rr_requster_always_granted_fairly      , seen_B_req_while_granting_A && !seen_B_grant |-> !valid_grant_A );

endmodule

