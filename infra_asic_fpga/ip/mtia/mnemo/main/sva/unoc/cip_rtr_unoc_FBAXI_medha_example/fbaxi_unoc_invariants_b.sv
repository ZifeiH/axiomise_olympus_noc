///////////////////////////////////////////////////
/// File: fbaxi_unoc_invariants_b.sv
/// This file contains invariants on TX 
///////////////////////////////////////////////////

module unoc_tx_invariants 
#(
    parameter DIR = 0,
    parameter NUM_TX         = 6,
    parameter NUM_RX         = 6,
    parameter NUM_VC         = 5
)
(   
    input logic                               tx_valid_o          ,
    input cip_pkg::utility_noc_t              tx_pyld_o           ,
    input  logic                               clk                 ,
    input  logic                               reset_n,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             dfifo_empty ,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             dfifo_pop ,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             cfifo_pop ,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             cfifo_empty ,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             q_arb_grant ,
    input  logic [NUM_VC-1:0][NUM_RX-1:0]             q_arb_req ,
    input  logic [NUM_VC-1:0]                         vc_arb_grant ,
    input  cip_pkg::utility_noc_t                     pyld_tx_muxed ,
    input  logic [NUM_VC-1:0]                         vc_arb_grant_r

);

genvar i;
genvar j;

generate

`include "fbaxi_unoc_invariants_vars.sv"

`ifdef FORMAL
if(DIR == 0) begin: north_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_IRTR_N_TX.vc_timeout_cnt));
end
else if(DIR == 1) begin : west_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_IRTR_W_TX.vc_timeout_cnt));
end
else if(DIR == 2) begin : south_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_IRTR_S_TX.vc_timeout_cnt));
end
else if(DIR == 3) begin : east_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_IRTR_E_TX.vc_timeout_cnt));
end
else if(DIR == 4) begin : f0_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_CRTR_FI0_TX.vc_timeout_cnt));
end
else if(DIR == 5) begin : f1_am
`SV_ASSERT(FVPH_RTR_FV_am_vc_timeout_never_happens, !(&`UNOC_IRTR_FI1_TX.vc_timeout_cnt));
end
`endif

////////////////////////////////////////////////////////
////// General invariants
///////////////////////////////////////////////////////


function logic legal_turn(int side, int trans_type);

  // side = RX, vc = channel, (include_vc = 1:To consider vc, 0:To not consider vc), trans_type = 1:request, 0:response
  legal_turn = 'h0;

  if(DIR != LEAF0) begin
    if(trans_type) begin
      if(DIR == NORTH || DIR == SOUTH) begin
        legal_turn  = !(side == DIR || side == EAST || side == WEST);
      end
      else begin
        legal_turn  = !(side == DIR);
      end
    end
    else begin
      legal_turn  = !((DIR == WEST || DIR == EAST) && (side == NORTH || side == SOUTH));
    end
  end
  else begin
    legal_turn = (side == LEAF1) || ((side == DIR) && !trans_type);
  end

endfunction

// gen_invariant1: tx_rd_mux_rx channel output
for(j = 0; j < 6; j++) begin
    if(legal_turn(j, 1)) begin
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_rreq, 
        u_tx_rd_mux_rx_sel0[j] |-> tx_rd_mux_rx_out[0].channel == cip_pkg::UNOC_CHANNEL_E_READ_REQ);

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wreq0, 
        u_tx_rd_mux_rx_sel1[j] |-> tx_rd_mux_rx_out[1].channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ);

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wreq1, 
        u_tx_rd_mux_rx_sel2[j] |-> tx_rd_mux_rx_out[2].channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ);
        
    end
    else begin
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_rreq,  !u_tx_rd_mux_rx_sel0[j]);

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wreq0, !u_tx_rd_mux_rx_sel1[j]);

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wreq1, !u_tx_rd_mux_rx_sel2[j]);
    end

    if(legal_turn(j, 0)) begin
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_rresp, 
      u_tx_rd_mux_rx_sel3[j] |-> tx_rd_mux_rx_out[3].channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP);

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wresp, 
      u_tx_rd_mux_rx_sel4[j] |-> tx_rd_mux_rx_out[4].channel == cip_pkg::UNOC_CHANNEL_E_WRITE_RESP);
    end
    else begin
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_rresp, !u_tx_rd_mux_rx_sel3[j]);

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant1_rd_mux_out_channel_wresp, !u_tx_rd_mux_rx_sel4[j]);
    end
end



// gen_invariant2: unused fifos
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant2_unused_fifo_rreq, !dfifo_pop[0][DIR] && dfifo_empty[0][DIR] && cfifo_empty[0][DIR]);
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant2_unused_fifo_wreq0, !dfifo_pop[1][DIR] && dfifo_empty[1][DIR] && cfifo_empty[1][DIR]);
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant2_unused_fifo_wreq1, !dfifo_pop[2][DIR] && dfifo_empty[2][DIR] && cfifo_empty[2][DIR]);

// gen_invariant3: tx_valid_o means ttl > 1 
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant3_valid_o_implies_tx_muxed_ttl_gt_1, tx_valid_o |-> $past(pyld_tx_muxed.ttl) > 1);



// gen_invariant4: If the design is updated to exclude dfifo_empty check from dfifo_pop 
// assignment then these invariants are not required.
for(i = 0; i < 6; i++) begin :invariant4
    for(j = 0; j < 5; j++) begin 
      if(j != 3 && j != 4) begin
        if(legal_turn(i, 1)) begin
            `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant4_not_cfifo_empty_implies_not_dfifo_empty,
                !cfifo_empty[j][i] |-> !dfifo_empty[j][i]);
        end
      end
      else begin
        if(legal_turn(i, 0)) begin
            `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant4_not_cfifo_empty_implies_not_dfifo_empty,
                !cfifo_empty[j][i] |-> !dfifo_empty[j][i]);
        end
      end
    end
end

// gen_invariant5: If q_arb_grant[j][i] then it means that the respective request must have been set too.
for(i = 0; i < 6; i++) begin :invariant5
    for(j = 0; j < 5; j++) begin
      if(j != 3 && j != 4) begin
        if(legal_turn(i, 1)) begin
                `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant5_granted_q_must_have_been_requested,
                    (q_arb_grant[j][i]) |-> (q_arb_req[j][i]));
        end
        else begin
                `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant5_unused_q_arb_grants_gen, !q_arb_grant[j][i]);
        end
      end
      else begin
        if(legal_turn(i, 0)) begin
                `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant5_granted_q_must_have_been_requested,
                    (q_arb_grant[j][i]) |-> (q_arb_req[j][i]));
        end
        else begin
                `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant5_unused_q_arb_grants_gen, !q_arb_grant[j][i]);
        end
      end
    end
end

// invariant6: If the design is updated to exclude dfifo_empty check from dfifo_pop 
// assignment then these invariants are not required.
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx__base1_invariant6_vc_arb_grant_implies_at_least_one_non_empty_fifo,
     (|vc_arb_grant) |-> !(&dfifo_empty));


// invariant7: prove and assume all gen_invariant4
for(i = 0; i < 5; i++) begin :invariant7
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant7_fifo_q_granted_implies_non_empty_cfifo, (|q_arb_grant[i]) |-> !(&cfifo_empty[i]));
end

for(i = 0; i < 5; i++) begin : invariant8_decomposed
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant8_decomposed_fifo_vc_arb_grant_next_cycle_dfifo_pop, (vc_arb_grant[i]) |-> (|dfifo_pop[i]));
end
// Invariant13: prove and assume invariant10_helpers, invariant15_helpers and invariant16
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant8_fifo_vc_arb_grant_next_cycle_dfifo_pop, (|vc_arb_grant) |-> (|dfifo_pop));


////////////////////////////////////////////////////////
////// Read Response invariants
///////////////////////////////////////////////////////

logic rvalid;
assign rvalid =  tx_valid_o && tx_pyld_o.channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP;

logic rlast;
assign rlast = tx_pyld_o.payload.uaxi_r.last;

logic [5:0] [3:0] rpop_cnt;

for(j = 0; j < 6; j++) begin


  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      rpop_cnt[j] <= 4'd0;
    end
    else if(dfifo_pop[3][j] && !sdata[3][j].payload.uaxi_r.last) begin
     rpop_cnt[j] <= rpop_cnt[j] + 4'd1;
    end
    else if(dfifo_pop[3][j] && sdata[3][j].payload.uaxi_r.last) begin
      rpop_cnt[j] <= 4'd0;
    end
  end

  if(legal_turn(j, 0)) begin

    //Invariant2: consecutive beats
    if(j == DIR) begin
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant9_fifo_rresp_vc3_src0_always_one_beat,
            dfifo_pop[3][j] |-> sdata[3][j].payload.uaxi_r.last);
    end
    else begin

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant10_fifo_rresp_consecutive_pops,
          dfifo_pop[3][j] && !sdata[3][j].payload.uaxi_r.last |=> dfifo_pop[3][j]);

      //Invariant16:
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant11_fifo_tx_valid_write_resp_and_not_last_past_popped_last_was_low,
              rvalid && !rlast
              && $past(dfifo_pop[3][j]) |-> $past(!sdata[3][j].payload.uaxi_r.last));

      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant12_fifo_rresp_ttl_in_burst_same_throughout,
          dfifo_pop[3][j] && !sdata[3][j].payload.uaxi_r.last |=> $stable(sdata[3][j].ttl));
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant13_fifo_rresp_id_in_burst_same_throughout,
          dfifo_pop[3][j] && !sdata[3][j].payload.uaxi_r.last |=> $stable(sdata[3][j].payload.uaxi_r.id));
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant14_fifo_rresp_user_in_burst_same_throughout,
          dfifo_pop[3][j] && !sdata[3][j].payload.uaxi_r.last |=> $stable(sdata[3][j].payload.uaxi_r.user));
      `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant15_fifo_rresp_last_as_expected,
          dfifo_pop[3][j] |-> sdata[3][j].payload.uaxi_r.last == (rpop_cnt[j] == sdata[3][j].payload.uaxi_r.id.len));
    end


    //Invariant16: If pop and ttl>1 then the next cycle tx_pyld_o.channel is the same as the popped channel 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant16_fifo_tx_channel_rresp,
        dfifo_pop[3][j] && sdata[3][j].ttl > 1 |=> tx_pyld_o.channel == cip_pkg::UNOC_CHANNEL_E_READ_RESP);


    //Invariant3: pop and enough ttl will lead to tx_valid_o next cycle
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant17_dfifo_pop_next_cycle_tx_valid_o,
        dfifo_pop[3][j] && sdata[3][j].ttl > 1 |=> tx_valid_o);

    //Invariant4: If pop and ttl>1 then the next cycle tx_pyld_o.payload is the same as the popped payload 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant18_tx_pyld_o_same_as_popped_data,
        dfifo_pop[3][j] && sdata[3][j].ttl > 1 |=> tx_pyld_o.payload == $past(sdata[3][j].payload));


    //Invariant6: If pop then pyld_tx_muxed.ttl is the same as the popped ttl 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant19_pyld_tx_muxed_ttl_same_as_popped_ttl,
        dfifo_pop[3][j] |-> sdata[3][j].ttl == pyld_tx_muxed.ttl);

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant19_rvalid_rpop_cnt_eq,
        dfifo_pop[3][j] && sdata[3][j].ttl > 1 |=> ##1 rvalid_cnt == $past(rpop_cnt[j]));

  end
end

// Changed vc_arb_grant_r[3] to vc_arb_grant[3]
// Invariant10: Important invariant: if RRESP on tx output, then the vc_arb_grant_r[3]
// First prove invariant21 also 10, 15, 16 and 17
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant20_tx_rresp_vc_grant_was_3, 
    rvalid |-> $past(vc_arb_grant[3]));


// Invariant15:
`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant21_rvalid_but_not_last_, 
    rvalid && !rlast |-> $past(|dfifo_pop3));


for(i = 0; i < 6; i++) begin : invariant22
 if(legal_turn(i, 0) && (i != DIR))
 `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant22_rrsep_consecutive_tx_valid_o_per_pop,
    rvalid && !rlast && $past(dfifo_pop[3][i]) |=> tx_valid_o);
end


`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant23_rresp_consecutive_tx_valid_o, 
    rvalid && !rlast |=> tx_valid_o);

`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant24_rresp_ttl_stable, 
    rvalid && !rlast |=> $stable(tx_pyld_o.ttl));

`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant25_rresp_id_stable, 
    rvalid && !rlast |=> $stable(tx_pyld_o.payload.uaxi_r.id));

`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant26_rresp_user_stable, 
    rvalid && !rlast |=> $stable(tx_pyld_o.payload.uaxi_r.user));


  logic [3:0] rvalid_cnt;



  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      rvalid_cnt <= 4'd0;
    end
    else if(rvalid && !rlast) begin
     rvalid_cnt <= rvalid_cnt + 4'd1;
    end
    else if(rvalid && rlast) begin
      rvalid_cnt <= 4'd0;
    end
  end


`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant27_rresp_last_as_expected, 
    rvalid |-> rlast == (rvalid_cnt == tx_pyld_o.payload.uaxi_r.id.len));


////////////////////////////////////////////////////////
////// Read Request invariants
///////////////////////////////////////////////////////

logic arvalid = tx_valid_o && tx_pyld_o.channel == cip_pkg::UNOC_CHANNEL_E_READ_REQ;



for(j = 0; j < 6; j++) begin

  if(legal_turn(j, 1)) begin
    //Invariant5: If pop and ttl>1 then the next cycle tx_pyld_o.channel is the same as the popped channel 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant28_tx_channel_rreq,
    dfifo_pop[0][j] && sdata[0][j].ttl > 1 |=> tx_pyld_o.channel == cip_pkg::UNOC_CHANNEL_E_READ_REQ);
    
    //Invariant3: pop and enough ttl will lead to tx_valid_o next cycle
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant29_dfifo_pop_next_cycle_tx_valid_o_rreq,
    dfifo_pop[0][j] && sdata[0][j].ttl > 1 |=> tx_valid_o);
    
    //Invariant4: If pop and ttl>1 then the next cycle tx_pyld_o.payload is the same as the popped payload 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant30_tx_pyld_o_same_as_popped_data_rreq,
    dfifo_pop[0][j] && sdata[0][j].ttl > 1 |=> tx_pyld_o.payload == $past(sdata[0][j].payload));
    
    
    //Invariant6: If pop then pyld_tx_muxed.ttl is the same as the popped ttl 
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant31_pyld_tx_muxed_ttl_same_as_popped_ttl_rreq,
    dfifo_pop[0][j] |-> sdata[0][j].ttl == pyld_tx_muxed.ttl);
    
    
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant32_rreq_valid_size,
     dfifo_pop[0][j] |-> sdata[0][j].payload.uaxi_ar.size inside {'d2, 'd3});
  
  end
end



`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant33_rreq_tx_valid_size,
 arvalid |-> tx_pyld_o.payload.uaxi_ar.size inside {'d2, 'd3});



////////////////////////////////////////////////////////
////// Write Request invariants
///////////////////////////////////////////////////////

logic awvalid;
assign awvalid = tx_valid_o && tx_pyld_o.channel == cip_pkg::UNOC_CHANNEL_E_WRITE_REQ;

logic wlast;
assign wlast = tx_pyld_o.payload.uaxi_combo_aw_w.w.last;

logic [5:0] [3:0] aw0pop_cnt;
logic [5:0] [3:0] aw1pop_cnt;

for(j = 0; j < 6; j++) begin

if (legal_turn(j, 1)) begin

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      aw0pop_cnt[j] <= 4'd0;
    end
    else if(dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last) begin
     aw0pop_cnt[j] <= aw0pop_cnt[j] + 4'd1;
    end
    else if(dfifo_pop[1][j] && sdata[1][j].payload.uaxi_combo_aw_w.w.last) begin
      aw0pop_cnt[j] <= 4'd0;
    end
  end

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      aw1pop_cnt[j] <= 4'd0;
    end
    else if(dfifo_pop[2][j] && !sdata[2][j].payload.uaxi_combo_aw_w.w.last) begin
     aw1pop_cnt[j] <= aw1pop_cnt[j] + 4'd1;
    end
    else if(dfifo_pop[2][j] && sdata[2][j].payload.uaxi_combo_aw_w.w.last) begin
      aw1pop_cnt[j] <= 4'd0;
    end
  end


    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant34_wreq0_pop_and_not_last_there_will_be_a_vc_grant,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> (|vc_arb_grant));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant34_wreq0_pop_and_not_last_there_will_be_a_non_empty_cfifo,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> (~cfifo_empty[1][j]));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant34_wreq0_pop_and_not_last_there_will_be_a_q_arb_grant,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> (q_arb_grant[1][j]));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant34_wreq0_pop_and_not_last_there_will_be_atleast_one_q_arb_grant,
    dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> (|q_arb_grant[1]));


    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant34_wreq0_consecutive_pops,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> dfifo_pop[1][j]);
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant35_wreq1_consecutive_pops,
        dfifo_pop[2][j] && !sdata[2][j].payload.uaxi_combo_aw_w.w.last |=> dfifo_pop[2][j]);
            
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant36_wreq0_stable_addr,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[1][j].payload.uaxi_combo_aw_w.aw.addr));
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant37_wreq1_stable_addr,
        dfifo_pop[2][j] && !sdata[2][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[2][j].payload.uaxi_combo_aw_w.aw.addr));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant38_wreq0_stable_user,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[1][j].payload.uaxi_combo_aw_w.aw.user));
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant39_wreq1_stable_user,
        dfifo_pop[2][j] && !sdata[2][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[2][j].payload.uaxi_combo_aw_w.aw.user));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant40_wreq0_stable_id,
        dfifo_pop[1][j] && !sdata[1][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[1][j].payload.uaxi_combo_aw_w.aw.id));
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant41_wreq1_stable_id,
        dfifo_pop[2][j] && !sdata[2][j].payload.uaxi_combo_aw_w.w.last |=> $stable(sdata[2][j].payload.uaxi_combo_aw_w.aw.id));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant42_wreq0_size,
        dfifo_pop[1][j] |=> sdata[1][j].payload.uaxi_combo_aw_w.aw.size  inside {'d2, 'd3});
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant43_wreq1_size,
        dfifo_pop[2][j] |=> sdata[2][j].payload.uaxi_combo_aw_w.aw.size  inside {'d2, 'd3});

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant44_wreq0_vc0,
        dfifo_pop[1][j] |-> !sdata[1][j].payload.uaxi_combo_aw_w.aw.user.vc);
        
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant45_wreq1_vc1,
        dfifo_pop[2][j] |->  sdata[2][j].payload.uaxi_combo_aw_w.aw.user.vc);

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant46_fifo_wreq_last_as_expected_vc0,
        dfifo_pop[1][j] |-> sdata[1][j].payload.uaxi_combo_aw_w.w.last == (aw0pop_cnt[j] == sdata[1][j].payload.uaxi_combo_aw_w.aw.id.len));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base0_invariant47_fifo_wreq_last_as_expected_vc1,
        dfifo_pop[2][j] |-> sdata[2][j].payload.uaxi_combo_aw_w.w.last == (aw1pop_cnt[j] == sdata[2][j].payload.uaxi_combo_aw_w.aw.id.len));
end
end

    // Change vc_arb_grant_r to vc_arb_grant
    // Invariant10: Important invariant: if RRESP on tx output, then the vc_arb_grant_r[3]
    // First prove invariant21 also 10, 15, 16 and 17
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant46_tx_wreq_vc_grant_was_1, 
        awvalid && !tx_pyld_o.payload.uaxi_combo_aw_w.aw.user.vc |->
         $past(vc_arb_grant[1]));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant46_tx_wreq_vc_grant_was_2, 
        awvalid && tx_pyld_o.payload.uaxi_combo_aw_w.aw.user.vc |->
         $past(vc_arb_grant[2]));


    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant46_tx_wreq_vc_grant_was_1_or_2, 
        awvalid |-> $past(vc_arb_grant[1]) || $past(vc_arb_grant[2]));


    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant47_awvalid_but_not_last_dfifo_pop_1, 
        awvalid && !wlast && !tx_pyld_o.payload.uaxi_combo_aw_w.aw.user.vc |-> $past(|dfifo_pop1));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_base1_invariant47_awvalid_but_not_last_dfifo_pop_2, 
        awvalid && !wlast && tx_pyld_o.payload.uaxi_combo_aw_w.aw.user.vc |-> $past(|dfifo_pop2));

    // Invariant15:
    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant47_awvalid_but_not_last_dfifo_pop_1_or_2, 
        awvalid && !wlast |-> $past(|dfifo_pop1) ||  $past(|dfifo_pop2));


    for(i = 0; i < 6; i++) begin : invariant48
    if(legal_turn(i, 1)) begin
        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant48_wreq0_consecutive_tx_valid_o_per_pop,
            awvalid && !wlast && $past(dfifo_pop[1][i]) |=> tx_valid_o);

        `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant48_wreq1_consecutive_tx_valid_o_per_pop,
            awvalid && !wlast && $past(dfifo_pop[2][i]) |=> tx_valid_o);
    end
    end



    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant49_awvalid_valid_size,
        awvalid |-> tx_pyld_o.payload.uaxi_combo_aw_w.aw.size inside {'d2, 'd3});

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant50_awvalid_consecutive,
        awvalid && !wlast |=> awvalid);

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant51_ttl_stable_throughout_burst,
        awvalid && !wlast |=> $stable(tx_pyld_o.ttl));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant52_awaddr_stable_throughout_burst,
        awvalid && !wlast |=> $stable(tx_pyld_o.payload.uaxi_combo_aw_w.aw.addr));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant53_awid_stable_throughout_burst,
        awvalid && !wlast |=> $stable(tx_pyld_o.payload.uaxi_combo_aw_w.aw.id));

    `SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant54_awuser_stable_throughout_burst,
        awvalid && !wlast |=> $stable(tx_pyld_o.payload.uaxi_combo_aw_w.aw.user));



  logic [3:0] awvalid_cnt;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      awvalid_cnt <= 4'd0;
    end
    else if(awvalid && !wlast) begin
     awvalid_cnt <= awvalid_cnt + 4'd1;
    end
    else if(awvalid && wlast) begin
      awvalid_cnt <= 4'd0;
    end
  end


`SV_ASSERT(FVPH_RTR_FV_as_unoc_tx_invariant55_wlast_as_expected, 
    awvalid |-> wlast == (awvalid_cnt == tx_pyld_o.payload.uaxi_combo_aw_w.aw.id.len));


endgenerate
endmodule