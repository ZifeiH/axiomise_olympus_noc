// Default Cfgs for north:
// Total credit = 128
// VC reserved max = 2
// VC grp rsvd Max = 0
// Total shared credits = Total credit - Total reserved = 128 - (2 * 11 = 22) = 106
// VC grp shrd Max = Total shrd credit / 2 = 53
// VC shrd max = 53
// Total shrd max = 53

module shrd_crd_mgr_sva #(
  parameter NUM_VC = 8,
  parameter VCID_W = $clog2(NUM_VC),
  parameter CRD_W = 5,
  parameter NUM_RSVD_GROUPS = 4,
  parameter NUM_SHRD_GROUPS = 4,
  parameter RSVD_GROUP_W = $clog2(NUM_RSVD_GROUPS),
  parameter MAX_LEN = 2,
  parameter DISABLE_RTT_CHECK = 16'h0 // per VC vector to disable RTT check for low performance VCs
) (
  input  logic                                   credit_taken_valid  , // asserted once per beat.
  input  logic [VCID_W-1:0]                      credit_taken_id     ,
  input  logic                                   credit_release_valid, // asserted once per beat.
  input  logic [VCID_W-1:0]                      credit_release_id   ,

  output logic [NUM_VC-1:0][MAX_LEN-1:0]         credit_ok           , // Per VC, per LEN

  input  logic [NUM_VC-1:0][CRD_W-1:0]           cfg_vc_rsvd_max     ,
  input  logic [NUM_VC-1:0][CRD_W-1:0]           cfg_vc_shrd_max     ,
  input  logic [NUM_VC-1:0]                      cfg_vc_group_rsvd_en,
  input  logic [NUM_VC-1:0][RSVD_GROUP_W-1:0]    cfg_vc_group_rsvd_id, // Which VCs belong to each shared credit pool
  input  logic [NUM_VC-1:0][NUM_SHRD_GROUPS-1:0] cfg_vc_group_shrd   , // Which VCs belong to each shared credit pool
  input  logic [NUM_RSVD_GROUPS-1:0][CRD_W-1:0]  cfg_group_rsvd_max  ,
  input  logic [NUM_SHRD_GROUPS-1:0][CRD_W-1:0]  cfg_group_shrd_max  ,
  input  logic [CRD_W-1:0]                       cfg_total_shrd_max  ,
  input  logic [CRD_W-1:0]                       cfg_total_credits   , // Only used for assertion to check programming

  output logic [NUM_VC-1:0][CRD_W-1:0]          sts_vc_rsvd_cnt      ,
  output logic [NUM_VC-1:0][CRD_W-1:0]          sts_vc_group_rsvd_cnt,
  output logic [NUM_VC-1:0][CRD_W-1:0]          sts_vc_group_shrd_cnt,
  output logic [NUM_RSVD_GROUPS-1:0][CRD_W-1:0] sts_group_rsvd_cnt   ,
  output logic [NUM_SHRD_GROUPS-1:0][CRD_W-1:0] sts_group_shrd_cnt   ,
  output logic [CRD_W-1:0]                      sts_total_shrd_cnt   ,

  output logic [NUM_VC-1:0]                     idle,
  output logic [NUM_VC-1:0]                     credit_overflow      ,
  output logic [NUM_VC-1:0]                     credit_underflow     ,
  input  logic clk,
  input  logic reset_n
);


  logic [NUM_VC-1:0] vc_rsvd_full, vc_grp_rsvd_full, vc_shrd_full, grp_shrd_full, vc_grp_shrd_full;
  logic [NUM_VC-1:0] vc_rsvd_empty, vc_grp_rsvd_empty, vc_shrd_empty;

  logic [NUM_VC-1:0] vc_incr, vc_decr;
  logic [NUM_RSVD_GROUPS-1:0] rsvd_grp_incr, rsvd_grp_decr;
  logic [NUM_SHRD_GROUPS-1:0] shrd_grp_incr, shrd_grp_decr;
  logic                       total_shrd_incr, total_shrd_decr;
  // For vc_rsvd_cnt, vc_rsvd_grp_cnt and vc_shrd_cnt
  logic [NUM_VC-1:0] crd_consumed, crd_returned;
  logic [NUM_RSVD_GROUPS-1:0] rsvd_grp_crd_consumed, rsvd_grp_crd_returned;
  logic [NUM_SHRD_GROUPS-1:0] shrd_grp_crd_consumed, shrd_grp_crd_returned;

  logic [NUM_VC-1:0][CRD_W-1:0] vc_rsvd_cnt, vc_rsvd_grp_cnt, vc_shrd_cnt;

  logic [NUM_RSVD_GROUPS-1:0][CRD_W-1:0] grp_rsvd_cnt;
  logic [NUM_SHRD_GROUPS-1:0][CRD_W-1:0] grp_shrd_cnt;

  logic [CRD_W-1:0] total_shrd_cnt;

  logic [NUM_VC-1:0] vc_shrd_enable;

  logic [NUM_VC-1:0][MAX_LEN-1:0] tb_credit_ok


  genvar vc, grp;

  generate begin

    for(vc = 0; vc < NUM_VC; vc++) begin

      // Credit increment and decrement logic per vc
      assign vc_incr[vc]  = credit_taken_valid && credit_taken_id == vc; 
      assign vc_decr[vc]  = credit_release_valid && credit_release_id == vc;
      // Logic to check from/to which vc credit shoule be taken or returned
      assign crd_consumed[vc]  = vc_incr[vc] && !vc_decr[vc];
      assign crd_returned[vc]  = vc_decr[vc] && !vc_incr[vc];

      // Full and Empty flags for vc_rsvd_cnt, rsvd_grp_cnt and vc_shrd_cnt
      // rsvd_full per vc
      assign vc_rsvd_full[vc]   = vc_rsvd_cnt[vc] == cfg_vc_rsvd_max[vc];
      // vc_grp_rsvd_full in term of vc
      assign vc_grp_rsvd_full[vc]  = (grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] == cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]]);
      // shrd_full per vc
      assign vc_shrd_full[vc]   = vc_shrd_cnt[vc] == cfg_vc_shrd_max[vc];

      for(grp = 0; grp < NUM_SHRD_GROUPS; grp++) begin
        // grp_shrd_full
        assign grp_shrd_full[grp] = grp_shrd_cnt[grp] == cfg_group_shrd_max[grp];
      end

      always_comb begin
        for(int g = 0; g < NUM_SHRD_GROUPS; g++) begin
          // grp_shrd_full
          vc_grp_shrd_full[vc] |= cfg_vc_group_shrd[vc][g]? grp_shrd_full[g] : 'h0;
        end
      end

      // rsvd_empty per vc
      assign vc_rsvd_empty[vc]  = vc_rsvd_cnt[vc] == 'h0;
      // vc_grp_rsvd_empty per vc
      assign vc_grp_rsvd_empty[vc] = grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] == 'h0; // can we use vc_rsvd_grp_cnt[vc] == 'h0 to indicate vc_grp_rsvd_empty?
      // shrd_empty per vc
      assign vc_shrd_empty[vc]  = vc_shrd_cnt[vc] == 'h0;

      // vc_rsvd_cnt, vc_rsvd_grp_cnt and vc_shrd_cnt incr and decr logic per vc
      always @(posedge clk or negedge reset_n) begin
        if(!reset_n) begin
          vc_rsvd_cnt     <= 'h0;
          vc_rsvd_grp_cnt <= 'h0;
          vc_shrd_cnt     <= 'h0;
        end
        else begin
          if(crd_consumed[vc]) begin
            if(!vc_rsvd_full[vc])
              vc_rsvd_cnt[vc] <= vc_rsvd_cnt[vc] + 1'h1;
            else if (cfg_vc_group_rsvd_en[vc] && !vc_grp_rsvd_full[vc])
              vc_rsvd_grp_cnt[vc] <= vc_rsvd_grp_cnt[vc] + 1'h1;
            else if (!vc_shrd_full[vc])
              vc_shrd_cnt[vc] <= vc_shrd_cnt[vc] + 1'h1;
          end
          else if(crd_returned[vc]) begin
            if(!vc_shrd_empty[vc])
              vc_shrd_cnt[vc] <= vc_shrd_cnt[vc] - 1'h1;
            else if(cfg_vc_group_rsvd_en[vc] && !vc_grp_rsvd_empty[vc])
              vc_rsvd_grp_cnt[vc] <= vc_rsvd_grp_cnt[vc] - 1'h1;
            else if(!vc_rsvd_empty[vc])
              vc_rsvd_cnt[vc] <= vc_rsvd_cnt[vc] - 1'h1;
          end
        end
      end
    end

    for(grp = 0; grp < NUM_RSVD_GROUPS; grp++) begin

      assign rsvd_grp_incr[grp]     = credit_taken_valid && vc_rsvd_full[credit_taken_id] && 
                                      cfg_vc_group_rsvd_en[credit_taken_id] && cfg_vc_group_rsvd_id[credit_taken_id] == grp;
      assign rsvd_grp_decr[grp]     = credit_release_valid && (grp_rsvd_cnt[grp] > 0) && vc_shrd_cnt[credit_release_id] == 'h0 &&
                                      cfg_vc_group_rsvd_en[credit_release_id] && cfg_vc_group_rsvd_id[credit_release_id] == grp;

      assign rsvd_grp_crd_consumed[grp]  = rsvd_grp_incr[grp] && !rsvd_grp_decr[grp];
      assign rsvd_grp_crd_returned[grp]  = rsvd_grp_decr[grp] && !rsvd_grp_incr[grp];

      always @(posedge clk or negedge reset_n) begin
        if(!reset_n)
          grp_rsvd_cnt[grp] <= 'h0;
        else begin
          if(rsvd_grp_crd_consumed[grp])
            grp_rsvd_cnt[grp] <= grp_rsvd_cnt[grp] + 1'h1;
          else if(rsvd_grp_crd_returned)
            grp_rsvd_cnt[grp] <= grp_rsvd_cnt[grp] - 1'h1;
        end
      end
    end

    for(grp = 0; grp < NUM_SHRD_GROUPS; grp++) begin

      assign shrd_grp_incr[grp]     = credit_taken_valid && vc_rsvd_full[credit_taken_id] && vc_grp_rsvd_full[credit_taken_id] &&
                                      cfg_vc_group_shrd[credit_taken_id][grp];
      assign shrd_grp_decr[grp]     = credit_release_valid && (grp_shrd_cnt[grp] > 'h0) && cfg_vc_group_shrd[credit_taken_id][grp];

      assign shrd_grp_crd_consumed[grp]  = shrd_grp_incr[grp] && !shrd_grp_decr[grp];
      assign shrd_grp_crd_returned[grp]  = shrd_grp_decr[grp] && !shrd_grp_incr[grp];

      always @(posedge clk or negedge reset_n) begin
        if(!reset_n)
          grp_shrd_cnt[grp] <= 'h0;
        else begin
          if(rsvd_grp_crd_consumed[grp])
            grp_shrd_cnt[grp] <= grp_shrd_cnt[grp] + 1'h1;
          else if(rsvd_grp_crd_returned)
            grp_shrd_cnt[grp] <= grp_shrd_cnt[grp] - 1'h1;
        end
      end
    end

    assign total_shrd_incr = credit_taken_valid && vc_rsvd_full[credit_taken_id] && vc_grp_rsvd_full[credit_taken_id];
    assign total_shrd_decr = credit_release_valid && (total_shrd_cnt > 'h0);

    assign total_shrd_crd_consumed = total_shrd_incr && !total_shrd_decr;
    assign total_shrd_crd_returned = total_shrd_decr && !total_shrd_incr;

    always @(posedge clk or negedge reset_n) begin
      if(!reset_n)
        total_shrd_cnt <= 'h0;
      else begin
        if(total_shrd_crd_consumed)
          total_shrd_cnt <= total_shrd_cnt + 1'h1;
        else if(total_shrd_crd_returned)
          total_shrd_cnt <= total_shrd_cnt - 1'h1;
      end
    end

  end
  endgenerate

  logic [NUM_VC-1:0] crd_needed;

  always_comb begin
    credit_ok = 'h0;
    crd_needed = 'h0;
    for(int vc = 0; vc < NUM_VC; vc++) begin
      for(int len = 0; len < MAX_LEN; len++) begin
        if(!vc_rsvd_full[vc])
          credit_ok[vc][len]  = (vc_rsvd_cnt[vc] + len) < cfg_vc_rsvd_max[vc];

        if((vc_rsvd_full[vc] || (credit_ok[vc][len] && !credit_ok[vc][len+1])) && cfg_vc_group_rsvd_en[vc] && !vc_grp_rsvd_full[vc])
          credit_ok[vc][len] = (grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] + len) < cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]];
        if(!(vc_shrd_full[vc] || vc_grp_shrd_full[vc]))
          credit_ok[vc][len] = (grp_shrd_cnt[cfg_vc_group_rsvd_id[vc]] + len) < cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]];
      end
    end
    
  end

  always_comb begin
    credit_ok = 'h0;
    crd_needed = 'h0;
    for(int vc = 0; vc < NUM_VC; vc++) begin
      // First need to check whether credits are available in vc reserved or not. 
      // If partial credits are available then set the crd_needed to 1 to get credits 
      // from other resources otherwise set to 0
      if(!vc_rsvd_full[vc]) begin
        credit_ok[vc][0]  = vc_rsvd_cnt[vc] < cfg_vc_rsvd_max[vc];
        credit_ok[vc][1]  = vc_rsvd_cnt[vc] + 1 < cfg_vc_rsvd_max[vc];
        crd_needed[vc]    = credit_ok[vc][0] && !credit_ok[vc][1];
      end
      else
        crd_needed[vc]    = 'h0;

      // Possibilities for needing credits from rsvd grp
      // 1) vc_rsvd is full
      // 2) vc_rsvd is not full but not have enough credits to offer
      if((vc_rsvd_full[vc] || crd_needed[vc]) && cfg_vc_group_rsvd_en[vc] && !vc_grp_rsvd_full[vc]) begin
        if(vc_rsvd_full[vc]) begin
          credit_ok[vc][0] = grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] < cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]];
          credit_ok[vc][1] = grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] + 1 < cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]];
          crd_needed[vc]   = credit_ok[vc][0] && !credit_ok[vc][1];
        end
        else begin
          credit_ok[vc][1] = grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] < cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]];
        end
      end
      else if(vc_rsvd_full[vc] && !cfg_vc_group_rsvd_en[vc] && vc_grp_rsvd_full[vc])
        crd_needed[vc]    = 'h0;

      // Possibilities for needing credits from shrd grp
      // 1) vc_rsvd and, rsvd grp are full or rsvd grp is not enable
      // 2) vc_rsvd is not full but not have enough credits to offer and rsvd grp is full
      // 3) rsvd grp is not full but not have enough credits to offer and vc rsvd is full
      if((vc_rsvd_full[vc] || !cfg_vc_group_rsvd_en[vc] || vc_grp_rsvd_full[vc] || crd_needed[vc]) && !(vc_shrd_full[vc] || vc_grp_shrd_full[vc] || cfg_total_shrd_max > 'h0)) begin
        if(vc_rsvd_full[vc] && (!cfg_vc_group_rsvd_en[vc] || vc_grp_rsvd_full[vc])) begin
          for(int grp = 0; grp < NUM_SHRD_GROUPS; grp++) begin
            credit_ok[vc][0] |= cfg_vc_group_shrd[vc][grp]? (grp_shrd_cnt[grp] < cfg_group_shrd_max[grp]) && !vc_shrd_full[vc] : 'h0;
            credit_ok[vc][1] |= cfg_vc_group_shrd[vc][grp]? (grp_shrd_cnt[grp] + 1 < cfg_group_shrd_max[grp]) && !vc_shrd_full[vc] : 'h0;
          end
        end
        else if(crd_needed[vc]) begin
          for(int grp = 0; grp < NUM_SHRD_GROUPS; grp++) begin
            credit_ok[vc][1] |= cfg_vc_group_shrd[vc][grp]? (grp_shrd_cnt[grp] + 1 < cfg_group_shrd_max[grp]) && !vc_shrd_full[vc] : 'h0;
          end
        end
      end
    end
  end

endmodule