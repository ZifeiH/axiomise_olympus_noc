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


logic [MNM_DNOC_TOTAL_NUM_VC-1:0] vc_rsvd_full, grp_rsvd_full, vc_shrd_full, grp_shrd_full;
logic [MNM_DNOC_TOTAL_NUM_VC-1:0] vc_rsvd_empty, grp_rsvd_empty, vc_shrd_empty;

logic [MNM_DNOC_TOTAL_NUM_VC-1:0] vc_incr, vc_decr;
logic [MNM_RTR_NUM_RSVD_CREDIT_GROUPS-1:0] rsvd_grp_incr, rsvd_grp_decr;

// For vc_rsvd_cnt, vc_rsvd_grp_cnt and vc_shrd_cnt
logic [MNM_DNOC_TOTAL_NUM_VC-1:0] crd_consumed, crd_returned;
logic [MNM_RTR_NUM_RSVD_CREDIT_GROUPS-1:0] rsvd_grp_crd_consumed, rsvd_grp_crd_returned;

logic [MNM_DNOC_TOTAL_NUM_VC-1:0][MNM_RTR_DNOC_RX_DEPTH_W-1:0] vc_rsvd_cnt, vc_rsvd_grp_cnt, vc_shrd_cnt;

logic [MNM_RTR_NUM_RSVD_CREDIT_GROUPS-1:0][MNM_RTR_DNOC_RX_DEPTH_W-1:0] grp_rsvd_cnt;
logic [MNM_RTR_NUM_SHRD_CREDIT_GROUPS-1:0][MNM_RTR_DNOC_RX_DEPTH_W-1:0] grp_shrd_cnt;

logic [MNM_RTR_DNOC_RX_DEPTH_W-1:0] total_shrd_cnt;




genvar vc, grp;


generate begin

  for(vc = 0; vc < MNM_DNOC_TOTAL_NUM_VC; vc++) begin
    
    // Credit increment and decrement logic per vc
    assign vc_incr[vc]  = credit_taken_valid && credit_taken_id == vc; 
    assign vc_decr[vc]  = credit_release_valid && credit_release_id == vc;
    // Logic to check from/to which vc credit shoule be taken or returned
    assign crd_consumed[vc]  = vc_incr[vc] && !vc_decr[vc];
    assign crd_returned[vc]  = vc_decr[vc] && !vc_incr[vc];

    // Full and Empty flags for vc_rsvd_cnt, rsvd_grp_cnt and vc_shrd_cnt
    // rsvd_full per vc
    assign vc_rsvd_full[vc]   = vc_rsvd_cnt[vc] == cfg_vc_rsvd_max[vc];
    // grp_rsvd_full in term of vc
    assign grp_rsvd_full[vc]  = (grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] == cfg_group_rsvd_max[cfg_vc_group_rsvd_id[vc]]);
    // shrd_full per vc
    assign vc_shrd_full[vc]   = vc_shrd_cnt[vc] == cfg_vc_shrd_max[vc];

    for(grp = 0; grp < MNM_RTR_NUM_SHRD_CREDIT_GROUPS; grp++) begin
      // grp_shrd_full per vc
      assign grp_shrd_full[vc] |= cfg_vc_group_shrd[vc][grp]? grp_shrd_cnt[grp] == cfg_group_shrd_max[grp];
    end

    // rsvd_empty per vc
    assign vc_rsvd_empty[vc]  = vc_rsvd_cnt[vc] == 'h0;
    // grp_rsvd_empty per vc
    assign grp_rsvd_empty[vc] = grp_rsvd_cnt[cfg_vc_group_rsvd_id[vc]] == 'h0; // can we use vc_rsvd_grp_cnt[vc] == 'h0 to indicate grp_rsvd_empty?
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
          else if (cfg_vc_group_rsvd_en[vc] && !grp_rsvd_full[vc])
            vc_rsvd_grp_cnt[vc] <= vc_rsvd_grp_cnt[vc] + 1'h1;
          else if (!vc_shrd_full[vc])
            vc_shrd_cnt[vc] <= vc_shrd_cnt[vc] + 1'h1;
        end
        else if(crd_returned[vc]) begin
          if(!vc_shrd_empty[vc])
            vc_shrd_cnt[vc] <= vc_shrd_cnt[vc] - 1'h1;
          else if(cfg_vc_group_rsvd_en[vc] && !grp_rsvd_empty[vc])
            vc_rsvd_grp_cnt[vc] <= vc_rsvd_grp_cnt[vc] - 1'h1;
          else if(!vc_rsvd_empty[vc])
            vc_rsvd_cnt[vc] <= vc_rsvd_cnt[vc] - 1'h1;
        end
      end
    end
  end

  for(grp = 0; grp < MNM_RTR_NUM_RSVD_CREDIT_GROUPS; grp++) begin

    assign shrd_grp_incr[grp]     = credit_taken_valid && vc_rsvd_full[credit_taken_id] && 
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

  for(grp = 0; grp < MNM_RTR_NUM_SHRD_CREDIT_GROUPS; grp++) begin

    assign shrd_grp_incr[grp]     = credit_taken_valid && vc_rsvd_full[credit_taken_id] && grp_rsvd_full[credit_taken_id] &&
                                    cfg_vc_group_shrd[credit_taken_id][grp];
    assign shrd_grp_decr[grp]     = credit_release_valid && cfg_vc_group_shrd[credit_taken_id][grp] && ;

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

end
endgenerate


endmodule