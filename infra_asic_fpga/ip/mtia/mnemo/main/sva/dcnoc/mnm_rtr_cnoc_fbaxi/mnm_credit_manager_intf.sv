module credit_manager_constraints_input
# (
) (
    input    [LEN_W-1:0]                                        noc_in_len ,
    input    [VC_W-1:0]                                         noc_in_vc,
    input                                                       noc_in_last,
    input                                                       noc_in_vld ,
            
    input                                                       crd_rel_vld,
    input   [VC_W-1:0]                                          crd_rel_id ,
            
    input   [NUM_VC-1:0][CRED_W-1:0]                            vc_rsvd_max,       // max credit per vc can reserve
    input   [NUM_VC-1:0][CRED_W-1:0]                            vc_shrd_max,       // max credit per vc can share
            
    input   [NUM_VC-1:0]                                        vc_grp_rsvd_en ,   // grp access enabled for this vc
    input   [NUM_VC-1:0][RSVD_GRP_W-1:0]                        vc_grp_rsvd_id ,   // which grp this vc belongs to
    input   [NUM_RSVD_GRP-1:0][CRED_W-1:0]                      vc_grp_rsvd_max,   // max credit per grp can reserve
            
    input   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                      vc_grp_shrd_max,   // max credit per grp can share
    input   [NUM_VC-1:0][NUM_SHRD_GRP-1:0]                      vc_grp_shrd    ,   // per vc, group : 1 0 1 0 0 0 ...
            
    input   [CRED_W-1:0]                                        total_shrd_max ,
    input   [CRED_W-1:0]                                        total_credits  ,
            
    input                                                       clk    ,
    input                                                       reset_n
);

logic   [NUM_VC-1:0]                                            credit_ok       ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_rsvd         ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_shrd         ;
logic   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                          per_grp_shrd    ;

logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_grp_rsvd     ;

logic   [NUM_VC-1:0]                                            vc_rsvd_full    ;
logic   [NUM_VC-1:0]                                            vc_shrd_full    ;
logic   [NUM_SHRD_GRP-1:0]                                      grp_shrd_full   ;
logic   [NUM_RSVD_GRP-1:0]                                      vc_grp_rsvd_full;

logic   [NUM_VC-1:0]                                            vc_rsvd_incr;
logic   [NUM_VC-1:0]                                            vc_rsvd_decr;

logic   [NUM_VC-1:0]                                            vc_shrd_incr;
logic   [NUM_VC-1:0]                                            vc_shrd_decr;

logic   [NUM_VC-1:0]                                            grant;

logic   [CRED_W-1:0]                                            total_shrd_credits;
logic   [CRED_W-1:0]                                            total_credits_taken;

generate

for (genvar vc = 0 ; vc < NUM_VC ; vc ++ ) begin

    assign vc_rsvd_full[vc]        =  vc_rsvd[vc]       == vc_rsvd_max[vc];
    assign vc_shrd_full[vc]        =  vc_shrd[vc]       == vc_shrd_max[vc];

end

for (genvar grp = 0 ; grp < NUM_RSVD_GRP ; grp ++ ) begin
    assign vc_grp_rsvd_full[grp]    = (vc_grp_rsvd[grp]   == vc_grp_rsvd_max[vc_grp_rsvd_id[grp]]) || vc_grp_rsvd_en[grp];
end

for (genvar grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
    assign grp_shrd_full[grp]      = per_grp_shrd[grp]  == vc_grp_shrd_max[grp];
end

endgenerate


always_comb begin
    vc_rsvd_incr = '0;
    vc_rsvd_decr = '0;
    vc_shrd_incr = '0;
    vc_shrd_decr = '0;
    grant        = '1;

    for (int vc = 0 ; vc < NUM_VC ; vc++) begin
        credit_ok[vc] = 0;

        if (noc_in_vld && (noc_in_vc == vc)) begin
            if (!vc_rsvd_full[vc]) begin
                vc_rsvd_incr[vc] = 1;
                credit_ok[vc]    = 1;
            end
            else if (total_shrd_credits < total_shrd_max && !vc_shrd_full[vc]) begin
                for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++) begin
                    if (vc_grp_shrd[vc][grp])
                        grant[vc] &= (!grp_shrd_full[grp]);
                end
                if (grant[vc]) begin
                    vc_shrd_incr[vc] = 1;
                    credit_ok[vc]    = 1;
                end
            end
        end

        if (crd_rel_vld && (crd_rel_id == vc)) begin
            if (vc_shrd[vc] != 0)
                vc_shrd_decr[vc] = 1;
            else
                vc_rsvd_decr[vc] = 1;
        end
    end
end


always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            vc_rsvd[vc]       <= '0;
            vc_shrd[vc]       <= '0;
            vc_grp_rsvd[vc]   <= '0;
        end

        for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp++) begin
            per_grp_shrd[grp] <= '0;
        end

        total_shrd_credits <= '0;

    end else begin
        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            
            vc_rsvd[vc] <= vc_rsvd[vc] + vc_rsvd_incr[vc] - vc_rsvd_decr[vc];
            vc_shrd[vc] <= vc_shrd[vc] + vc_shrd_incr[vc] - vc_shrd_decr[vc];

        end

        for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp++) begin
            for (int vc = 0 ; vc < NUM_VC ; vc++) begin
                per_grp_shrd[grp] <= per_grp_shrd[grp] + vc_shrd_incr[vc] && vc_grp_shrd[vc][grp] - vc_shrd_decr[vc] && vc_grp_shrd[vc][grp];
            end
        end

        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            total_shrd_credits <= total_shrd_credits + vc_shrd_incr[vc] - vc_shrd_decr[vc];
        end

    end
end


always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        total_credits_taken     <= '0;
    end
    else begin
        total_credits_taken     <= total_credits_taken + noc_in_vld - crd_rel_vld;
    end

end

generate

//------------------------------------------------------------------------------
//-- Covers --
//------------------------------------------------------------------------------
    for (genvar vc=0; vc < NUM_VC ; vc++) begin   
        `SV_COVER (FVPH_RTR_FV_co_vc_rsvd_full                       ,   vc_rsvd_full[vc] == '1);
    end

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------

        `SV_ASSERT (FVPH_RTR_FV_am_credit_ok_when_in_valid           ,   noc_in_vld && noc_in_last |-> credit_ok[noc_in_vc]);

//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------
    for (genvar vc=0; vc < NUM_VC ; vc++) begin                         
        `SV_ASSERT (FVPH_RTR_FV_as_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_vc_no_credit_release_when_no_taken,   vc_rsvd[vc] == 0 && vc_shrd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));
    end

    `SV_ASSERT (FVPH_RTR_FV_as_no_credit_release_when_no_taken       ,   total_credits_taken == '0              |-> !crd_rel_vld);

endgenerate

endmodule


module credit_manager_constraints_output
# () (
    input    [LEN_W-1:0]                                        noc_out_len ,
    input    [VC_W-1:0]                                         noc_out_vc,
    input                                                       noc_out_last,
    input                                                       noc_out_vld ,
            
    input                                                       crd_rel_vld,
    input   [VC_W-1:0]                                          crd_rel_id ,
            
    input   [NUM_VC-1:0][CRED_W-1:0]                            vc_rsvd_max,       // max credit per vc can reserve
    input   [NUM_VC-1:0][CRED_W-1:0]                            vc_shrd_max,       // max credit per vc can share
            
    input   [NUM_VC-1:0]                                        vc_grp_rsvd_en ,   // grp access enabled for this vc
    input   [NUM_VC-1:0][RSVD_GRP_W-1:0]                        vc_grp_rsvd_id ,   // which grp this vc belongs to
    input   [NUM_RSVD_GRP-1:0][CRED_W-1:0]                      vc_grp_rsvd_max,   // max credit per grp can reserve
            
    input   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                      vc_grp_shrd_max,   // max credit per grp can share
    input   [NUM_VC-1:0][NUM_SHRD_GRP-1:0]                      vc_grp_shrd    ,   // per vc, group : 1 0 1 0 0 0 ...
            
    input   [CRED_W-1:0]                                        total_shrd_max ,
    input   [CRED_W-1:0]                                        total_credits  ,
            
    input                                                       clk    ,
    input                                                       reset_n
);


logic   [NUM_VC-1:0]                                            credit_ok       ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_rsvd         ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_shrd         ;
logic   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                          per_grp_shrd    ;

logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_grp_rsvd     ;

logic   [NUM_VC-1:0]                                            vc_rsvd_full    ;
logic   [NUM_VC-1:0]                                            vc_shrd_full    ;
logic   [NUM_SHRD_GRP-1:0]                                      grp_shrd_full   ;
logic   [NUM_RSVD_GRP-1:0]                                      vc_grp_rsvd_full;

logic   [NUM_VC-1:0]                                            vc_rsvd_incr;
logic   [NUM_VC-1:0]                                            vc_rsvd_decr;

logic   [NUM_VC-1:0]                                            vc_shrd_incr;
logic   [NUM_VC-1:0]                                            vc_shrd_decr;

logic   [NUM_VC-1:0]                                            grant;

logic   [CRED_W-1:0]                                            total_shrd_credits;
logic   [CRED_W-1:0]                                            total_credits_taken;

generate

for (genvar vc = 0 ; vc < NUM_VC ; vc ++ ) begin

    assign vc_rsvd_full[vc]        =  vc_rsvd[vc]       == vc_rsvd_max[vc];
    assign vc_shrd_full[vc]        =  vc_shrd[vc]       == vc_shrd_max[vc];

end

for (genvar grp = 0 ; grp < NUM_RSVD_GRP ; grp ++ ) begin
    assign vc_grp_rsvd_full[grp]    = (vc_grp_rsvd[grp]   == vc_grp_rsvd_max[vc_grp_rsvd_id[grp]]) || vc_grp_rsvd_en[grp];
end

for (genvar grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
    assign grp_shrd_full[grp]      = per_grp_shrd[grp]  == vc_grp_shrd_max[grp];
end

endgenerate


always_comb begin
    vc_rsvd_incr = '0;
    vc_rsvd_decr = '0;
    vc_shrd_incr = '0;
    vc_shrd_decr = '0;
    grant        = '1;

    for (int vc = 0 ; vc < NUM_VC ; vc++) begin
        credit_ok[vc] = 0;

        if (noc_out_vld && (noc_out_vc == vc)) begin
            if (!vc_rsvd_full[vc]) begin
                vc_rsvd_incr[vc] = 1;
                credit_ok[vc]    = 1;
            end
            else if (total_shrd_credits < total_shrd_max && !vc_shrd_full[vc]) begin
                for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++) begin
                    if (vc_grp_shrd[vc][grp])
                        grant[vc] &= (!grp_shrd_full[grp]);
                end
                if (grant[vc]) begin
                    vc_shrd_incr[vc] = 1;
                    credit_ok[vc]    = 1;
                end
            end
        end

        if (crd_rel_vld && (crd_rel_id == vc)) begin
            if (vc_shrd[vc] != 0)
                vc_shrd_decr[vc] = 1;
            else
                vc_rsvd_decr[vc] = 1;
        end
    end
end


always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            vc_rsvd[vc]       <= '0;
            vc_shrd[vc]       <= '0;
            vc_grp_rsvd[vc]   <= '0;
        end

        for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp++) begin
            per_grp_shrd[grp] <= '0;
        end

        total_shrd_credits <= '0;

    end else begin
        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            
            vc_rsvd[vc] <= vc_rsvd[vc] + vc_rsvd_incr[vc] - vc_rsvd_decr[vc];
            vc_shrd[vc] <= vc_shrd[vc] + vc_shrd_incr[vc] - vc_shrd_decr[vc];

        end

        for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp++) begin
            for (int vc = 0 ; vc < NUM_VC ; vc++) begin
                per_grp_shrd[grp] <= per_grp_shrd[grp] + vc_shrd_incr[vc] && vc_grp_shrd[vc][grp] - vc_shrd_decr[vc] && vc_grp_shrd[vc][grp];
            end
        end

        for (int vc = 0 ; vc < NUM_VC ; vc++) begin
            total_shrd_credits <= total_shrd_credits + vc_shrd_incr[vc] - vc_shrd_decr[vc];
        end

    end
end


always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        total_credits_taken     <= '0;
    end
    else begin
        total_credits_taken     <= total_credits_taken + noc_out_vld - crd_rel_vld;
    end

end

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------

generate

for (genvar vc=0; vc < NUM_VC ; vc++) begin
                     
    `SV_ASSERT (FVPH_RTR_FV_am_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
    `SV_ASSERT (FVPH_RTR_FV_am_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
    `SV_ASSERT (FVPH_RTR_FV_am_no_vc_credit_release_when_no_taken,   vc_rsvd[vc] == 0 && vc_shrd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));
end
    `SV_ASSERT (FVPH_RTR_FV_am_no_credit_release_when_no_taken   ,   total_credits_taken == '0              |-> !crd_rel_vld);

//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------

    `SV_ASSERT (FVPH_RTR_FV_as_no_credit_credit_ok_when_out_valid ,   noc_out_last && noc_out_vld |-> credit_ok[noc_out_vc]);

    for (genvar grp=0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin: per_grp
        `SV_ASSERT (FVPH_RTR_FV_as_gropmax_not_reach_per_grp         ,   per_grp_shrd[grp]  <= vc_grp_shrd_max[grp]);
    end

    for (genvar vc=0; vc < NUM_VC ; vc++) begin
        `SV_ASSERT (FVPH_RTR_FV_as_vcmax_not_reach_per_vc            ,   vc_shrd[vc]        <= vc_shrd_max[vc]);
                         
        `SV_ASSERT (FVPH_RTR_FV_as_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_no_credit_release_when_no_taken   ,   vc_rsvd[vc] == 0 && vc_shrd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));

    end

    `SV_ASSERT (FVPH_RTR_FV_as_total_shrd_less_than_total_shrd_max   ,   total_shrd_credits  <= total_shrd_max);
    `SV_ASSERT (FVPH_RTR_FV_as_total_taken_less_than_total           ,   total_credits_taken <= total_credits);

endgenerate


endmodule


