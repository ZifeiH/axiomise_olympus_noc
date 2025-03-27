// Credit consumption out of the three buckets of credit type is in the following order.
// 1. First, use VC exclusive (rsvd)
// 2. Second use VC grp rsvd, if VC belongs to a rsvd grp
// 3. Third, if VC is in a VC grp shrd, credit is ok if
//    a. if VC shrd max not hit and,
//    b. credit is available in all grps the VC belongs to and,
//    c. total shrd max not hit
// Third, if VC is not in a VC grp shrd, credit is ok if
//    d. if VC shrd max not hit, and
//    e. total shrd max not hit
module credit_manager_constraints_input
# (
) (
    input    [LEN_W-1:0]                                        noc_in_len ,
    input    [VC_W-1:0]                                         noc_in_vc,
    input                                                       noc_in_last,
    input                                                       noc_in_vld ,
            
    input                                                       crd_rel_vld,
    input   [NUM_VC-1:0][VC_W-1:0]                              crd_rel_id ,
            
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

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);


logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_rsvd         ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_shrd         ;
logic   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                          per_grp_shrd    ;

logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_grp_rsvd     ;

logic   [NUM_VC-1:0]                                            vc_rsvd_full    ;
logic   [NUM_VC-1:0]                                            vc_shrd_full    ;
logic   [NUM_SHRD_GRP-1:0]                                      grp_shrd_full   ;
logic   [NUM_RSVD_GRP-1:0]                                      vc_grp_rsvd_full;

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

for (genvar vc = 0 ; vc < NUM_VC ; vc ++ ) begin

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin

            vc_rsvd[vc]            <= '0;
            vc_grp_rsvd[vc]        <= '0;
            vc_shrd[vc]            <= '0;

        end else begin
        if (noc_in_vld) begin

            if      (!vc_rsvd_full[vc])       vc_rsvd[vc]  <= vc_rsvd[vc] + (noc_in_vc == vc);
            // else if (!vc_grp_rsvd_full[vc])   vc_rsvd[vc]      <= vc_rsvd[vc]     + (noc_in_vc == vc);
            else                              vc_shrd[vc]      <= vc_shrd[vc]     + (noc_in_vc == vc);        

        end

        if (crd_rel_vld) begin

            if      (vc_shrd[vc]     != 0)    vc_shrd[vc]      <= vc_shrd[vc]     - (crd_rel_id == vc);
            // else if (vc_grp_rsvd[vc] != 0)    vc_rsvd[vc]      <= vc_rsvd[vc]     + (crd_rel_id == vc);
            else if (vc_rsvd[vc]     != 0)    vc_rsvd[vc]      <= vc_rsvd[vc]     - (crd_rel_id == vc);

        end
        end
        
    end 
end

endgenerate

always_comb begin: per_grp_credits_calc
    per_grp_shrd        = '0;
    for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
        for (int vc = 0 ; vc < NUM_VC ; vc ++ ) begin
            if (vc_grp_shrd[vc][grp]) per_grp_shrd[grp] = per_grp_shrd[grp] + vc_shrd[vc];
        end
    end
end

always_comb begin: total_shrd_credits_calc
    total_shrd_credits     = '0;
    for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
        total_shrd_credits = total_shrd_credits + per_grp_shrd[grp];
    end
end

always_comb begin: total_credits_calc
    total_credits_taken     = '0;
    for (int vc = 0 ; vc < NUM_VC ; vc ++ ) begin
        total_credits_taken = vc_rsvd[vc] + total_credits_taken;
    end
    total_credits_taken     = total_credits_taken + total_shrd_credits;
end

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------

generate
    for (genvar grp=0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
        `SV_ASSERT (FVPH_RTR_FV_am_gropmax_not_reach_per_grp         ,   per_grp_shrd[grp]  <= vc_grp_shrd_max[grp]);
    end

    for (genvar vc=0; vc < NUM_VC ; vc++) begin
        `SV_ASSERT (FVPH_RTR_FV_am_vcmax_not_reach_per_vc            ,   vc_shrd[vc]        <= vc_shrd_max[vc]);
                         
        `SV_ASSERT (FVPH_RTR_FV_am_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_am_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_am_no_credit_release_when_no_taken   ,   vc_rsvd[vc] == 0 && vc_rsvd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));

    end

    `SV_ASSERT (FVPH_RTR_FV_am_total_shrd_less_than_total_shrd_max   ,   total_shrd_credits  <= total_shrd_max);
    `SV_ASSERT (FVPH_RTR_FV_am_total_taken_less_than_total           ,   total_credits_taken <= total_credits);


//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------
    for (genvar vc=0; vc < NUM_VC ; vc++) begin                         
        `SV_ASSERT (FVPH_RTR_FV_as_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_no_credit_release_when_no_taken   ,   vc_rsvd[vc] == 0 && vc_rsvd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));

    end
endgenerate

endmodule


module credit_manager_constraints_output
# (
    parameter NUM_VC       = 11
    // parameter VC_W         = $clog2(NUM_VC),
    // parameter CRED_W       = CRED_W,
    // parameter NUM_RSVD_GRP = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS,
    // parameter RSVD_GRP_W   = $clog2(NUM_RSVD_GRP),
    // parameter NUM_SHRD_GRP = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS,
    // parameter SHRD_GRP_W   = $clog2(NUM_SHRD_GRP)

) (
    input    [LEN_W-1:0]                                        noc_out_len ,
    input    [VC_W-1:0]                                         noc_out_vc,
    input                                                       noc_out_last,
    input                                                       noc_out_vld ,
            
    input                                                       crd_rel_vld,
    input   [NUM_VC-1:0][VC_W-1:0]                              crd_rel_id ,
            
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

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);


logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_rsvd         ;
logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_shrd         ;
logic   [NUM_SHRD_GRP-1:0][CRED_W-1:0]                          per_grp_shrd    ;

logic   [NUM_VC-1:0][CRED_W-1:0]                                vc_grp_rsvd     ;

logic   [NUM_VC-1:0]                                            vc_rsvd_full    ;
logic   [NUM_VC-1:0]                                            vc_shrd_full    ;
logic   [NUM_SHRD_GRP-1:0]                                      grp_shrd_full   ;
logic   [NUM_RSVD_GRP-1:0]                                      vc_grp_rsvd_full;

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

for (genvar vc = 0 ; vc < NUM_VC ; vc ++ ) begin

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin

            vc_rsvd[vc]            <= '0;
            vc_grp_rsvd[vc]        <= '0;
            vc_shrd[vc]            <= '0;

        end else begin
        if (noc_out_vld) begin

            if      (!vc_rsvd_full[vc])       vc_rsvd[vc]  <= vc_rsvd[vc] + (noc_out_vc == vc);
            // else if (!vc_grp_rsvd_full[vc])   vc_rsvd[vc]      <= vc_rsvd[vc]     + (noc_out_vc == vc);
            else                              vc_shrd[vc]      <= vc_shrd[vc]     + (noc_out_vc == vc);        

        end

        if (crd_rel_vld) begin

            if      (vc_shrd[vc]     != 0)    vc_shrd[vc]      <= vc_shrd[vc]     - (crd_rel_id == vc);
            // else if (vc_grp_rsvd[vc] != 0)    vc_rsvd[vc]      <= vc_rsvd[vc]     + (crd_rel_id == vc);
            else if (vc_rsvd[vc]     != 0)    vc_rsvd[vc]      <= vc_rsvd[vc]     - (crd_rel_id == vc);

        end
        end
        
    end 
end

endgenerate

always_comb begin: per_grp_credits_calc
    per_grp_shrd        = '0;
    for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
        for (int vc = 0 ; vc < NUM_VC ; vc ++ ) begin
            if (vc_grp_shrd[vc][grp]) per_grp_shrd[grp] = per_grp_shrd[grp] + vc_shrd[vc];
        end
    end
end

always_comb begin: total_shrd_credits_calc
    total_shrd_credits     = '0;
    for (int grp = 0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin
        total_shrd_credits = total_shrd_credits + per_grp_shrd[grp];
    end
end

always_comb begin: total_credits_calc
    total_credits_taken     = '0;
    for (int vc = 0 ; vc < NUM_VC ; vc ++ ) begin
        total_credits_taken = vc_rsvd[vc] + total_credits_taken;
    end
    total_credits_taken     = total_credits_taken + total_shrd_credits;
end


generate

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------

for (genvar vc=0; vc < NUM_VC ; vc++) begin
                     
    `SV_ASSERT (FVPH_RTR_FV_am_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
    `SV_ASSERT (FVPH_RTR_FV_am_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
    `SV_ASSERT (FVPH_RTR_FV_am_no_credit_release_when_no_taken   ,   vc_rsvd[vc] == 0 && vc_rsvd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));
end

//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------

    for (genvar grp=0 ; grp < NUM_SHRD_GRP ; grp ++ ) begin: per_grp
        `SV_ASSERT (FVPH_RTR_FV_as_gropmax_not_reach_per_grp         ,   per_grp_shrd[grp]  <= vc_grp_shrd_max[grp]);
    end

    for (genvar vc=0; vc < NUM_VC ; vc++) begin
        `SV_ASSERT (FVPH_RTR_FV_as_vcmax_not_reach_per_vc            ,   vc_shrd[vc]        <= vc_shrd_max[vc]);
                         
        `SV_ASSERT (FVPH_RTR_FV_as_vc_shrd_eventually_credit_back    ,   vc_shrd[vc] != 0                       |-> s_eventually vc_shrd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_vc_rsvd_eventually_credit_back    ,   vc_rsvd[vc] != 0                       |-> s_eventually vc_rsvd[vc] == 0);
        `SV_ASSERT (FVPH_RTR_FV_as_no_credit_release_when_no_taken   ,   vc_rsvd[vc] == 0 && vc_rsvd[vc] == 0   |-> !(crd_rel_vld && crd_rel_id == vc));

    end

    `SV_ASSERT (FVPH_RTR_FV_as_total_shrd_less_than_total_shrd_max   ,   total_shrd_credits  <= total_shrd_max);
    `SV_ASSERT (FVPH_RTR_FV_as_total_taken_less_than_total           ,   total_credits_taken <= total_credits);

endgenerate


endmodule