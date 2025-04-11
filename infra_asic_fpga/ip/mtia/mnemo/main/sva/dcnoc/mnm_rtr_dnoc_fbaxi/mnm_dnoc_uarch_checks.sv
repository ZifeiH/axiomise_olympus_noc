/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_dnoc_uarch_checks.sv
// This file contains micro architer checks
/////////////////////////////////////////////////////////////////////////////////////////
// main.north0_lane.rx_north0.genblk2[0].
// main.north0_lane.rx_north0.rx_valid_i
`define DNOC_CA(SIDE, LANE_NUM)            genblk1.``SIDE````LANE_NUM``_lane.ca_``SIDE````LANE_NUM``
`define DNOC_CA_RTR_DWRR(SIDE, LANE_NUM)  `DNOC_CA(SIDE, LANE_NUM).genblk2[LANE_NUM].q_arb_dwrr
`define DNOC_CA_BYP_RR(SIDE, LANE_NUM)    `DNOC_CA(SIDE, LANE_NUM).genblk2[LANE_NUM].q_byp_arb_rr

// for (genvar lane = 0; lane < NUM_LANE_NUMS; lane++ ) begin: per_lane
//     if (!REMOVE_LANE_NUM[lane]) begin
// main.north0_lane.ca_north0.NUM_RX
        // .N                    (  11),
        // .LW                   ( 2 ),
        // .WW                   ( 8),
        // .ALLOW_GRANT_SWITCH   (  1),
        // .GRANT_POWER_OPT      ( 0),

        // .N_RR                    (  11),
        // .ALLOW_GRANT_SWITCH_RR   (  1)
    ca_arb_checker_sva #( 
        .N                    (  11),
        .LW                   ( 2 ),
        .WW                   ( 8),
        .ALLOW_GRANT_SWITCH   (  1),
        .GRANT_POWER_OPT      ( 0),

        .N_RR                    (  11),
        .ALLOW_GRANT_SWITCH_RR   (  1)
    ) ca_arb_checker ( 

        .clk                     (`DNOC_CA(north,0).clk    ),
        .reset_n                 (`DNOC_CA(north,0).reset_n),
        .rtr_dwrr_req            (`DNOC_CA_RTR_DWRR(north,0).req),
        .rtr_dwrr_req_max_len    (`DNOC_CA_RTR_DWRR(north,0).req_max_len),
        .rtr_dwrr_req_len_cmp    (`DNOC_CA_RTR_DWRR(north,0).req_len_cmp),
        .rtr_dwrr_req_weights    (`DNOC_CA_RTR_DWRR(north,0).req_weights),
        .rtr_dwrr_mask           (`DNOC_CA_RTR_DWRR(north,0).mask),
        .rtr_dwrr_starve         (`DNOC_CA_RTR_DWRR(north,0).starve),
        .rtr_dwrr_grant_accept   (`DNOC_CA_RTR_DWRR(north,0).grant_accept),
        .rtr_dwrr_grant          (`DNOC_CA_RTR_DWRR(north,0).grant),
        .rtr_dwrr_grant_ix       (`DNOC_CA_RTR_DWRR(north,0).grant_ix),
        .rtr_dwrr_deficit_credit (`DNOC_CA_RTR_DWRR(north,0).deficit_credit),
        .q_byp_arb_req           (`DNOC_CA_BYP_RR(north,0).req),
        .q_byp_arb_grant         (`DNOC_CA_BYP_RR(north,0).grant),
        .q_byp_arb_grant_ix      (`DNOC_CA_BYP_RR(north,0).grant_ix),
        .q_byp_arb_grant_accept  (`DNOC_CA_BYP_RR(north,0).grant_accept)

       
    ); 

//     end

// end