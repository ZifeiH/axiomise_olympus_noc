/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_sub_block_check_defines.sv
/// This file contains the performance, rx buffer/fifo, tx fifo and arb checks
/////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- RX vc_buf check defines --
//------------------------------------------------------------------------------

  `define VC_BUF_CHECKS(VC_BUF_LABELS, SIDE, FIFO_DEPTH, RX_VC_BUF, NUM_NOCS) begin: VC_BUF_LABELS   \
    for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane   \
    for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc   \
        for (genvar ch=0; ch < cip_pkg::CIP_RTR_NUM_DIRECTIONS ; ch++) begin: per_dir   \
            if ((num_of_nocs<LANES_CAN_TURN)?!ILLEGAL_TGT_ID_TABLE[SIDE][ch][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][ch][vc]) begin: expected   \
              transaction_tracker_sva # (   \
                .DATA_WIDTH(1),   \
                .CHECKER_DEPTH(FIFO_DEPTH)   \
              ) vc_buffer_checker (   \
                .data_in    (RX_VC_BUF.wdin[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]),   \
                .in_valid   (RX_VC_BUF.we[ch]),   \
                .data_out   (RX_VC_BUF.rdout[ch==`PARTNER_IX][`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                .out_valid  (RX_VC_BUF.re[ch]),   \
                .clk        (clk),   \
                .reset_n    (reset_n)   \
                ); \
              `SV_ASSERT (FVPL_RTR_FV_as_vc_buf_checks_no_buffer_underflow ,   RX_VC_BUF.empty[ch] |-> !RX_VC_BUF.re[ch]);   \
            end   \
            end \
            \
            `SV_ASSERT (FVPL_RTR_FV_as_vc_buf_checks_no_buffer_overflow ,   RX_VC_BUF.full |-> !|RX_VC_BUF.we ); \
            end   \
    end   \
  end


//------------------------------------------------------------------------------
//-- RX fifo check defines --
//------------------------------------------------------------------------------

    `define RX_FIFO_CHECKS(FIFO_CHECK_LABELS, DIRECTION, RX_FIFO, NUM_NOCS, NUM_DIRECTIONS) begin: FIFO_CHECK_LABELS \
   \
      for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
       \
              for (genvar vc=0; vc<TOTAL_NUM_VC; vc++)begin: per_vc \
   \
                      fb_fifo_tb #( \
   \
                        .DEPTH(RX_FIFO.DEPTH), \
                        .WIDTH(1) \
   \
                        )  \
                      fifo_checker ( \
   \
                         .out     (RX_FIFO.out[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                         .full    (RX_FIFO.full), \
                         .empty   (RX_FIFO.empty), \
                         .count   (RX_FIFO.count), \
                         .push    (RX_FIFO.push), \
                         .pop     (RX_FIFO.pop), \
                         .in      (RX_FIFO.in[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                         .scan    (RX_FIFO.scan), \
                         .clk     (clk), \
                         .reset_n (reset_n) \
   \
                      ); \
   \
                  end \
          end \
  \
    end

//------------------------------------------------------------------------------
//-- TX fifo check defines --
//------------------------------------------------------------------------------
 
  `define FIFO_CHECKS(FIFO_CHECK_LABELS, DIRECTION, TX_FIFO, NUM_NOCS, NUM_DIRECTIONS) begin: FIFO_CHECK_LABELS \
 \
    for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
     \
        for (genvar dir=0; dir<NUM_DIRECTIONS; dir++) begin: per_dir \
     \
            for (genvar vc=0; vc<TOTAL_NUM_VC; vc++)begin: per_vc \
 \
                if ((DIRECTION==LEAF0||DIRECTION==LEAF1)?!LEAF_TX_ILLEGAL_TRUNS_TABLE[dir][vc]:(num_of_nocs<LANES_CAN_TURN?!ILLEGAL_TGT_ID_TABLE[dir][DIRECTION][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[dir][DIRECTION][vc])) begin: expected \
 \
                    fb_fifo_tb #( \
 \
                      .DEPTH(TX_FIFO.DEPTH), \
                      .WIDTH(1) \
 \
                      )  \
                    fifo_checker ( \
 \
                       .out     (TX_FIFO.out[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                       .full    (TX_FIFO.full), \
                       .empty   (TX_FIFO.empty), \
                       .count   (TX_FIFO.count), \
                       .push    (TX_FIFO.push), \
                       .pop     (TX_FIFO.pop), \
                       .in      (TX_FIFO.in[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                       .scan    (TX_FIFO.scan), \
                       .clk     (clk), \
                       .reset_n (reset_n) \
 \
                    ); \
 \
                end \
        end \
    end \
    end \
\
  end


//------------------------------------------------------------------------------
//-- leaf rx performance check defines --
//------------------------------------------------------------------------------

 `define LEAF_RX_PERFORMANCE_CHECKS(LEAF_RX_PERFORMANCE_CHECKS_LABEL, RX_PATH, RX_FIFO, NUM_NOCS) begin: LEAF_RX_PERFORMANCE_CHECKS_LABEL \
 \
     for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
 \
        for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit, !RX_FIFO.empty && RX_PATH.credit_pool[RX_PATH.fifo_destid[vc]][vc] > RX_PATH.fifo_len[vc] \
 \
                                                                  |->  \
 \
                                                                  RX_PATH.vc_arb_req[vc]); \
 \
                `SV_ASSERT (FVPL_RTR_FV_as_tx_valid_after_grant , RX_PATH.vc_arb_grant[vc] && |RX_PATH.fifo_destid[vc] |-> RX_PATH.tx_valid_o); \
 \
        end \
            \
            `SV_ASSERT (FVPL_RTR_FV_as_vc_arb_grant_winner_when_having_req, |RX_PATH.vc_arb_req |-> $onehot(RX_PATH.vc_arb_grant)); \
 \
     end \
 end


//------------------------------------------------------------------------------
//-- NSEW rx performance check defines --
//------------------------------------------------------------------------------

 `define RX_PERFORMANCE_CHECKS(RX_PERFORMANCE_CHECKS_LABEL, SIDE, RX_PATH, RX_VC_BUF, RX_VC_BUF_PRTNR, NUM_NOCS, NUM_DIRECTIONS) begin: RX_PERFORMANCE_CHECKS_LABEL \
 \
 for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane  \
 \
        for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
 \
            if (num_of_nocs<LANES_CAN_TURN?!ILLEGAL_TGT_ID_TABLE[SIDE][LEAF0][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][LEAF0][vc]) begin: leaf_arb_performance_checker \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_partner_req_when_fifo_not_empty   , !RX_VC_BUF_PRTNR.empty[`LOCAL_IX] \
 \
                                                                      |->  \
 \
                                                                      RX_PATH.leaf_arb_req[vc][1]); \
               \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_local_req_when_fifo_not_empty   ,  !RX_VC_BUF.empty[`LOCAL_IX] |->  \
                                                                             \
                                                                            RX_PATH.leaf_arb_req[vc][0]); \
                                                                            \
              `SV_ASSERT (FVPL_RTR_FV_as_leaf_arb_grant_winner_when_having_reqs   ,  |RX_PATH.leaf_arb_req[vc] |->  $onehot(RX_PATH.leaf_arb_grant[vc])); \
              \
            end \
 \
            begin: dest_arb_performance_checker \
 \
              for (genvar tx=0; tx<NUM_DIRECTIONS ; tx++) begin: per_dir \
 \
              if (((num_of_nocs<LANES_CAN_TURN)?!ILLEGAL_TGT_ID_TABLE[SIDE][tx][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][tx][vc]) && tx != `PARTNER_IX) begin: local_req \
 \
                    if (tx != `LOCAL_IX) begin: not_to_leaf \
 \
                    `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit  ,!RX_VC_BUF.empty[tx] && \
 \
                                                                        RX_PATH.credit_pool[tx][vc] > RX_VC_BUF.rlen[tx] |-> \
 \
                                                                        RX_PATH.dest_arb_req[vc][tx] ); \
                    end \
                    else begin: to_leaf \
 \
                    `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit  ,!RX_VC_BUF.empty[tx] && \
 \
                                                                        RX_PATH.credit_pool[tx][vc] > RX_VC_BUF.rlen[tx] && \
 \
                                                                        !RX_PATH.leaf_arb_grant[vc][1] |-> \
 \
                                                                        RX_PATH.dest_arb_req[vc][tx] ); \
                    end \
 \
              end \
 \
              end \
   \
              if ((num_of_nocs<LANES_CAN_TURN)?!ILLEGAL_TGT_ID_TABLE[SIDE][LEAF0][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][LEAF0][vc]) begin: partner_req \
   \
                      `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit  ,!RX_VC_BUF.empty[`PARTNER_IX] && \
   \
                                                                           RX_PATH.credit_pool[`LOCAL_IX][vc] > RX_VC_BUF_PRTNR.rlen[`LOCAL_IX] && \
   \
                                                                           RX_PATH.leaf_arb_grant[vc][1] \
       \
                                                                           |-> \
   \
                                                                           RX_PATH.dest_arb_req[vc][`LOCAL_IX] ); \
              end \
 \
                `SV_ASSERT (FVPL_RTR_FV_as_dest_arb_grant_winner_when_having_requests   ,  (|RX_PATH.dest_arb_req[vc] |->  $onehot(RX_PATH.dest_arb_grant[vc]))); \
 \
            end \
 \
            begin: vc_arb_performance_checker \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit     , !RX_PATH.fifo_empty[vc]   &&  RX_PATH.credit_pool > RX_PATH.fifo_len[vc] |->  RX_PATH.vc_arb_req[vc] ); \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_tx_valid_after_grant        , RX_PATH.vc_arb_grant[vc] && |RX_PATH.fifo_destid[vc] |=> RX_PATH.tx_valid_o); \
 \
            end \
 \
      end \
     \
              `SV_ASSERT (FVPL_RTR_FV_as_vc_arb_grant_winner_when_having_requests   ,  (|RX_PATH.vc_arb_req |->  $onehot(RX_PATH.vc_arb_grant))); \
    end \
end


//------------------------------------------------------------------------------
//-- TX performance check defines --
//------------------------------------------------------------------------------

 `define TX_PERFORMANCE_CHECKS(TX_PERFORMANCE_CHECK_LABEL, DIRECTION, TX_PATH, NUM_NOCS, NUM_DIRECTIONS) begin: TX_PERFORMANCE_CHECK_LABEL \
 \
    for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
 \
        for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
 \
          begin: q_arb_performance_checker \
 \
            for (genvar dir=0; dir<NUM_DIRECTIONS; dir++) begin: per_dir \
 \
                if ((DIRECTION==LEAF0||DIRECTION==LEAF1)?!LEAF_TX_ILLEGAL_TRUNS_TABLE[dir][vc]:(num_of_nocs<LANES_CAN_TURN?!ILLEGAL_TGT_ID_TABLE[dir][DIRECTION][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[dir][DIRECTION][vc])) begin: expected \
 \
                      `SV_ASSERT (FVPL_RTR_FV_as_req_when_fifo_not_empty, !TX_PATH.fifo_empty[dir][vc] |-> TX_PATH.q_arb_req[vc][dir] ); \
 \
              end \
 \
            end \
          end \
\
          `SV_ASSERT (FVPL_RTR_FV_as_q_arb_grant_winner_when_having_reqs, |TX_PATH.q_arb_req[vc] |-> $onehot(TX_PATH.q_arb_grant[vc])); \
 \
          begin: vc_arb_performance_checker \
           \
             `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit, |TX_PATH.q_arb_grant[vc] &&  TX_PATH.credit_pool[vc] > TX_PATH.vc_arb_req_len[vc] |-> TX_PATH.vc_arb_req[vc]); \
             \
             `SV_ASSERT (FVPL_RTR_FV_as_vc_arb_grant_winner_when_having_req, |TX_PATH.vc_arb_req |-> $onehot(TX_PATH.final_arb_grant)); \
             `SV_ASSERT (FVPL_RTR_FV_as_vc_arb_grant_when_having_req, |TX_PATH.vc_arb_req |-> |TX_PATH.final_arb_grant); \
           \
          end \
 \
        end \
 \
          `SV_ASSERT (FVPL_RTR_FV_as_tx_valid_after_grant, |TX_PATH.final_arb_grant |=> TX_PATH.tx_valid_o); \
 \
      end \
 \
  end

 `define RX_ARB_CHECKS(RX_ARB_CHECKS_LABEL, SIDE, RX_PATH, NUM_NOCS) begin: RX_ARB_CHECKS_LABEL \
     for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
  \
         fb_dw_rr_arb_sva #( \
  \
           .N             (RX_PATH.NUM_VC), \
           .LW            (RX_PATH.vc_arb.LW), \
           .CHECK         ("RX_VC_ARB_CHECK"), \
           .WW            (RX_PATH.vc_arb.WW) \
  \
           )  \
         cnoc_vc_arb_checker ( \
           .clk            (clk                           ), \
           .reset_n        (reset_n                       ), \
           .req            (RX_PATH.vc_arb_req            ), \
           .req_len        (RX_PATH.vc_arb_req_len        ), \
           .req_weights    (RX_PATH.dwrr_vc_weights       ), \
           .grant_accept   (RX_PATH.vc_arb_accept         ), \
           .grant          (RX_PATH.vc_arb_grant          ), \
           .grant_ix       (RX_PATH.vc_arb_grant_ix       ), \
           .deficit_credit (RX_PATH.vc_arb.deficit_credit ) \
         ); \
  \
         for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
  \
             fb_rr_arb_sva # ( \
              \
                 .N                    (RX_PATH.vc_loop[vc].genblk1.dest_arb.N), \
                 .TX_W                 (RX_PATH.TXID_W), \
                 .SRC_DIR              (SIDE), \
                 .LANE                 (num_of_nocs), \
                 .vc                   (vc), \
                 .CHECK                ("RX_DEST_ARB_CHECK") \
  \
               ) cip_rtr_dest_arb_checker ( \
              \
                 .clk             (clk),          \
                 .reset_n         (reset_n),      \
                 .req             (RX_PATH.dest_arb_req[vc]),          \
                 .grant_accept    (RX_PATH.dest_arb_accept[vc]),  \
                 .fifo_destid     (RX_PATH.fifo_destid[vc]), \
                 .vc_arb_grant    (RX_PATH.vc_arb_grant[vc]),        \
                 .grant_ix        (RX_PATH.dest_arb_grant_ix[vc]), \
                 .grant           (RX_PATH.dest_arb_grant[vc]) \
  \
               ); \
            if (num_of_nocs<LANES_CAN_TURN?!ILLEGAL_TGT_ID_TABLE[SIDE][LEAF0][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][LEAF0][vc]) begin \
               fb_rr_arb_sva # ( \
              \
                 .N                  (RX_PATH.vc_loop[vc].genblk1.genblk2.leaf_arb.N), \
                 .SRC_DIR            (SIDE), \
                 .TX_W               (RX_PATH.TXID_W), \
                 .LANE               (num_of_nocs), \
                 .vc                 (vc), \
                 .CHECK              ("RX_LEAF_ARB_CHECK") \
  \
               ) cip_rtr_leaf_arb_checker ( \
              \
                 .clk             (clk                        ),          \
                 .reset_n         (reset_n                    ),      \
                 .req             (RX_PATH.leaf_arb_req[vc]   ),          \
                 .grant_accept    (RX_PATH.leaf_arb_accept[vc]), \
                 .grant           (RX_PATH.leaf_arb_grant[vc] ),    \
                 .fifo_destid     (RX_PATH.fifo_destid[vc]    ), \
                 .vc_arb_grant    (RX_PATH.vc_arb_grant[vc]   ),        \
                 .grant_ix        (RX_PATH.vc_loop[vc].genblk1.genblk2.leaf_arb.grant_ix) \
  \
               ); \
             end \
  \
       end \
      \
     end \
 end

 `define LEAF_RX_ARB_CHECKS(RX_ARB_CHECKS_LABEL, SIDE, RX_PATH, NUM_NOCS) begin: RX_ARB_CHECKS_LABEL \
     for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
  \
         fb_dw_rr_arb_sva #( \
  \
           .N             (RX_PATH.NUM_VC), \
           .LW            (RX_PATH.vc_arb.LW), \
           .CHECK         ("RX_VC_ARB_CHECK"), \
           .WW            (RX_PATH.vc_arb.WW) \
  \
           )  \
         cnoc_vc_arb_checker ( \
           .clk            (clk                           ), \
           .reset_n        (reset_n                       ), \
           .req            (RX_PATH.vc_arb_req            ), \
           .req_len        (RX_PATH.vc_arb_req_len        ), \
           .req_weights    (RX_PATH.dwrr_vc_weights       ), \
           .grant_accept   (RX_PATH.vc_arb_accept         ), \
           .grant          (RX_PATH.vc_arb_grant          ), \
           .grant_ix       (RX_PATH.vc_arb_grant_ix       ), \
           .deficit_credit (RX_PATH.vc_arb.deficit_credit ) \
         ); \
  \
 end \
 end
 
 `define TX_ARB_CHECKS(TX_ARB_CHECKS_LABEL, SIDE, TX_PATH, NUM_NOCS) begin: TX_ARB_CHECKS_LABEL \
 \
    for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
     \
        for (genvar vc=0 ; vc < TOTAL_NUM_VC ; vc++) begin: per_vc \
     \
            fb_dw_rr_arb_sva #( \
                .N             (TX_PATH.vc_loop[vc].genblk1.q_arb_dwrr.N), \
                .LW            (TX_PATH.vc_loop[vc].genblk1.q_arb_dwrr.LW),  \
                .CHECK         ("TX_DW_RR_ARB_CHECK"), \
                .WW            (TX_PATH.vc_loop[vc].genblk1.q_arb_dwrr.WW), \
                .TX            (SIDE), \
                .vc            (vc), \
                .LANE          (num_of_nocs) \
            )  \
            q_arb_dwrr_checker ( \
                .clk         (clk               ), \
                .reset_n     (reset_n           ), \
                .req         (TX_PATH.q_arb_req[vc]     ), \
                .req_len     (TX_PATH.q_arb_req_len[vc] ), \
                .req_weights (TX_PATH.dwrr_src_weights  ), \
                .grant_accept(TX_PATH.q_arb_accept[vc]  ), \
                .grant       (TX_PATH.q_arb_grant[vc]   ), \
                .grant_ix    (TX_PATH.q_arb_grant_ix[vc]), \
                .deficit_credit (TX_PATH.vc_loop[vc].genblk1.q_arb_dwrr.deficit_credit  ) \
            ); \
 \
        end \
 \
        fb_dw_rr_arb_sva #( \
          .N(TX_PATH.vc_arb.N),  \
          .LW(TX_PATH.vc_arb.LW),  \
          .WW(TX_PATH.vc_arb.WW),  \
          .CHECK("TX_DW_RR_ARB_CHECK") \
          )  \
        vc_arb_checker ( \
          .clk         (clk              ), \
          .reset_n     (reset_n          ), \
          .req         (TX_PATH.vc_arb_req       ), \
          .req_len     (TX_PATH.vc_arb_req_len   ), \
          .req_weights (TX_PATH.dwrr_vc_weights  ), \
          .grant_accept(TX_PATH.vc_arb_accept    ), \
          .grant       (TX_PATH.vc_arb_grant     ), \
          .grant_ix    (TX_PATH.vc_arb_grant_ix  ), \
          .deficit_credit (TX_PATH.vc_arb.deficit_credit  ) \
        ); \
    end \
   \
end

 `define LEAF_TX_ARB_CHECKS(TX_ARB_CHECKS_LABEL, SIDE, TX_PATH, NUM_NOCS) begin: TX_ARB_CHECKS_LABEL  \
   \
   for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane      \
   \
        for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc  \
  \
              fb_rr_arb_sva # (  \
              \
                .N                (TX_PATH.NUM_RX),  \
                .CHECK            ("LEAF_TX_Q_ARB_CHECK"),  \
                .vc               (vc)  \
  \
              ) leaf_rr_arb_checker (  \
              \
                .clk             (clk),           \
                .reset_n         (reset_n),       \
                .req             (TX_PATH.vc_loop[vc].genblk1.q_arb.req),           \
                .grant_accept    (TX_PATH.vc_loop[vc].genblk1.q_arb.grant_accept),  \
                .grant           (TX_PATH.vc_loop[vc].genblk1.q_arb.grant),     \
                .grant_ix        (TX_PATH.vc_loop[vc].genblk1.q_arb.grant_ix)  \
  \
              );  \
  \
        end  \
  \
        fb_dw_rr_arb_sva #(   \
          .N(TX_PATH.vc_arb.N),    \
          .LW(TX_PATH.vc_arb.LW),    \
          .WW(TX_PATH.vc_arb.WW),    \
          .CHECK("TX_DW_RR_ARB_CHECK")   \
          )    \
        vc_arb_checker (   \
          .clk         (clk              ),   \
          .reset_n     (reset_n          ),   \
          .req         (TX_PATH.vc_arb_req       ),   \
          .req_len     (TX_PATH.vc_arb_req_len   ),   \
          .req_weights (TX_PATH.dwrr_vc_weights  ),   \
          .grant_accept(TX_PATH.vc_arb_accept    ),   \
          .grant       (TX_PATH.vc_arb_grant     ),   \
          .grant_ix    (TX_PATH.vc_arb_grant_ix  ),   \
          .deficit_credit (TX_PATH.vc_arb.deficit_credit  )   \
        );   \
        \
   end  \
 end


 ////////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_rtr_sub_block_check_defines.sv
/// This file contains the performance, rx buffer/fifo, tx fifo and arb checks macro defines
////////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- RX vc_buf check defines --
//------------------------------------------------------------------------------

  `define IO_EW_VC_BUF_CHECKS(VC_BUF_LABELS, SIDE, FIFO_DEPTH, RX_VC_BUF, NUM_NOCS) begin: VC_BUF_LABELS   \
    for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane   \
    for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc   \
        for (genvar ch=0; ch < cip_pkg::CIP_RTR_NUM_DIRECTIONS ; ch++) begin: per_dir   \
            if ((num_of_nocs<LANES_CAN_TURN)?!ILLEGAL_TGT_ID_TABLE[SIDE][ch][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][ch][vc]) begin: expected   \
              transaction_tracker_sva # (   \
                .DATA_WIDTH(1),   \
                .CHECKER_DEPTH(FIFO_DEPTH)   \
              ) cip_rtr_vc_buffer_checker (   \
                .data_in    (RX_VC_BUF.wdin[`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]),   \
                .in_valid   (RX_VC_BUF.we[ch]),   \
                .data_out   (RX_VC_BUF.rdout[0][`IS_REQUEST_VC?REQ_FIFO_CHECK_BIT:RESP_FIFO_CHECK_BIT]), \
                .out_valid  (RX_VC_BUF.re[ch]),   \
                .clk        (clk),   \
                .reset_n    (reset_n)   \
                ); \
              `SV_ASSERT (FVPL_RTR_FV_as_cip_rtr_rx_buffer_checker_no_buffer_underflow ,   RX_VC_BUF.empty[ch] |-> !RX_VC_BUF.re[ch]);   \
            end   \
            end \
            \
            `SV_ASSERT (FVPL_RTR_FV_as_cip_rtr_rx_buffer_checker_no_buffer_overflow ,   RX_VC_BUF.full |-> !|RX_VC_BUF.we ); \
            end   \
    end   \
  end


//------------------------------------------------------------------------------
//-- NSEW rx performance check defines --
//------------------------------------------------------------------------------

 `define IO_EW_RX_PERFORMANCE_CHECKS(RX_PERFORMANCE_CHECKS_LABEL, SIDE, RX_PATH, RX_VC_BUF, RX_VC_BUF_PRTNR, NUM_NOCS, NUM_DIRECTIONS) begin: RX_PERFORMANCE_CHECKS_LABEL \
 \
 for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane  \
 \
        for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
 \
            begin: dest_arb_performance_checker \
 \
              for (genvar tx=0; tx<NUM_DIRECTIONS ; tx++) begin: per_dir \
 \
              if (((num_of_nocs<LANES_CAN_TURN)?!ILLEGAL_TGT_ID_TABLE[SIDE][tx][vc]:!ILLEGAL_TGT_ID_TABLE_NOTURN[SIDE][tx][vc])) begin \
\
                    `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit  ,!RX_VC_BUF.empty[tx] && \
 \
                                                                        RX_PATH.credit_pool[tx][vc] > RX_VC_BUF.rlen[tx] |-> \
 \
                                                                        RX_PATH.dest_arb_req[vc][tx] ); \
 \
              end \
 \
              end \
              \
                `SV_ASSERT (FVPL_RTR_FV_as_dest_arb_grant_winner_when_having_requests   ,  (|RX_PATH.dest_arb_req[vc] |->  $onehot(RX_PATH.dest_arb_grant[vc]))); \
 \
            end \
 \
            begin: vc_arb_performance_checker \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_req_when_enough_credit     , !RX_PATH.fifo_empty[vc]   &&  RX_PATH.credit_pool[RX_PATH.fifo_destid[vc]][vc] > RX_PATH.fifo_len[vc] |->  RX_PATH.vc_arb_req[vc] ); \
 \
              `SV_ASSERT (FVPL_RTR_FV_as_tx_valid_after_grant        , RX_PATH.vc_arb_grant[vc] && |RX_PATH.fifo_destid[vc] |=> RX_PATH.tx_valid_o); \
 \
            end \
 \
      end \
     \
              `SV_ASSERT (FVPL_RTR_FV_as_vc_arb_grant_winner_when_having_requests   ,  (|RX_PATH.vc_arb_req |->  $onehot(RX_PATH.vc_arb_grant))); \
    end \
end

 `define IO_EW_RX_ARB_CHECKS(RX_ARB_CHECKS_LABEL, SIDE, RX_PATH, NUM_NOCS) begin: RX_ARB_CHECKS_LABEL \
     for (genvar num_of_nocs = 0; num_of_nocs<NUM_NOCS; num_of_nocs++) begin: per_lane \
  \
         fb_dw_rr_arb_sva #( \
  \
           .N             (RX_PATH.NUM_VC), \
           .LW            (RX_PATH.vc_arb.LW), \
           .CHECK         ("RX_VC_ARB_CHECK"), \
           .WW            (RX_PATH.vc_arb.WW) \
  \
           )  \
         cnoc_vc_arb_checker ( \
           .clk            (clk                           ), \
           .reset_n        (reset_n                       ), \
           .req            (RX_PATH.vc_arb_req            ), \
           .req_len        (RX_PATH.vc_arb_req_len        ), \
           .req_weights    (RX_PATH.dwrr_vc_weights       ), \
           .grant_accept   (RX_PATH.vc_arb_accept         ), \
           .grant          (RX_PATH.vc_arb_grant          ), \
           .grant_ix       (RX_PATH.vc_arb_grant_ix       ), \
           .deficit_credit (RX_PATH.vc_arb.deficit_credit ) \
         ); \
  \
         for (genvar vc=0; vc<TOTAL_NUM_VC; vc++) begin: per_vc \
  \
             fb_rr_arb_sva # ( \
              \
                 .N                    (RX_PATH.vc_loop[vc].genblk1.dest_arb.N), \
                 .TX_W                 (RX_PATH.TXID_W), \
                 .SRC_DIR              (SIDE), \
                 .LANE                 (num_of_nocs), \
                 .vc                   (vc), \
                 .CHECK                ("IO_EW_DEST_ARB_CHECK") \
  \
               ) cip_rtr_dest_arb_checker ( \
              \
                 .clk             (clk),          \
                 .reset_n         (reset_n),      \
                 .req             (RX_PATH.dest_arb_req[vc]),          \
                 .grant_accept    (RX_PATH.dest_arb_accept[vc]),  \
                 .fifo_destid     (RX_PATH.fifo_destid[vc]), \
                 .vc_arb_grant    (RX_PATH.vc_arb_grant[vc]),        \
                 .grant_ix        (RX_PATH.dest_arb_grant_ix[vc]), \
                 .grant           (RX_PATH.dest_arb_grant[vc]) \
  \
               ); \
      \
     end \
     end \
 end
 

 `define INTERRUPT_CHECKS(INTERRUPT_CHECKS_LABEL, RX_PATH, NUM_NOCS) begin: INTERRUPT_CHECKS_LABEL  \
  \
     for (genvar num_of_nocs=0 ; num_of_nocs < NUM_NOCS; num_of_nocs++) begin: per_lane  \
  \
         `SV_ASSERT(FVPL_RTR_FV_as_interrupt_checks_illegal_turn_err,   RX_PATH.rx_valid_i && RX_PATH.rx_destid[SOUTH] |->  RX_PATH.genblk8.illegal_turn_err);  \
         \
    end  \
 end

 `define LEAF_INTERRUPT_CHECKS(SIDE, LEAF, RX_PATH, NUM_NOCS) \
//  begin: INTERRUPT_CHECKS_LABEL \
//  \
//      for (genvar lane=0 ; lane < NUM_NOCS; lane++) begin: per_lane \
//  \
        `SV_ASSERT(FVPL_RTR_FV_as_``LEAF``2s``NUM_NOCS``_interrupt_checks,  `CIP_CRTR_SOUTH_TX(NUM_NOCS).rx_valid_i[SIDE] \
                                                     \
                                                     |-> ##2  \
                                                     \
                                                     `SOUTH_CSR_INTO_ABYSS(NUM_NOCS) ); 
//     end \
//  end \
 `define VC_INTERRUPT_CHECKS(NOC_TYPE, INTERRUPT_CHECKS_LABEL, RX_PATH, NUM_NOCS) begin: INTERRUPT_CHECKS_LABEL  \
  \
     for (genvar num_of_nocs=0 ; num_of_nocs < NUM_NOCS; num_of_nocs++) begin: per_lane  \
      \
        `SV_ASSERT(FVPL_RTR_FV_as_interrupt_checks_invalid_vc_req,   RX_PATH.rx_valid_i && RX_PATH.rx_ctrl_i.is_req && RX_PATH.rx_ctrl_i.`IS_REQ_VC_INVALID_RANGE  \
                                                      \
                                                     |->   \
                                                      \
                                                     RX_PATH.rx_intr.invalid_vc_set);  \
 \
      if ( NOC_TYPE != "DNOC") begin \
        `SV_ASSERT(FVPL_RTR_FV_as_interrupt_checks_invalid_vc_resp,   RX_PATH.rx_valid_i && !RX_PATH.rx_ctrl_i.is_req && RX_PATH.rx_ctrl_i.`IS_RESP_VC_INVALID_RANGE  \
                                                      \
                                                     |->   \
                                                      \
                                                     RX_PATH.rx_intr.invalid_vc_set);  \
      end \
 \
    end  \
 end