/////////////////////////////////////////////////////////////////////////////////////////
// File: credit_release_counter_sva.sv
// This file contains cip router credit counters
/////////////////////////////////////////////////////////////////////////////////////////

module credit_counter_TX_sva # (

  parameter TX_CREDITS           = 4,
  parameter LEN_WIDTH            = cip_pkg::CIP_DAXI_ID_LEN_WIDTH,
  parameter CREDIT_RELEASE_OPT   = 0

) (

  input     logic                                                     noc_out_valid,
  input     logic                                                     noc_out_credit_release,
  input     logic [LEN_WIDTH-1:0]                                     noc_out_len,
  input     logic                                                     noc_out_last,
  
  input     logic                                                     clk,
  input     logic                                                     reset_n

);

  localparam CREDIT_WIDTH                           = $clog2(TX_CREDITS+2);
  localparam LOCK_CREDIT_RELEASE                    = 0;

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);


//------------------------------------------------------------------------------
//-- Auxilliary Code --
//------------------------------------------------------------------------------
      
    logic [CREDIT_WIDTH-1:0]                        credit_counter     ;
    logic                                           enough_credit      ;
    logic                                           pending_credit     ;
    logic                                           first_beat         ;

    always_ff @(posedge clk or negedge reset_n) begin
      if (~reset_n) begin
            credit_counter      <= TX_CREDITS[CREDIT_WIDTH-1:0] ;
      end
      else begin
            credit_counter      <= credit_counter  +  noc_out_credit_release - noc_out_valid ;       
      end
    end


    always_ff @(posedge clk or negedge reset_n) begin
      if (~reset_n) begin
            first_beat      <= 1'b1;
      end
      else begin
            first_beat      <= noc_out_valid ? noc_out_last : '1;       
      end
    end

    assign enough_credit        = (credit_counter > noc_out_len) || (credit_counter == noc_out_len && noc_out_credit_release);
    assign pending_credit       = credit_counter <  TX_CREDITS;

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------
 
    `SV_ASSERT (FVPH_RTR_FV_am_no_credit_release_when_no_pkt         ,    credit_counter == TX_CREDITS[CREDIT_WIDTH-1:0]   |->              !noc_out_credit_release   );

    `ifdef FORMAL
    generate if (CREDIT_RELEASE_OPT==1) begin: routing_checks_opt_credit_assumptions
        `SV_ASSERT (FVPH_RTR_FV_am_credit_release_with_pending_pkt       ,    pending_credit                                 |-> ##[4:5]  noc_out_credit_release   );
    end
    
    begin: regular_credit_assumptions
    `SV_ASSERT (FVPH_RTR_FV_am_credit_release_with_pending_pkt       ,    pending_credit                                 |-> s_eventually  noc_out_credit_release   );
    end
    endgenerate
    `endif

//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------

    `SV_ASSERT (FVPH_RTR_FV_as_no_input_traffic_overflow        ,    noc_out_valid     && first_beat                |->   enough_credit   );

//------------------------------------------------------------------------------
//-- Covers --
//------------------------------------------------------------------------------

    `SV_COVER (FVPH_RTR_FV_co_no_credit_release_when_no_pkt          ,    credit_counter == TX_CREDITS[CREDIT_WIDTH-1:0]   && !noc_out_credit_release             );
    `SV_COVER (FVPH_RTR_FV_co_unoc_credit_is_0_but_len_is_not        ,    noc_out_valid                                  &&  enough_credit                        );
    `SV_COVER (FVPH_RTR_FV_co_unoc_input_tx_no_enough_credits        ,    !enough_credit                                                                            );
    `SV_COVER (FVPH_RTR_FV_co_counter_is_0                           ,    credit_counter == 0                                                                       );
    `SV_COVER (FVPH_RTR_FV_co_counter_can_be_replenished             ,    credit_counter == 0 ##[0:$]                credit_counter == TX_CREDITS[CREDIT_WIDTH-1:0] );

endmodule



module credit_counter_RX_sva # (

  parameter RX_CREDITS   = 4,
  parameter LEN_WIDTH    = cip_pkg::CIP_DAXI_ID_LEN_WIDTH

            
) (

  input     logic                                                               noc_in_valid,
  input     logic                                                               noc_in_credit_release,
  input     logic  [LEN_WIDTH - 1 : 0]                                          noc_in_len,
  input     logic                                                               noc_in_last,
                
  input     logic                                                               clk,
  input     logic                                                               reset_n

);

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);

//------------------------------------------------------------------------------
//-- Auxilliary Code --
//------------------------------------------------------------------------------
      
    localparam RX_CREDIT_WIDTH                         = $clog2(RX_CREDITS+2);

    logic [RX_CREDIT_WIDTH-1:0]                     credit_counter     ;
    logic                                           enough_credit   ;
    logic                                           pending_credit     ;
    logic                                           first_beat         ;

    always_ff @(posedge clk or negedge reset_n) begin
      if (~reset_n) begin
            credit_counter      <= RX_CREDITS[RX_CREDIT_WIDTH-1:0] ;
      end
      else begin
            credit_counter      <= credit_counter  +  noc_in_credit_release - noc_in_valid ;       
      end
    end

    always_ff @(posedge clk or negedge reset_n) begin
      if (~reset_n) begin
            first_beat      <= 1'b1;
      end
      else begin
            first_beat      <= noc_in_valid ? noc_in_last : '1;       
      end
    end


    assign enough_credit        = (credit_counter > noc_in_len) || (credit_counter == noc_in_len && noc_in_credit_release) ;
    assign pending_credit       =  credit_counter <  RX_CREDITS;

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------
 
    `SV_ASSERT (FVPH_RTR_FV_am_no_input_traffic_overflow      ,    noc_in_valid  && first_beat  |-> enough_credit      );

//------------------------------------------------------------------------------
//-- Assertions --
//------------------------------------------------------------------------------
    // If vc value is invalid, this will fail. For AMN-9
    `ifndef ONLY_INTERRUPT_CHECKS
    `SV_ASSERT (FVPH_RTR_FV_as_credit_no_exceed_init          ,    credit_counter == RX_CREDITS[RX_CREDIT_WIDTH-1:0]    |->  !noc_in_credit_release   );
    `endif
    `ifdef FORMAL
      `SV_ASSERT (FVPH_RTR_FV_as_credit_release_with_pending_pkt   ,    pending_credit                                       |-> s_eventually  noc_in_credit_release   );
    `endif

//------------------------------------------------------------------------------
//-- Covers --
//------------------------------------------------------------------------------

    `SV_COVER (FVPH_RTR_FV_co_liveness_on_traffic_injection          ,    credit_counter == RX_CREDITS[RX_CREDIT_WIDTH-1:0]  &&  noc_in_valid);
    `SV_COVER (FVPH_RTR_FV_co_counter_can_be_replenished                  ,    credit_counter == 0 ##[0:$] credit_counter == RX_CREDITS[RX_CREDIT_WIDTH-1:0] );

endmodule


