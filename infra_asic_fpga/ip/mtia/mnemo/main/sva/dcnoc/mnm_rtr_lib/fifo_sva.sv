/////////////////////////////////////////////////////////////////////////////////////////
// File: fifo_sva.sv
// This file contains cip router fifo checks for dcnoc
/////////////////////////////////////////////////////////////////////////////////////////

module fb_fifo_tb
#(
    parameter DEPTH = 1,
    parameter WIDTH = 1,
    parameter ENTRY_COUNTER_WIDTH = $clog2(DEPTH+1)
)
(
    input logic [WIDTH-1:0] out,
    input logic full,
    input logic empty,

    input logic [ENTRY_COUNTER_WIDTH-1:0] count,

    input push,
    input pop,
    input [WIDTH-1:0] in,

    input clk,
    input reset_n,
    input scan
);

  default clocking @(posedge clk); endclocking
  default disable iff (!reset_n);

  /*@ASM scan tied to low @*/
  `SV_ASSERT (FVPL_RTR_FV_am_scan_tied_low, !scan);
  logic [WIDTH-1:0] symb_data;
  /*@ASM  symb_data keeps its value the same after reset @*/
  `SV_ASSERT (FVPL_RTR_FV_am_symb_data_fixed, ##1 $stable(symb_data));

  logic sample_it;                  
  logic sampling_in, sampling_out;  
  logic sampled_in,  sampled_out;   

  // tracking counter
  logic [$clog2(DEPTH):0] tracking_counter;            
  logic tracking_counter_incr, tracking_counter_decr;  

  assign tracking_counter_incr = !sampled_in  && push;  
  assign tracking_counter_decr = !sampled_out && pop;   

  always_ff @(posedge clk or negedge reset_n) begin
  	if (~reset_n) begin
  	  tracking_counter <= '0;
  	end
  	else begin
  	  tracking_counter <= tracking_counter + tracking_counter_incr - tracking_counter_decr;
  	end
  end

  assign sampling_in  = !sampled_in && push && (in == symb_data) && sample_it;
  assign sampling_out =  sampled_in && pop  && (tracking_counter == 1);

  always_ff @(posedge clk or negedge reset_n) begin
  	if (~reset_n) begin
  	  sampled_in  <= 0;
      sampled_out <= 0;
    end
    else begin
      sampled_in  <= sampled_in  || sampling_in;
      sampled_out <= sampled_out || sampling_out;
    end
  end

  `ifndef ONLY_FIFO_COVERS
    genvar k;
    for (k=0; k<WIDTH; k++) begin : symb_data_single_bit
      `SV_ASSERT (FVPL_RTR_FV_as_fifo_ordering_check_per_bit, sampling_out |-> out[k] == symb_data[k]);
    end
  `endif

  logic [$clog2(DEPTH):0] tb_counter;

  always_ff @(posedge clk or negedge reset_n) begin
    if (~reset_n) begin
      tb_counter <= '0;
    end
    else begin
      tb_counter <= tb_counter + push - pop;
    end
  end

  `ifndef ONLY_FIFO_COVERS

    `SV_ASSERT (FVPL_RTR_FV_as_fifo_no_overflow_check                           ,        full         |-> !push             );
    `SV_ASSERT (FVPL_RTR_FV_as_fifo_no_underflow_check                          ,        empty        |-> !pop              );
    `SV_ASSERT (FVPL_RTR_FV_as_fifo_ordering_check                              ,        sampling_out |->  out == symb_data );

    `ifdef GEN_FIFO_COUNT_CHECKS
      `SV_ASSERT (FVPL_RTR_FV_as_empty_has_its_expected_value                   ,        empty == (tb_counter == '0)        );
      `SV_ASSERT (FVPL_RTR_FV_as_full_has_its_expected_value                    ,        full  == (tb_counter == DEPTH)     );
      `SV_ASSERT (FVPL_RTR_FV_as_count_has_its_expected_value                   ,        count == tb_counter                );
    `endif
    
    `SV_ASSERT (FVPL_RTR_FV_as_fifo_full_next_cycle_not_empty_check        ,        full         |=> !empty  );
    `SV_ASSERT (FVPL_RTR_FV_as_fifo_empty_next_cycle_not_full_check        ,        empty        |=> !full   );
    `SV_ASSERT (FVPL_RTR_FV_as_fifo_empty_full_not_high_same_time_check    ,        (empty && full) == 0     );

  `endif

  `SV_COVER  (FVPL_RTR_FV_co_fifo_can_be_non_empty_check                      ,        !empty );
  `SV_COVER  (FVPL_RTR_FV_co_fifo_can_be_full_check                           ,        full );

endmodule
