/////////////////////////////////////////////////////////////////////////////////////////
// File: transaction_tracker_sva.sv
// This file contains cip router transaction trackers
/////////////////////////////////////////////////////////////////////////////////////////

module transaction_tracker_sva # (

  parameter DATA_WIDTH          = 4,
            CHECKER_DEPTH       = 10,
            TYPE                = "E2E"
            
) (

  input     logic                           [DATA_WIDTH-1:0]                                                                        data_in,
  input     logic                                                                                                                   in_valid,

  input     logic                           [DATA_WIDTH-1:0]                                                                        data_out,
  input     logic                                                                                                                   out_valid,

  input     logic                                                                                                                   clk,
  input     logic                                                                                                                   reset_n

);

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);


//------------------------------------------------------------------------------
//-- Local Parameters --
//------------------------------------------------------------------------------

    localparam COUNTER_DEPTH = $clog2(CHECKER_DEPTH+1);

//------------------------------------------------------------------------------
//-- Auxilliary Code --
//------------------------------------------------------------------------------
`ifdef FORMAL
    logic                                       sampled_in_d;
    logic                                       ready_to_sample_in_d;
    logic [DATA_WIDTH-1:0]                      sym_data, ready_to_sample_out_d, sampled_out_d;
    logic [COUNTER_DEPTH-1:0]                   tracking_counter;
    logic                                       incr, decr;

    assign ready_to_sample_in_d                 = incr && (sym_data == data_in);

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            sampled_in_d     <= 1'b0;
        end else  begin
            sampled_in_d     <= sampled_in_d        || ready_to_sample_in_d;
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)   tracking_counter <= {COUNTER_DEPTH{1'b0}};
        else            tracking_counter <= tracking_counter + incr - decr;
    end

    assign  incr    = in_valid  && !sampled_in_d    ;
    assign  decr    = out_valid && !(&sampled_out_d);

    genvar i;
    generate
        for (i = 0; i < DATA_WIDTH; i++) begin: data_decomposition
            // Smart tracking logic
            always @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    sampled_out_d[i] <= 1'b0;
                end else  begin
                    sampled_out_d[i] <= sampled_out_d[i]    || ready_to_sample_out_d[i];
                end
            end
        
        
            assign ready_to_sample_out_d[i] =  decr && tracking_counter == 1;
        
        
        //------------------------------------------------------------------------------
        //-- Assertions --
        //------------------------------------------------------------------------------

        if (TYPE == "E2E") begin: high_prior
            `SV_ASSERT (FVPH_RTR_FV_as_main_data_check             ,   sampled_in_d && !sampled_out_d[i] && ready_to_sample_out_d[i] |-> sym_data[i] == data_out[i]      );
        
            `ifdef FORMAL  // liveness property, not handled by simulation
                `SV_ASSERT (FVPH_RTR_FV_as_main_liveness_check         ,   ready_to_sample_in_d && !sampled_out_d[i] |-> s_eventually (ready_to_sample_out_d[i]) );
            `endif  // ifdef FORMAL

        end else begin: low_prior

            `SV_ASSERT (FVPL_RTR_FV_as_main_data_check             ,   sampled_in_d && !sampled_out_d[i] && ready_to_sample_out_d[i] |-> sym_data[i] == data_out[i]      );
        
            `ifdef FORMAL  // liveness property, not handled by simulation
                `SV_ASSERT (FVPL_RTR_FV_as_main_liveness_check         ,   ready_to_sample_in_d && !sampled_out_d[i] |-> s_eventually (ready_to_sample_out_d[i]) );
            `endif  // ifdef FORMAL
        end

        end

    endgenerate

    
//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------
    /*@ASM Symbolic data used for intergrity check @*/
    // `SV_ASSERT (FVPH_RTR_FV_am_stable_am_sym_data          ,    ##1 $stable(sym_data) );
    generate
        if (TYPE == "E2E") begin: high_prior
            `SV_ASSERT (FVPH_RTR_FV_am_stable_am_sym_data          ,    ##1 $stable(sym_data) );
        end else begin: low_prior
            `SV_ASSERT (FVPL_RTR_FV_am_stable_am_sym_data          ,    ##1 $stable(sym_data) );
        end

    endgenerate
        

//------------------------------------------------------------------------------

`endif

endmodule

