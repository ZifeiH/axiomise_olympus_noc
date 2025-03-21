///////////////////////////////////////////////////
/// File: flow_control_sva.sv
/// This file contains flow control for unoc input
///////////////////////////////////////////////////

module flow_control # (
    parameter   MAX_ALLOWED_REQS                    = 10

) (
    input    logic                                           clk,
    input    logic                                           reset_n,
    input    logic                                           valid

);

//------------------------------------------------------------------------------
//-- Clock and Reset --
//------------------------------------------------------------------------------

    default clocking @(posedge clk); endclocking
    default disable iff (!reset_n);

//------------------------------------------------------------------------------
//-- Auxilliary Code --
//------------------------------------------------------------------------------

    localparam ALLOWED_REQS_WIDTH                   = $clog2(MAX_ALLOWED_REQS+1);

    // limiting number of requests
    logic [ALLOWED_REQS_WIDTH : 0]              request_counter;

    always @(posedge clk or negedge reset_n) begin
        if(!reset_n) begin
            request_counter     <=  {ALLOWED_REQS_WIDTH{1'b0}};
        end else begin
            request_counter     <=  request_counter + valid;
        end
    end

//------------------------------------------------------------------------------
//-- Assumptions --
//------------------------------------------------------------------------------
    `ifdef FORMAL

        /*@ASM flow control for routing data checks @*/
        `SV_ASSERT ( FVPH_RTR_FV_am_limit_reqs             ,   request_counter == MAX_ALLOWED_REQS |-> !valid );

    `endif
    

endmodule
