`define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 



