module fifo_ctrl_checker
  #(parameter DEPTH = 8,
    parameter WIDTH = 32)
  (input logic             clk,
   input logic 		   resetn,
   input logic 		   push_req,
   input logic 		   push_ack,
   input logic [WIDTH-1:0] data_in,
   input logic 		   pop_req,
   input logic 		   pop_ack,
   input logic 		   fifo_full,
   input logic 		   fifo_empty,
   input logic [WIDTH-1:0] data_out);

    // assumptions
   property p_push_req_stable;
      @(posedge clk) disable iff (!resetn)
	(push_req && !push_ack) |=> push_req;
   endproperty
   property p_data_in_stable;
      @(posedge clk) disable iff (!resetn)
	(push_req && !push_ack) |=> $stable(data_in);
   endproperty
   property p_pop_req_stable;
      @(posedge clk) disable iff (!resetn)
	(pop_req && !pop_ack) |=> pop_req;
   endproperty

   asm_push_req_stable : assume property(p_push_req_stable);
   asm_data_in_stable  : assume property(p_data_in_stable);
   asm_pop_req_stable  : assume property(p_pop_req_stable);

   // assertions
   property p_no_underflow;
      @(posedge clk) disable iff (!resetn)
	fifo_empty |-> !pop_ack;
   endproperty
   property p_no_overflow;
      @(posedge clk) disable iff (!resetn)
	fifo_full |-> !push_ack;
   endproperty

   ast_no_underflow    : assert property(p_no_underflow);
   ast_no_overflow     : assert property(p_no_overflow);

   scoreboard
     #(.WIDTH   (WIDTH),
       .DEPTH   (DEPTH))
   scbd
     (.Resetn   (resetn),
      .Clk      (clk),
      .ValidIn  (push_req & push_ack),
      .DataIn   (data_in),
      .ValidOut (pop_req & pop_ack),
      .DataOut  (data_out));

endmodule
