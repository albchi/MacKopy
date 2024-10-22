`ifndef FIFODEPTH
  `define FIFODEPTH 8
`endif
`ifndef FIFOWIDTH
  `define FIFOWIDTH 32
`endif

module fifo_ctrl
  #(parameter DEPTH = `FIFODEPTH,
    parameter WIDTH = `FIFOWIDTH)
   (input logic              clk,
    input logic 	     resetn,
    input logic 	     push_req,
    output logic 	     push_ack,
    input logic [WIDTH-1:0]  data_in,
    input logic 	     pop_req,
    output logic 	     pop_ack,
    output logic [WIDTH-1:0] data_out);

   localparam PTRWD = $clog2(DEPTH);

   logic fifo_wren, fifo_rden;
   logic fifo_full, fifo_empty;
   logic [WIDTH-1:0] data [0:DEPTH-1];
   logic [PTRWD-1:0] wptr, rptr;
   logic [PTRWD:0]   fifo_cnts;

   assign fifo_empty = (fifo_cnts=='d0);
   assign fifo_full  = (fifo_cnts>=DEPTH);
   assign fifo_wren  = push_req & ~fifo_full;
   assign fifo_rden  = pop_req & ~fifo_empty;
   //assign push_ack   = ~fifo_full;
   assign push_ack   = 1;
   assign pop_ack    = ~fifo_empty;
   assign data_out   = data[rptr];

   always @(posedge clk or negedge resetn)
     if (!resetn) begin
	wptr <= 'd0;
     end else if (fifo_wren) begin
	wptr <= (wptr==(DEPTH-1))? 'd0 : (wptr + 'd1);
     end

   always @(posedge clk or negedge resetn)
     if (!resetn) begin
	rptr <= 'd0;
     end else if (fifo_rden) begin
	rptr <= (rptr==(DEPTH-1))? 'd0 : (rptr + 'd1);
     end

   always @(posedge clk)
     if (fifo_wren) data[wptr] <= data_in;

   always @(posedge clk or negedge resetn)
     if (!resetn) begin
	fifo_cnts <= 'd0;
     end else begin
	fifo_cnts <= fifo_cnts + fifo_wren - fifo_rden;
     end

endmodule
