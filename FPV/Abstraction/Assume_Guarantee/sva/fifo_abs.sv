module fifo_abs #(
   parameter DATA_WIDTH = 64,
   parameter DEPTH = 64,
   parameter ADDR_WIDTH = $clog2(DEPTH)
)(
   input [ADDR_WIDTH-1:0] wr_ptr,
   input [ADDR_WIDTH-1:0] rd_ptr,
   input                  fifo_full,
   input                  fifo_empty,
   input                  fifo_push,
   input                  fifo_pop,
   input                  clk,
   input                  rst
);

// Delayed reset signal for adding constraints on the 1st cycle after reset
reg rst_1d;
always @(posedge clk) begin
   rst_1d <= rst;
end

fa_wr_rd_ptr_eq_aftr_rst:
   assert property (@(posedge clk) disable iff (rst)
   rst_1d |-> wr_ptr == rd_ptr
);

// fifo shouldn't be full if fifo is empty
fa_fifo_not_full_if_empty:
   assert property (@(posedge clk) disable iff (rst)
   fifo_empty |-> !fifo_full
);

// if wrptr and rdptrs are equal and fifo is not empty then fifo is full
fa_wr_rd_ptr_eq_and_fifo_not_empty_imp_fifo_full:
   assert property (@(posedge clk) disable iff (rst)
   (wr_ptr==rd_ptr) && !fifo_empty |-> fifo_full
);

// if fifo is full and no data has been poped then fifo remains full
fa_fifo_full_and_no_pop_imp_fifo_full:
   assert property (@(posedge clk) disable iff (rst)
   fifo_full && !fifo_pop |=> fifo_full
);

//// if fifo is full and data is pushed and poped at the same time then fifo remains full
//fa_fifo_full_push_and_pop_imp_fifo_full:
//   assert property (@(posedge clk) disable iff (rst)
//   fifo_full && fifo_push && fifo_pop |=> fifo_full
//);

// if data is poped and no new data pushed then fifo is not full:
fa_fifo_pop_and_no_push_imp_fifo_not_full:
   assert property (@(posedge clk) disable iff (rst)
   !fifo_push && fifo_pop |=> !fifo_full
);
endmodule
