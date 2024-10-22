`ifndef DIRECTIVE
  `define DIRECTIVE 0
`endif

bind packet_ctrl abstracted_counter
  #(.BIT_WIDTH (CNTS_WIDTH),
    .SPVALUE_1 (BUSY_CNTS),
    .SPVALUE_2 (READY_CNTS),
    .DIRECTIVE (`DIRECTIVE))
  abscnt
   (.clk    (clk),
    .rst    (rst),
    .clr    (clr_counts),
    .incr   (incr_counts),
    .counts (init_counts));

