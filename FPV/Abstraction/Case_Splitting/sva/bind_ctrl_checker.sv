
`ifndef SPLIT_MODE
 `define SPLIT_MODE 0
`endif
`ifndef DATA_INTEG
 `define DATA_INTEG 0
`endif

bind ctrl ctrl_checker
  #(.DATA_WIDTH (DATA_WIDTH),
    .LEN_WIDTH  (LEN_WIDTH),
    .DATA_INTEG (`DATA_INTEG),
    .SPLIT_MODE (`SPLIT_MODE))
chkr (.*);
