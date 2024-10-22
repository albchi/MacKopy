bind fifo_ctrl fifo_abs
   #( .DATA_WIDTH (`FIFOWIDTH),
      .DEPTH      (`FIFODEPTH))
i_fifo_abs
   ( .clk          (clk),
     .rst          (!resetn),
     .fifo_full    (fifo_full),
     .fifo_empty   (fifo_empty),
     .fifo_push    (push_req && push_ack),
     .fifo_pop     (pop_req && pop_ack),
     .wr_ptr       (wptr),
     .rd_ptr       (rptr)
   );
