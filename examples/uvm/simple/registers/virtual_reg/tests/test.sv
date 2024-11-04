/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

program automatic test;
import uvm_pkg::*;

`include "./test_collection.sv"

initial begin
  $timeformat(-9, 1, "ns", 10);
  uvm_reg::include_coverage("*",UVM_CVR_ALL);
  run_test();
end

endprogram
