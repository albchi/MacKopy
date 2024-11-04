/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

`ifndef __INC_ROUTER_TEST_TOP_SV__
`define __INC_ROUTER_TEST_TOP_SV__
`timescale 1ns/100ps
module router_test_top;
  parameter simulation_cycle = 100 ;
  bit  SystemClock;

  router_io sigs(SystemClock);
  host_io   host(SystemClock);
  router    dut(sigs, host);

  initial begin
    $vcdpluson;
    forever #(simulation_cycle/2) SystemClock = ~SystemClock ;
  end
  
endmodule  
`endif
