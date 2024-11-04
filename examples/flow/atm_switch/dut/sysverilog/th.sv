/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

//
//      Copyright (c) 2000 by Qualis Design Corporation. All rights reserved.
//      
//
//      This file contains licensed materials and may used and distributed
//      provided that this copyright statement is not removed from the file
//      and that any derivative work contains this copyright notice.
//
//      Qualis Design Corporation            Synopsys, Inc.
//      http://www.qualis.com                http://www.synopsys.com
//
// Description:
//      Test harness for ATM switch
//
// Author:      $Author: badri $
// Revision:    $Revision: 1.1 $
//

//Feature: interfaces


`include "interface.svh"

module th;   
   
// Input Utopia interfaces x 8
atm_interface rx_0();
atm_interface rx_1();
atm_interface rx_2();
atm_interface rx_3();
atm_interface rx_4();
atm_interface rx_5();
atm_interface rx_6();
atm_interface rx_7();

// Output Utopia interfaces x 8
atm_interface tx_0();
atm_interface tx_1();
atm_interface tx_2();
atm_interface tx_3();
atm_interface tx_4();
atm_interface tx_5();
atm_interface tx_6();
atm_interface tx_7();

//
// Miscellaneous pins
//
 
reg  clk;
wire rst;

//
// 100MHz system clock
//
initial
begin
   #10;
   forever begin
      clk = 1'b0;
      #5;
      clk = 1'b1;
      #5;
   end
end

//
// Dump control
//
initial begin
    if ($test$plusargs("dump"))
      $dumpvars();
end

//
// VERA interface
//
parameter simulation_cycle = 100 ;
  
reg  SystemClock ;
initial
begin
   SystemClock = 0 ;
   forever begin
      #(simulation_cycle/2) 
      SystemClock = ~SystemClock ;
   end
end

`ifdef NTB
main vshell(.SystemClock(SystemClock));
`else
vera_shell vshell(.*);
`endif


//
// Design under verification
//

//Feature:module port connection
octopus duv(.*);

endmodule

