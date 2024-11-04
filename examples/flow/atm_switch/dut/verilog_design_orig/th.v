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

`resetall

module th;   
   
//
// Input Utopia interfaces x 8
//
wire       Rx_clk_0,   Rx_clk_1,   Rx_clk_2,   Rx_clk_3;
wire [7:0] Rx_data_0,  Rx_data_1,  Rx_data_2,  Rx_data_3;
wire       Rx_soc_0,   Rx_soc_1,   Rx_soc_2,   Rx_soc_3; 
wire       Rx_en_0,    Rx_en_1,    Rx_en_2,    Rx_en_3;  
wire       Rx_empty_0, Rx_empty_1, Rx_empty_2, Rx_empty_3;

wire       Rx_clk_4,   Rx_clk_5,   Rx_clk_6,   Rx_clk_7;
wire [7:0] Rx_data_4,  Rx_data_5,  Rx_data_6,  Rx_data_7;
wire       Rx_soc_4,   Rx_soc_5,   Rx_soc_6,   Rx_soc_7; 
wire       Rx_en_4,    Rx_en_5,    Rx_en_6,    Rx_en_7;  
wire       Rx_empty_4, Rx_empty_5, Rx_empty_6, Rx_empty_7;

//
// Output Utopia interfaces x 8
//
wire       Tx_clk_0,   Tx_clk_1,   Tx_clk_2,   Tx_clk_3;
wire [7:0] Tx_data_0,  Tx_data_1,  Tx_data_2,  Tx_data_3;
wire       Tx_soc_0,   Tx_soc_1,   Tx_soc_2,   Tx_soc_3; 
wire       Tx_en_0,    Tx_en_1,    Tx_en_2,    Tx_en_3;  
wire       Tx_full_0,  Tx_full_1,  Tx_full_2,  Tx_full_3;

wire       Tx_clk_4,   Tx_clk_5,   Tx_clk_6,   Tx_clk_7;
wire [7:0] Tx_data_4,  Tx_data_5,  Tx_data_6,  Tx_data_7;
wire       Tx_soc_4,   Tx_soc_5,   Tx_soc_6,   Tx_soc_7; 
wire       Tx_en_4,    Tx_en_5,    Tx_en_6,    Tx_en_7;  
wire       Tx_full_4,  Tx_full_5,  Tx_full_6,  Tx_full_7;

//
// Miscellaneous pins
//
 
reg  clk;
wire rst;

//
// Waveform traces
//
`ifdef VCD
initial $dumpvars;
`endif

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
vera_shell vshell(.SystemClock(SystemClock));
`endif

//
// Design under verification
//

`ifdef emu
/* DUT is in emulator, so not instantiated here */
`else
octopus duv(.Rx_clk_0  ( Rx_clk_0 ),
            .Rx_clk_1  ( Rx_clk_1 ),
            .Rx_clk_2  ( Rx_clk_2 ),
            .Rx_clk_3  ( Rx_clk_3 ),
            .Rx_data_0 ( Rx_data_0 ),
            .Rx_data_1 ( Rx_data_1 ),
            .Rx_data_2 ( Rx_data_2 ),
            .Rx_data_3 ( Rx_data_3 ),
            .Rx_soc_0  ( Rx_soc_0 ),
            .Rx_soc_1  ( Rx_soc_1 ),
            .Rx_soc_2  ( Rx_soc_2 ),
            .Rx_soc_3  ( Rx_soc_3 ),
            .Rx_en_0   ( Rx_en_0 ),
            .Rx_en_1   ( Rx_en_1 ),
            .Rx_en_2   ( Rx_en_2 ),
            .Rx_en_3   ( Rx_en_3 ),
            .Rx_empty_0( Rx_empty_0 ),
            .Rx_empty_1( Rx_empty_1 ),
            .Rx_empty_2( Rx_empty_2 ),
            .Rx_empty_3( Rx_empty_3 ),
            .Rx_clk_4  ( Rx_clk_4 ),
            .Rx_clk_5  ( Rx_clk_5 ),
            .Rx_clk_6  ( Rx_clk_6 ),
            .Rx_clk_7  ( Rx_clk_7 ),
            .Rx_data_4 ( Rx_data_4 ),
            .Rx_data_5 ( Rx_data_5 ),
            .Rx_data_6 ( Rx_data_6 ),
            .Rx_data_7 ( Rx_data_7 ),
            .Rx_soc_4  ( Rx_soc_4 ),
            .Rx_soc_5  ( Rx_soc_5 ),
            .Rx_soc_6  ( Rx_soc_6 ),
            .Rx_soc_7  ( Rx_soc_7 ),
            .Rx_en_4   ( Rx_en_4 ),
            .Rx_en_5   ( Rx_en_5 ),
            .Rx_en_6   ( Rx_en_6 ),
            .Rx_en_7   ( Rx_en_7 ),
            .Rx_empty_4( Rx_empty_4 ),
            .Rx_empty_5( Rx_empty_5 ),
            .Rx_empty_6( Rx_empty_6 ),
            .Rx_empty_7( Rx_empty_7 ),
            .Tx_clk_0  ( Tx_clk_0 ),
            .Tx_clk_1  ( Tx_clk_1 ),
            .Tx_clk_2  ( Tx_clk_2 ),
            .Tx_clk_3  ( Tx_clk_3 ),
            .Tx_data_0 ( Tx_data_0 ),
            .Tx_data_1 ( Tx_data_1 ),
            .Tx_data_2 ( Tx_data_2 ),
            .Tx_data_3 ( Tx_data_3 ),
            .Tx_soc_0  ( Tx_soc_0 ),
            .Tx_soc_1  ( Tx_soc_1 ),
            .Tx_soc_2  ( Tx_soc_2 ),
            .Tx_soc_3  ( Tx_soc_3 ),
            .Tx_en_0   ( Tx_en_0 ),
            .Tx_en_1   ( Tx_en_1 ),
            .Tx_en_2   ( Tx_en_2 ),
            .Tx_en_3   ( Tx_en_3 ),
            .Tx_full_0 ( Tx_full_0 ),
            .Tx_full_1 ( Tx_full_1 ),
            .Tx_full_2 ( Tx_full_2 ),
            .Tx_full_3 ( Tx_full_3 ),
            .Tx_clk_4  ( Tx_clk_4 ),
            .Tx_clk_5  ( Tx_clk_5 ),
            .Tx_clk_6  ( Tx_clk_6 ),
            .Tx_clk_7  ( Tx_clk_7 ),
            .Tx_data_4 ( Tx_data_4 ),
            .Tx_data_5 ( Tx_data_5 ),
            .Tx_data_6 ( Tx_data_6 ),
            .Tx_data_7 ( Tx_data_7 ),
            .Tx_soc_4  ( Tx_soc_4 ),
            .Tx_soc_5  ( Tx_soc_5 ),
            .Tx_soc_6  ( Tx_soc_6 ),
            .Tx_soc_7  ( Tx_soc_7 ),
            .Tx_en_4   ( Tx_en_4 ),
            .Tx_en_5   ( Tx_en_5 ),
            .Tx_en_6   ( Tx_en_6 ),
            .Tx_en_7   ( Tx_en_7 ),
            .Tx_full_4 ( Tx_full_4 ),
            .Tx_full_5 ( Tx_full_5 ),
            .Tx_full_6 ( Tx_full_6 ),
            .Tx_full_7 ( Tx_full_7 ),
            .clk         ( clk ),
            .rst         ( rst ) );
`endif



endmodule

