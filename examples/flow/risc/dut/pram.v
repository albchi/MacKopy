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
// Synchornous Data RAM, 12x2048
//
// Replace with your actual memory model..
//
module pram (
   clk,
   address,
   we,
   din,
   dout
);

input		clk;
input [10:0]	address;
input		we;
input [11:0]	din;
output [11:0]	dout;

// synopsys translate_off
parameter word_depth = 2048;

reg [10:0]	address_latched;

// Instantiate the memory array itself.
reg [11:0]	mem[0:word_depth-1];

// Latch address
always @(posedge clk)
   address_latched <= address;
   
// READ
assign dout = mem[address_latched];

// WRITE
always @(posedge clk)
   if (we) mem[address] <= din;

// synopsys translate_on

endmodule
