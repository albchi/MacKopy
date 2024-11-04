/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/


// ********************************************************************************************
// Name of the module 	: Dma Engine counter 
// Author 	  	: Subha Amancherla
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 1st, sept  2003
// Updated on 		: 
// Purpose of module	: Functionality of DMA engine counter is incorporated in here
// Comments		:
// ********************************************************************************************

module wb_dma_inc30r(
input	bit 	clk,
input	logic [29:0]	in,
output	logic [29:0]	out
);

// p_inc31_centre indicates the center bit of the 30 bit incrementor
// so it can be easily manually optimized for best performance
parameter	p_inc31_centre = 16;

reg	[p_inc31_centre:0]	out_r;

always @(posedge clk)
	out_r <= #1 in[(p_inc31_centre - 1):0] + 1;

always_comb out[29:p_inc31_centre] 	 = in[29:p_inc31_centre] + out_r[p_inc31_centre];
always_comb out[(p_inc31_centre - 1):0]  = out_r;

endmodule

