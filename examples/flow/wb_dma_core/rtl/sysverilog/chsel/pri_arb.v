/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/


// *************************************************
// Name of the module   : DMA priority arbiter 
// Author               : Subha Amancherla 
// Project name         : Wishbone DMA/Bridge core
// Created on           : 09/23/2003
// Updated on           :
// Purpose of module    :
// Comments             :
// *************************************************

`include "inc_addr.v"

module mod_pri_arb (intf_wb_top.ch_sel intf_arb,
		    input  logic prienc_priarb_start_arb, 
			   logic [7:0] fifo_priarb_empty,
		      	   logic [5:0] fifo_priarb_data [7:0],
		    output logic [7:0] priarb_fifo_rd);

 
parameter p_pri_arb_idle 	  = 3'b000;
parameter p_pri_arb_rdfifo  	  = 3'b001;
parameter p_pri_arb_rddata  	  = 3'b010;
parameter p_pri_arb_wait_nc 	  = 3'b011;
parameter p_pri_arb_set_dma_start = 3'b100;

logic [5:0] 	l_sel;
logic		l_start_arb;
logic [2:0]	l_pri; 
logic [3:0] 	l_priarb_state;


always_comb intf_arb.chsel_dma_sel_val = l_sel;

always @ (posedge intf_arb.i_clk or posedge intf_arb.i_reset)
begin

	if (intf_arb.i_reset == 'b1)
	begin
		l_priarb_state <= p_pri_arb_idle;
		l_start_arb    <= 'b0;
		l_pri          <= 'd0;
		l_sel 	       <= 'd0;
		priarb_fifo_rd <= 'b0;
	end
	else
	begin
	if (prienc_priarb_start_arb == 'b1)
		l_start_arb <= 'b1;

	case (l_priarb_state)
	p_pri_arb_idle :
	begin
		if (prienc_priarb_start_arb )
		begin
		   priority if(p_pri_sel == 2'b10)
			l_pri <= 'b111;
		   else if (p_pri_sel == 2'b01)
			l_pri <= 'b100;
		   else if (p_pri_sel == 2'b00)
			l_pri <= 'b010;
		    l_priarb_state <= p_pri_arb_rdfifo;
		    l_start_arb <= 'b0;
		    priarb_fifo_rd <= 7'b0;
                    intf_arb.chsel_dma_start <= 0;
		end // l_start_arb
	end // p_idle
	
	p_pri_arb_rdfifo :
	begin
                intf_arb.chsel_dma_start <= 0;
		if (fifo_priarb_empty[l_pri] == 'b0)
		begin
			priarb_fifo_rd[l_pri] <= 1'b1;
			l_priarb_state <= p_pri_arb_rddata;
		end
		else
			l_pri--;
	end // p_pri_arb_rdfifo

	p_pri_arb_rddata:
	begin
		l_sel <= fifo_priarb_data[l_pri];
		priarb_fifo_rd[l_pri] <= 1'b0;
		l_priarb_state <= p_pri_arb_set_dma_start;
	end // p_pri_arb_rddata

	p_pri_arb_set_dma_start:
	begin
                intf_arb.chsel_dma_start <= 1;
		l_priarb_state <= p_pri_arb_wait_nc;
	end

	p_pri_arb_wait_nc:
	begin
                intf_arb.chsel_dma_start <= 0;
		if (intf_arb.dma_chsel_next_ch == 'b1 && l_pri >= 'd0)
			l_priarb_state <= p_pri_arb_rdfifo;
		else if (intf_arb.dma_chsel_next_ch == 'b1 && l_pri < 'd0)
			l_priarb_state <= p_pri_arb_idle;
	end // p_pri_arb_wait_nc
	endcase
	end // else
end // always

endmodule

	

