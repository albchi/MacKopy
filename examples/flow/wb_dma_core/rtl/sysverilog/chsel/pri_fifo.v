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
// Name of the module   : DMA Priority fifo 
// Author               : Subha Amancherla 
// Project name         : Wishbone DMA/Bridge core
// Created on           : 09/23/2003
// Updated on           :
// Purpose of module    : Fifo to store priority reqs
// Comments             :
// *************************************************

module mod_pri_fifo(intf_wb_top.ch_sel intf_fifo,
		    input logic [5:0] prienc_fifo_data, 
			  logic prienc_fifo_wr, priarb_fifo_rd,
                
		    output logic [5:0] fifo_priarb_data, 
			   logic fifo_prienc_full, fifo_priarb_empty);

  logic [4:0] l_wr_addr, l_rd_addr;
  logic  [7:0] ram_block [31:0];
  logic [4:0] l_wr_addr_tmp, l_rd_addr_tmp; 
  bit b_up, b_down, b_half_full;
  logic [5:0] l_fifo_count;
  always @(l_wr_addr_tmp)
      l_wr_addr<= l_wr_addr_tmp;

  always @(l_rd_addr_tmp)
        l_rd_addr<= l_rd_addr_tmp;

  always_comb b_half_full 	= !intf_fifo.i_reset ? (l_fifo_count[5:0] >= 6'b010000) : 1'b0;
  always_comb fifo_prienc_full 	= !intf_fifo.i_reset ? (l_fifo_count[5:0] == 6'b100000) : 1'b0;
  always_comb fifo_priarb_empty = !intf_fifo.i_reset ? (l_fifo_count[5:0] == 6'b000000) : 1'b1;


  always_comb b_up   = (prienc_fifo_wr && !priarb_fifo_rd && !fifo_prienc_full)  ? 1'b1 : 1'b0; // during write
  always_comb b_down = (!prienc_fifo_wr && priarb_fifo_rd && !fifo_priarb_empty) ? 1'b1 : 1'b0; // during read


always_ff @ (posedge intf_fifo.i_clk or posedge intf_fifo.i_reset) 
	l_wr_addr_tmp  <= (intf_fifo.i_reset) ? 5'b0 : (~fifo_prienc_full & prienc_fifo_wr ? l_wr_addr : l_wr_addr++);

always_ff @ (posedge intf_fifo.i_clk or posedge intf_fifo.i_reset) 
	l_rd_addr_tmp  <= (intf_fifo.i_reset) ? 5'b0 : (~fifo_priarb_empty & priarb_fifo_rd ? l_rd_addr : l_rd_addr++);

//always_comb fifo_priarb_data = ram_block[l_rd_addr];
assign fifo_priarb_data = ram_block[l_rd_addr];

always_ff @ (posedge intf_fifo.i_clk or posedge intf_fifo.i_reset) 
        ram_block[l_rd_addr] <= (prienc_fifo_wr) ? prienc_fifo_data : ram_block[l_rd_addr];
 
always @ (negedge intf_fifo.i_clk or posedge intf_fifo.i_reset) // Has to operate on negedge
  begin
    if (intf_fifo.i_reset)
      l_fifo_count <= 6'b0;
    else
    begin
      if (b_up)
        l_fifo_count++;
      if (b_down)
        l_fifo_count--;
    end
  end
endmodule
