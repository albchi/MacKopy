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
// Name of the module   : channel select top module
// Author               : Subha Amancherla 
// Project name         : Wishbone DMA/Bridge core
// Created on           : 09/23/2003
// Updated on           :
// Purpose of module    : Interconnect all the modules in channel select
// Comments             :
// *************************************************

module mod_ch_top(intf_wb_top.ch_sel intf_chsel) ;

parameter [1:0] pri_sel = 2'h0;

logic[5:0]	prienc_fifo_data [7:0], fifo_priarb_data [7:0];
logic[7:0] 	fifo_prienc_full, fifo_priarb_empty, prienc_fifo_wr, priarb_fifo_rd;

logic 		prienc_priarb_start_arb;


//==================================================================================
// Instanciating 7 fifos
genvar nfifo;
generate for (nfifo = 0; nfifo < 8; nfifo++)
begin :inst_fifo
mod_pri_fifo u_pri_fifo (intf_chsel, prienc_fifo_data[nfifo], prienc_fifo_wr[nfifo], 
			 priarb_fifo_rd[nfifo],fifo_priarb_data[nfifo],
			 fifo_prienc_full[nfifo],fifo_priarb_empty[nfifo]);

end // inst_fifo
endgenerate

mod_pri_mux u_pri_mux (intf_chsel);

mod_pri_enc u_pri_enc (intf_chsel, fifo_prienc_full,prienc_priarb_start_arb,
		       prienc_fifo_data, prienc_fifo_wr ); 

mod_pri_arb u_pri_arb (intf_chsel, prienc_priarb_start_arb, fifo_priarb_empty, 
		       fifo_priarb_data,priarb_fifo_rd );

endmodule
