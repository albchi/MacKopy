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
// Name of the module 	: Wishbone Top (wb_dma_top)
// Author 	  	: Subha Amancherla
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 1st October,2003
// Updated on 		: 
// Purpose of module	: Wishbone top module consisting of interface instance 
// Comments		:
// ********************************************************************************************

`include "inc_addr.v"

// ********************** Parameters Declaration ***********************************
parameter		p_rf_addr   = 0;        // Internal register file address
parameter	[1:0]	p_pri_sel   = 2'b0;	// Priority level	
parameter		p_ch_count  = 1;		// Total Dma channel supported
parameter	[3:0]	p_ch0_conf  = 4'h1;	// Abilities of each channel chN_conf
parameter	[3:0]	p_ch1_conf  = 4'h0;
parameter	[3:0]	p_ch2_conf  = 4'h0;
parameter	[3:0]	p_ch3_conf  = 4'h0;
parameter	[3:0]	p_ch4_conf  = 4'h0;
parameter	[3:0]	p_ch5_conf  = 4'h0;
parameter	[3:0]	p_ch6_conf  = 4'h0;
parameter	[3:0]	p_ch7_conf  = 4'h0;
parameter	[3:0]	p_ch8_conf  = 4'h0;
parameter	[3:0]	p_ch9_conf  = 4'h0;
parameter	[3:0]	p_ch10_conf = 4'h0;
parameter	[3:0]	p_ch11_conf = 4'h0;
parameter	[3:0]	p_ch12_conf = 4'h0;
parameter	[3:0]	p_ch13_conf = 4'h0;
parameter	[3:0]	p_ch14_conf = 4'h0;
parameter	[3:0]	p_ch15_conf = 4'h0;
parameter	[3:0]	p_ch16_conf = 4'h0;
parameter	[3:0]	p_ch17_conf = 4'h0;
parameter	[3:0]	p_ch18_conf = 4'h0;
parameter	[3:0]	p_ch19_conf = 4'h0;
parameter	[3:0]	p_ch20_conf = 4'h0;
parameter	[3:0]	p_ch21_conf = 4'h0;
parameter	[3:0]	p_ch22_conf = 4'h0;
parameter	[3:0]	p_ch23_conf = 4'h0;
parameter	[3:0]	p_ch24_conf = 4'h0;
parameter	[3:0]	p_ch25_conf = 4'h0;
parameter	[3:0]	p_ch26_conf = 4'h0;
parameter	[3:0]	p_ch27_conf = 4'h0;
parameter	[3:0]	p_ch28_conf = 4'h0;
parameter	[3:0]	p_ch29_conf = 4'h0;
parameter	[3:0]	p_ch30_conf = 4'h0;


// **********************  Module wb_dma_top ***********************************
module wb_dma_top(
 input   bit               i_clk, i_reset,                           // Global Clk & Reset (clk_i, rst_i) 
                           i_mast0_ack, i_mast1_ack,		     // Mast Ack Input (ack_i)
                           i_mast0_err, i_mast1_err,		     // Mast error (err_i)
                           i_mast0_retry, i_mast1_retry,	     // Mast retry input (rty_i)
                           i_slv0_strb, i_slv1_strb,		     // Slave Strobe (stb_i)
                           i_slv0_cyc,i_slv1_cyc,		     // Slave cyc valid (cyc_i)
         logic             i_slv0_we,i_slv1_we,			     // Slave Write (we_i)
         logic4 	   i_slv0_byte_sel, i_slv1_byte_sel,	     // Slave byte sel (sel_i)
         logic32           i_mast0_data, i_slv0_data, i_slv0_addr,   // Addr (addr_i, m_data_i)
                           i_mast1_data, i_slv1_data, i_slv1_addr,
                           i_dma_nd, i_dma_req,i_dma_rest,	     // (dma_nd_i, dma_rest_i, dma_req_i)
output   bit               o_mast0_cyc, o_mast0_we,		     // (we_o,cyc_o)
                           o_mast1_cyc, o_mast1_we,
			   o_mast0_strb, o_mast1_strb,		     // Mast Strobe (stb_o)
                           o_slv0_ack, o_slv1_ack, 		     // (ack_o)
			   o_slv0_err,o_slv1_err,		     // (err_o)
                           o_slv0_retry, o_slv1_retry,		     // (rty_o)
                           o_inta, o_intb,			     // Interrupt (inta_o, intb_o) 
        wire [31:0] 	   o_mast0_data, o_mast0_addr, o_slv0_data,  // (m_data_o, addr_o)
                           o_mast1_data, o_mast1_addr,o_slv1_data,
			   o_ack,				     // (dma_ack_o)

        logic4	           o_mast0_byte_sel,o_mast1_byte_sel	     // (sel_o)
        );


// ********************** Instanciating interface ***********************************
intf_wb_top u_intf_wb_top(
			 i_clk, i_reset,
                         i_mast0_ack, i_mast1_ack,
                         i_mast0_err, i_mast1_err,
                         i_mast0_retry, i_mast1_retry,
                         i_slv0_strb, i_slv1_strb,
                         i_slv0_cyc,i_slv1_cyc,
                         i_slv0_we,i_slv1_we,
                   	 i_slv0_byte_sel, i_slv1_byte_sel,
	                 i_mast0_data, i_slv0_data, i_slv0_addr,
                         i_mast1_data, i_slv1_data, i_slv1_addr,
                         i_dma_nd, i_dma_req,i_dma_rest,
         	         o_mast0_cyc, o_mast0_we,
                         o_mast1_cyc, o_mast1_we,
                         o_inta, o_intb, o_mast0_strb, o_mast1_strb,
                         o_slv0_ack, o_slv1_ack, o_slv0_err,o_slv1_err,
                         o_slv0_retry, o_slv1_retry,
                  	 o_mast0_data, o_mast0_addr, o_slv0_data,
                         o_mast1_data, o_mast1_addr,o_slv1_data,
	                 o_mast0_byte_sel,o_mast1_byte_sel,
         	         o_ack
        );


// ********************** Module Instanciating ***********************************
mod_dma_eng  u_dma_eng 	(.intf_dma_eng 		(u_intf_wb_top));
reg_file     u_reg_file (.regfile_intf_wb_top	(u_intf_wb_top));
mod_ch_top   u_ch_sel   (.intf_chsel		(u_intf_wb_top));
wbif	     u_wb_if    (.intf_top		(u_intf_wb_top));

endmodule
