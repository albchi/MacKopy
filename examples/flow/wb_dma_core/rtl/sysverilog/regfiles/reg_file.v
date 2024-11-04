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
// Name of the module 	: Interface signals for regfile u_interface.v
// Author 	  	: Subhasree Amancherla
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: Interface module for the register file.
// Comments		:
// ********************************************************************************************

`include "inc_addr.v"

module reg_file(intf_wb_top.regfile  regfile_intf_wb_top);

logic 	swptr_adr_reach;
bit     l_adec_enable_ch_main_csr,
	l_adec_enable_int_maska,
	l_adec_enable_int_maskb,
	l_adec_enable_int_srca,
	l_adec_enable_int_srcb;

logic [31:0]    l_adec_enable_ch_csr,
		l_adec_enable_ch_sz,
		l_adec_enable_ch_a0 ,
        	l_adec_enable_ch_am0, 
		l_adec_enable_ch_a1,
		l_adec_enable_ch_am1,
        	l_adec_enable_ch_desc,
		l_adec_enable_ch_swpt;


addr_dec  adr_dec_top (
			l_adec_enable_ch_main_csr,
			l_adec_enable_int_maska,
			l_adec_enable_int_maskb,
			l_adec_enable_int_srca,
			l_adec_enable_int_srcb,
			l_adec_enable_ch_csr,
			l_adec_enable_ch_sz,
			l_adec_enable_ch_a0,
			l_adec_enable_ch_am0,
			l_adec_enable_ch_a1,
			l_adec_enable_ch_am1,
			l_adec_enable_ch_desc,
			l_adec_enable_ch_swpt,
			regfile_intf_wb_top,
			swptr_adr_reach);

reg_top  basic_reg_top (
                        l_adec_enable_ch_main_csr,
                        l_adec_enable_int_maska,
                        l_adec_enable_int_maskb,
                        l_adec_enable_int_srca,
                        l_adec_enable_int_srcb,
                        l_adec_enable_ch_csr,
                        l_adec_enable_ch_sz,
                        l_adec_enable_ch_a0,
                        l_adec_enable_ch_am0,
                        l_adec_enable_ch_a1,
                        l_adec_enable_ch_am1,
                        l_adec_enable_ch_desc,
                        l_adec_enable_ch_swpt,
                       	regfile_intf_wb_top);

mux_reg  mux_top       (
                        l_adec_enable_ch_main_csr,
                        l_adec_enable_int_maska,
                        l_adec_enable_int_maskb,
                        l_adec_enable_int_srca,
                        l_adec_enable_int_srcb,
                        l_adec_enable_ch_csr,
                        l_adec_enable_ch_sz,
                        l_adec_enable_ch_a0,
                        l_adec_enable_ch_am0,
                        l_adec_enable_ch_a1,
                        l_adec_enable_ch_am1,
                        l_adec_enable_ch_desc,
                        l_adec_enable_ch_swpt,
			regfile_intf_wb_top);







endmodule




