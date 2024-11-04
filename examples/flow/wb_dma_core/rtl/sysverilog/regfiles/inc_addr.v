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
// Name of the module 	: u_adress.v
// Author 	  	: Bhavana Kshirsagar
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: adress definitions for each register file.
// Comments		:
// ********************************************************************************************


`define csr_addr 	32'h00000000
`define intr_mask_a 	32'h00000004
`define intr_mask_b 	32'h00000008
`define intr_src_a 	32'h0000000c
`define intr_src_b 	32'h00000010

// Added by subha for DMA engine
`define USE_ED 	 	'd7
`define EOL		'd20
`define ARS		'd3
`define SRC_SEL		'd2
`define DEST_SEL	'd1
`define INC_SRC		'd4
`define INC_DST		'd3
`define SWPTR_EN	'd31

