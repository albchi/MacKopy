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
// Name of the module 	: Interface Wishbone Top (intf_wb_top)
// Author 	  	: Subha Amancherla
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 29th August' 2003
// Updated on 		: 
// Purpose of module	: Interface module for all the modules in wishbone
// Comments		:
// ********************************************************************************************

`include "inc_addr.v"

typedef logic  [31:0] logic32;
typedef logic  [4:0]  logic5;
typedef logic  [3:0]  logic4;

// ********************** Structure Declaration ***********************************
// Structure instanciated to use in regfiles
// Grouping of all channel register has t be achieved using this struct
typedef struct {
        logic[31:0]  regfile_chsel_ch_csr[31:0],
                     regfile_chsel_ch_am0[31:0],
                     regfile_chsel_ch_sz[31:0],
                     regfile_chsel_ch_am1[31:0],
                     regfile_chsel_ch_a0[31:0],
                     regfile_chsel_ch_a1[31:0],
                     regfile_chsel_ch_desc[31:0],
                     regfile_chsel_ch_swpt[31:0];
                }reg_str;

// **********************  Interface intf_wb_top ******************************************
interface intf_wb_top (
input	 bit             i_clk, i_reset,
                         i_mast0_ack, i_mast1_ack,
                         i_mast0_err, i_mast1_err,
                         i_mast0_retry, i_mast1_retry,
                         i_slv0_strb, i_slv1_strb,
                         i_slv0_cyc,i_slv1_cyc,
         logic           i_slv0_we,i_slv1_we,
 	 logic4          i_slv0_byte_sel, i_slv1_byte_sel,
	 logic32         i_mast0_data, i_slv0_data, i_slv0_addr,
                         i_mast1_data, i_slv1_data, i_slv1_addr,
                         i_dma_nd, i_dma_req,i_dma_rest,

output	 bit             o_mast0_cyc, o_mast0_we, 
                         o_mast1_cyc, o_mast1_we, 
                         o_inta, o_intb, o_mast0_strb, o_mast1_strb,
                         o_slv0_ack, o_slv1_ack, o_slv0_err,o_slv1_err,
                         o_slv0_retry, o_slv1_retry,
	logic32          o_mast0_data, o_mast0_addr, o_slv0_data,
                         o_mast1_data, o_mast1_addr,o_slv1_data,
	logic4           o_mast0_byte_sel,o_mast1_byte_sel,
	logic32          o_ack
	);

// ********************** Declarations ******************************************
	//struct instance
	reg_str str_inst;
        
	logic32          i_wr_addr, i_wr_data, o_rd_data;
        bit              regifle_wbif_ack,i_wr,i_rd;

	// dma regfile signals
	bit     	dma_regfile_wrnrd,dma_paused,dma_regfile_err,
			dma_regfile_busy,dma_reg_txsz_we,
			dma_regfile_done,dma_regfile_done_all,dma_regfile_ptr_sel,
			dma_reg_adr0_we, dma_reg_adr1_we,dma_reg_csr_we;

	logic32         dma_regfile_wr_data, dma_regfile_adr0, dma_regfile_adr1, dma_regfile_csr, dma_regfile_txsz; 

	bit	        regfile_dma_intr,regfile_dma_pause,regfile_dma_stop;

	logic32         regfile_dma_rd_data;

	logic32  	regfile_chsel_main_csr , regfile_chsel_int_maska ,
	 		regfile_chsel_int_maskb, regfile_chsel_int_srca, regfile_chsel_int_srcb;


	// regfile ch_sel signals
	bit 		chsel_regfile_ndndr,i_dma_fetch_descr, dma_regfile_ndnr ;
	
	// dma chsel signals
	logic32         chsel_dma_csr, chsel_dma_sz, chsel_dma_a0, chsel_dma_am0,
      			chsel_dma_a1, chsel_dma_am1, chsel_dma_desc, chsel_dma_swpt;

        logic5		chsel_dma_sel_val;
 	bit             chsel_dma_start, dma_chsel_busy, dma_chsel_next_ch, dma_chsel_nd, dma_chsel_ack;

	// dma wbif signals
	bit		dma_wbif_mast0_start, dma_wbif_mast0_wait, dma_wbif_mast0_wrnrd,
             		dma_wbif_mast1_start, dma_wbif_mast1_wait, dma_wbif_mast1_wrnrd;
                		
	logic32         dma_wbif_mast0_addr, dma_wbif_mast0_odata, dma_wbif_mast1_odata, dma_wbif_mast1_addr;

	logic32 	wbif_regfile_addr,wbif_regfile_data,regfile_wbif_data,wbif_dma_mast0_idata, wbif_dma_mast1_idata;

	bit		wbif_regfile_wrnrd,wbif_regfile_ack,
			wbif_dma_mast0_drdy, wbif_dma_mast1_drdy, wbif_dma_mast0_err,wbif_dma_mast1_err;


// **********************  modport Declarations *************************************

// ======================  Channel select Declarations ===============================
modport	ch_sel 
	(
	input 	i_clk, i_reset, dma_chsel_next_ch, i_dma_req, i_dma_nd, dma_chsel_busy,	
	        regfile_chsel_main_csr, regfile_chsel_int_maska, regfile_chsel_int_maskb, 
		regfile_chsel_int_srca, regfile_chsel_int_srcb,str_inst,dma_chsel_ack,
		
	output	chsel_dma_csr, chsel_dma_sz,chsel_dma_a0, chsel_dma_am0, chsel_dma_a1, chsel_dma_am1,
                chsel_dma_desc, chsel_dma_swpt, chsel_dma_sel_val, chsel_dma_start,o_ack
	);


// ======================  DMA engine Declarations =====================================
modport dma_eng 
	(
	input 	i_clk, i_reset, i_dma_req, i_dma_nd, i_dma_rest,
		regfile_dma_intr, regfile_dma_pause, regfile_dma_stop, regfile_dma_rd_data,
		chsel_dma_csr, chsel_dma_sz, chsel_dma_a0, chsel_dma_am0, chsel_dma_a1, chsel_dma_am1,
                chsel_dma_desc, chsel_dma_swpt, chsel_dma_sel_val, chsel_dma_start,wbif_dma_mast0_err,wbif_dma_mast1_err,
		wbif_dma_mast0_drdy, wbif_dma_mast1_drdy,wbif_dma_mast0_idata, wbif_dma_mast1_idata,

 	output	dma_chsel_ack,dma_chsel_next_ch,dma_regfile_err, dma_regfile_adr0, dma_regfile_adr1, dma_regfile_wr_data, dma_paused, dma_regfile_done, 
		dma_regfile_done_all,dma_wbif_mast0_addr, dma_regfile_csr, dma_regfile_txsz, dma_regfile_busy, 
		dma_wbif_mast0_start, dma_wbif_mast0_wait, dma_wbif_mast0_wrnrd, dma_wbif_mast0_odata,
		dma_wbif_mast1_start, dma_wbif_mast1_wait, dma_wbif_mast1_wrnrd, dma_wbif_mast1_odata,
		dma_wbif_mast1_addr
	);

// ======================  WB Interface Declarations =====================================
modport wb_if
	(
	input	i_clk, i_reset,chsel_dma_sel_val,
                dma_wbif_mast0_start, dma_wbif_mast0_wait, dma_wbif_mast0_wrnrd, dma_wbif_mast0_odata, dma_wbif_mast0_addr,
		dma_wbif_mast1_start, dma_wbif_mast1_wait, dma_wbif_mast1_wrnrd, dma_wbif_mast1_odata, dma_wbif_mast1_addr,
		i_slv1_strb,i_slv0_strb,i_slv0_byte_sel, i_slv1_byte_sel,
		i_mast1_err,i_mast0_err,i_slv0_cyc,i_slv1_cyc,i_mast0_ack,i_mast1_ack,
                i_mast1_data, i_slv1_data, i_slv1_addr,i_slv0_we,i_slv1_we,
       		i_mast0_data, i_slv0_data, i_slv0_addr,i_mast0_retry, i_mast1_retry,regfile_wbif_data,regifle_wbif_ack,

	output  o_mast0_cyc, o_mast0_we, o_mast0_strb,o_mast1_strb,
                o_slv0_err,o_slv1_err,o_slv0_retry, o_slv1_retry,o_slv0_ack, o_slv1_ack, // Added ack Subha
                o_mast0_data, o_mast0_addr, o_slv0_data,o_mast0_byte_sel,o_mast1_byte_sel,
            	wbif_dma_mast1_drdy,wbif_dma_mast0_drdy,    
		o_mast1_cyc, o_mast1_we,  
                o_mast1_data, o_mast1_addr, o_slv1_data,wbif_dma_mast0_err,wbif_dma_mast1_err,
		wbif_regfile_addr,wbif_regfile_data,wbif_regfile_wrnrd,i_wr_addr,i_rd,i_wr,i_wr_data,wbif_dma_mast0_idata,wbif_dma_mast1_idata,wbif_regfile_ack
	);


// ======================  Regfile Declarations =====================================
modport regfile 
	(
	input 	i_clk, i_reset,i_wr,i_rd, i_wr_addr, i_wr_data,dma_regfile_busy,dma_regfile_ndnr,dma_regfile_err,
		dma_regfile_done,dma_regfile_done_all,i_dma_fetch_descr,dma_regfile_csr,dma_regfile_ptr_sel,
		dma_reg_txsz_we, dma_reg_adr0_we, dma_reg_adr1_we, chsel_dma_sel_val,wbif_regfile_ack,
		
	output 	o_inta, o_intb,regfile_dma_pause, regfile_dma_stop, regfile_dma_rd_data,regfile_wbif_data,
	        regfile_chsel_main_csr, regfile_chsel_int_maska, regfile_chsel_int_maskb, 
		regfile_chsel_int_srca, regfile_chsel_int_srcb, str_inst
	);

endinterface // intf_wb_top
