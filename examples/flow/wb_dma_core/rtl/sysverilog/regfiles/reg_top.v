/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

//*****************************************************************************************
// Name of the module 	: u_reg_instances.v
// Author 	  	: Subhasree Amancherla 
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: instances of main csr,intr and all channel registers.
// Comments		:
// ********************************************************************************************


module reg_top (input   l_adec_enable_ch_main_csr,
		        l_adec_enable_int_maska,l_adec_enable_int_maskb,
   			l_adec_enable_int_srca,l_adec_enable_int_srcb,
         logic[31:0]		l_adec_enable_ch_csr,l_adec_enable_ch_sz,
        		l_adec_enable_ch_a0,l_adec_enable_ch_am0,
        		l_adec_enable_ch_a1,l_adec_enable_ch_am1,
        		l_adec_enable_ch_desc,l_adec_enable_ch_swpt,
			intf_wb_top.regfile rinstitf);


//instance of main csr,srcand mask interruput registers
basic_reg #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'h7fffffff),
		.p_read_clear(32'h00000000)) 
	ch_csr(	.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_main_csr),
		.o_breg_reg(rinstitf.regfile_chsel_main_csr));

basic_reg  #(	.p_reset_reg(32'hffffffff),
		.p_read(32'hffffffff),
		.p_write(32'h7fffffff),
		.p_read_clear(32'hffffffff)) 
	ch_int_maska(	
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_int_maska),
		.o_breg_reg(rinstitf.regfile_chsel_int_maska));
 
basic_reg  #(	.p_reset_reg(32'hffffffff),
		.p_read(32'hffffffff),
		.p_write(32'h7fffffff),
		.p_read_clear(32'hffffffff)) 
	ch_int_maskb (	
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_int_maskb),
		.o_breg_reg(rinstitf.regfile_chsel_int_maskb));

basic_reg  #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'h7fffffff),
		.p_read_clear(32'h00000000), 
		.p_int_src(1'b1)) 
	ch_intr_srca (
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_int_srca),
		.o_breg_reg(rinstitf.regfile_chsel_int_srca));


basic_reg  #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'h7fffffff),
		.p_read_clear(32'h00000000),
		.p_int_src(1'b1)) 
	ch_intr_srcb (
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_int_srcb),
		.o_breg_reg(rinstitf.regfile_chsel_int_srcb));


// instances of csr register

genvar b;
generate for (b=0;b<=30;b++)
begin:ch_csr_gen
basic_reg #(	.p_reset_reg(32'h00000000),
		.p_read(32'hfffffdff),
		.p_write(32'h007fe3ff),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b1),
		.p_ch_num(b)) 
	ch_csr_inst (
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_csr[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_csr[b]));
end
endgenerate

// instances of size register

generate for (b=0;b<=30;b++)
begin:sz_csr
basic_reg #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'h01ff0fff),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_sz(
		.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_sz[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_sz[b]));
end
endgenerate


//instances of a0 adress reg 

generate for (b=0;b<=30;b++)
begin:a0_csr
basic_reg #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'hfffffffc),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),.p_ch_num(b)) 
	ch_a0(	.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_a0[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_a0[b]));
end
endgenerate


//instances of a1 adress reg  

generate for (b=0;b<=30;b++)
begin:a1_csr
basic_reg #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'hfffffffc),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_a1(	.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_a1[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_a1[b]));
end
endgenerate


//instances of a0 adress mask

generate for (b=0;b<=30;b++)
begin:a0m_csr
basic_reg  #(	.p_reset_reg(32'hfffffffc),
		.p_read(32'hffffffff),
		.p_write(32'hfffffff0),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_am0(	.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_am0[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_am0[b]));
end
endgenerate

//instaces of a1 adress mask


generate for (b=0;b<=30;b++)
begin:a1m_csr
basic_reg  #(	.p_reset_reg(32'hfffffffc),
		.p_read(32'hffffffff),
		.p_write(32'hfffffff0),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_am1(	.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_am1[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_am1[b]));
end
endgenerate


//instaces of desc register

generate for (b=0;b<=30;b++)
begin:desc_csr
basic_reg  #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'hfffffffc),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_desc(.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_desc[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_desc[b]));
end
endgenerate

//instaces of  mask register

generate for (b=0;b<=30;b++)
begin:swpt_csr
basic_reg  #(	.p_reset_reg(32'h00000000),
		.p_read(32'hffffffff),
		.p_write(32'hfffffffc),
		.p_read_clear(32'hffffffff),
		.p_ch_csr(1'b0),
		.p_ch_num(b)) 
	ch_swpt(.rintf(rinstitf),
		.i_breg_enable(l_adec_enable_ch_swpt[b]),
		.o_breg_reg(rinstitf.str_inst.regfile_chsel_ch_swpt[b]));
end
endgenerate


endmodule
