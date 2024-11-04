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
// Name of the module 	: u_mux.v
// Author 	  	: Bhavana Kshiresagar
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: reads the selected channel register 
// Comments		:
// ********************************************************************************************

module mux_reg (input   l_adec_enable_ch_main_csr,
                        l_adec_enable_int_maska,l_adec_enable_int_maskb,
                        l_adec_enable_int_srca,l_adec_enable_int_srcb,
		logic [31:0] l_adec_enable_ch_csr,l_adec_enable_ch_sz,
                        l_adec_enable_ch_a0,l_adec_enable_ch_am0,
                        l_adec_enable_ch_a1,l_adec_enable_ch_am1,
                        l_adec_enable_ch_desc,l_adec_enable_ch_swpt,
		        intf_wb_top.regfile mux_top_intf);
/*
always_ff @(posedge mux_top_intf.i_clk)
begin

if(muxintf.l_adec_enable_ch_main_csr && mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_main_csr;

 if(muxintf.l_adec_enable_int_maska &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_maska;


 if (muxintf.l_adec_enable_int_maskb &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_maska;


 if (muxintf.l_adec_enable_int_srca &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_srca;

 if (muxintf.l_adec_enable_int_srcb &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_srcb;

end

genvar i;
generate for(i=0;i<=30;i=i+1)
begin:csr
always_ff @(posedge mux_top_intf.i_clk && !mux_top_intf.i_reset)
begin
if (muxintf.l_adec_enable_ch_csr[i] && mux_top_intf.i_rd)
begin
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_csr[i];
end
end
end
endgenerate

generate for(i=0;i<=30;i=i+1)
begin:sz
always_ff @(posedge mux_top_intf.i_clk && !mux_top_intf.i_reset)
begin
if (muxintf.l_adec_enable_ch_sz[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_sz[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:a0
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_a0[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <= mux_top_intf.str_inst.regfile_chsel_ch_a0[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:am0
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_am0[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_am0[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:a1
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_a1[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_a1[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:am1
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_am1[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_am1[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:desc
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_desc[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_desc[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:swpt
always_ff @(posedge mux_top_intf.i_clk)
begin
if (muxintf.l_adec_enable_ch_swpt[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_swpt[i];
end
end
endgenerate

*/


always_latch
begin

if(l_adec_enable_ch_main_csr && mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_main_csr;

 if(l_adec_enable_int_maska &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_maska;


 if (l_adec_enable_int_maskb &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_maska;


 if (l_adec_enable_int_srca &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_srca;

 if (l_adec_enable_int_srcb &&  mux_top_intf.i_rd)
mux_top_intf.regfile_wbif_data <= mux_top_intf.regfile_chsel_int_srcb;

end

genvar i;
generate for(i=0;i<=30;i=i+1)
begin:csr
always_latch
begin
if (l_adec_enable_ch_csr[i] && mux_top_intf.i_rd)
begin
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_csr[i];
end
end
end
endgenerate

generate for(i=0;i<=30;i=i+1)
begin:sz
always_latch
begin
if (l_adec_enable_ch_sz[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_sz[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:a0
always_latch
begin
if (l_adec_enable_ch_a0[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <= mux_top_intf.str_inst.regfile_chsel_ch_a0[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:am0
always_latch
begin
if (l_adec_enable_ch_am0[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_am0[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:a1
always_latch
begin
if (l_adec_enable_ch_a1[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_a1[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:am1
always_latch
begin
if (l_adec_enable_ch_am1[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_am1[i];
end
end
endgenerate

generate for (i=0;i<=30;i=i+1)
begin:desc
always_latch
begin
if (l_adec_enable_ch_desc[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_desc[i];
end
end
endgenerate


generate for (i=0;i<=30;i=i+1)
begin:swpt
always_latch
begin
if (l_adec_enable_ch_swpt[i] && mux_top_intf.i_rd)
	mux_top_intf.regfile_wbif_data <=mux_top_intf.str_inst.regfile_chsel_ch_swpt[i];
end
end
endgenerate

endmodule
