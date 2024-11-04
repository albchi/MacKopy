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
// Name of the module 	: u_adress_decoder.v
// Author 	  	: Bhavana Kshirsagar
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: adress decoder decodes adress of all the registers.
// Comments		:
// ********************************************************************************************


`include "./inc_addr.v"

// ** new**  module addr_dec(adr_mux_itf.add_dec adeco,intf_wb_top.regfile decintf,input swptr_adr_reach);
module addr_dec( output bit l_adec_enable_ch_main_csr,
		        l_adec_enable_int_maska,
         		l_adec_enable_int_maskb,
         		l_adec_enable_int_srca,
         		l_adec_enable_int_srcb,
         	logic [31:0] 	l_adec_enable_ch_csr,
        	 	l_adec_enable_ch_sz,
         		l_adec_enable_ch_a0,
        		l_adec_enable_ch_am0,
         		l_adec_enable_ch_a1,
         		l_adec_enable_ch_am1,
         		l_adec_enable_ch_desc,
         		l_adec_enable_ch_swpt,
			intf_wb_top.regfile decintf,
		input 	swptr_adr_reach);

logic [31:0] ch_csr_addr[31:0];
logic [31:0] ch_sz_addr[31:0];
logic [31:0] ch_a0_addr[31:0];
logic [31:0] ch_am0_addr[31:0];
logic [31:0] ch_a1_addr[31:0];
logic [31:0] ch_am1_addr[31:0];
logic [31:0] ch_desc_addr[31:0];
logic [31:0] ch_swpt_addr[31:0];


//TEST FOR INTA_O
logic [2:0]  ch_csr_r3[31:0];
logic [2:0]  int_src_r[31:0];
logic [31:0] int_srca;
logic [31:0] ch_int;

// starting adress of each register

logic [31:0]count 	=32'h20;
logic [31:0]szcount 	=32'h24;
logic [31:0]a0count 	=32'h28;
logic [31:0]am0count 	=32'h2c;
logic [31:0]a1count 	=32'h30;
logic [31:0]am1count 	=32'h34;
logic [31:0]desccount 	=32'h38;
logic [31:0]swptcount 	=32'h3c;
logic [31:0]aout	=32'h00000000;
//logic [31:0]aout	=32'hb0000000;


always_ff @ (posedge decintf.i_clk)
begin
        l_adec_enable_ch_main_csr	<=  (((decintf.i_wr_addr==(`csr_addr)) || swptr_adr_reach)  && !decintf.i_reset) ?1:0;
        l_adec_enable_int_maska   <=  ((decintf.i_wr_addr==(`intr_mask_a)) && !decintf.i_reset) ? 1:0;
	l_adec_enable_int_maskb	<=  ((decintf.i_wr_addr==(`intr_mask_b)) && !decintf.i_reset) ? 1:0;
        l_adec_enable_int_srca	<=  ((decintf.i_wr_addr==(`intr_src_a))  && !decintf.i_reset) ? 1:0;
	l_adec_enable_int_srcb	<=  ((decintf.i_wr_addr==(`intr_src_b))  && !decintf.i_reset) ? 1:0;


/*	if(l_adec_enable_int_maska)
	begin
		decintf.regfile_chsel_int_maska = decintf.i_wr_data;
	end*/
end


genvar i;

//generating enable signal for csr registers
generate for (i=0;i<=30;i=i+1)
begin:csr
always_ff @ (posedge decintf.i_clk or posedge decintf.i_reset)
begin
/*
l_adec_enable_ch_csr[i] <= ( ((decintf.i_wr_addr==(aout+(count+(i*32)))  || swptr_adr_reach)) && !decintf.i_reset) ?1:0;
*/
	        // Logic added fro inta_o INTERRUPT GENERATION  ch_csr_r3  for each channel given to wb_rf_din[19:17]
//		if(l_adec_enable_ch_csr[i]) 
		begin
	        	ch_csr_r3 [i]<= decintf.i_wr_data[19:17];
      			int_src_r [i] <= decintf.i_wr_data[22:20];
      			ch_int[i]    <= |(int_src_r[i] & ch_csr_r3[i]);
		end
end
end
endgenerate


generate for (i=0;i<=31;i=i+1)
begin:srca
always_ff @ (posedge decintf.i_clk or posedge decintf.i_reset)/* 
		int_srca[i]  = (decintf.i_reset) ? 'b0 : (decintf.regfile_chsel_int_maska[i] & decintf.regfile_chsel_int_srca[i]);
*/
	int_srca[i] = (decintf.chsel_dma_sel_val == i & decintf.dma_regfile_done == 1'b1) ? 1'b1 : 1'b0;

end
endgenerate

always_comb
begin
  decintf.o_inta = int_srca[0] | int_srca[1]| int_srca[2] | int_srca[3] | int_srca[4] | int_srca[5] | int_srca[6] | 
		   int_srca[7] | int_srca[8] | int_srca[9] |int_srca[10] | int_srca[11] | int_srca[12] | int_srca[13] | 
		   int_srca[14] | int_srca[15] | int_srca[16] | int_srca[17] | int_srca[18] | int_srca[19]|int_srca[20] | 
		   int_srca[21] | int_srca[22] | int_srca[23] | int_srca[24] | int_srca[25] | int_srca[26] | int_srca[27] | 
		   int_srca[28] | int_srca[29] |int_srca[30] |int_srca[31] ;
end

//generating enable signal for size registers
generate for (i=0;i<=30;i=i+1)
begin:sz
always_ff @ (posedge decintf.i_clk)
	begin
	l_adec_enable_ch_sz[i] <=((decintf.i_wr_addr==(aout+(szcount+(i*32)))) && !decintf.i_reset) ?1:0;
	end
end
endgenerate


//generating enable  signal for a0 address registers
generate for (i=0;i<=30;i=i+1)
begin:a0
always_ff @ (posedge decintf.i_clk)
begin
l_adec_enable_ch_a0[i] <=((decintf.i_wr_addr==(aout+(a0count+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

//generating enable signal  for a0m address registers
generate for (i=0;i<=30;i=i+1)
begin:am0
always_ff@ (posedge decintf.i_clk)
begin
l_adec_enable_ch_am0[i] <=((decintf.i_wr_addr==(aout+(am0count+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

//generating enable signal for a1 address registers
generate for (i=0;i<=30;i=i+1)
begin:a1
always_ff @ (posedge decintf.i_clk)
begin
l_adec_enable_ch_a1[i] <=((decintf.i_wr_addr==(aout+(a1count+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

//generating enable signal  for a1m address registers
generate for (i=0;i<=30;i=i+1)
begin:am1
always_ff @ (posedge decintf.i_clk)
begin
l_adec_enable_ch_am1[i] <=((decintf.i_wr_addr==(aout+(am1count+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

//generating enable signal  for desc registers
generate for (i=0;i<=30;i=i+1)
begin:desc
always_ff @ (posedge decintf.i_clk)
begin
l_adec_enable_ch_desc[i] <=((decintf.i_wr_addr==(aout+(desccount+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

//generating enable signal  for swptr registers
generate for (i=0;i<=30;i=i+1)
begin:swpt
always_ff @ (posedge decintf.i_clk)
begin
l_adec_enable_ch_swpt[i] <=((decintf.i_wr_addr==(aout+(swptcount+(i*32)))) && !decintf.i_reset) ?1:0;
end
end
endgenerate

endmodule
