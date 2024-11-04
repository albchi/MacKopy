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
// Name of the module   : DMA priority encoder 
// Author               : Subha Amancherla 
// Project name         : Wishbone DMA/Bridge core
// Created on           : 09/23/2003
// Updated on           :
// Purpose of module    :
// Comments             :
// *************************************************

`include "inc_addr.v"

module mod_pri_enc (intf_wb_top.ch_sel intf_pri, 
		    input logic [7:0] fifo_prienc_full,
		    output logic prienc_priarb_start_arb, 
		    logic [5:0] prienc_fifo_data [7:0],
		    logic [7:0] prienc_fifo_wr);


parameter p_pri_enc_idle  = 3'b001;
parameter p_chk_ch_valid  = 3'b010;

logic [30:0] l_ch_valid;
logic [3:0] l_arr_ch_conf [30:0] ;
logic [3:0] l_prienc_state;
logic [5:0] l_ch_num;
logic l_dma_chsel_ack; 
//==============================================================================
// Cannot use generate statement here :<
always_comb l_arr_ch_conf = '{p_ch30_conf, p_ch29_conf, p_ch28_conf, p_ch27_conf, p_ch26_conf, 
			     p_ch25_conf, p_ch24_conf, p_ch23_conf, p_ch22_conf, p_ch21_conf,
			     p_ch20_conf, p_ch19_conf, p_ch18_conf, p_ch17_conf, p_ch16_conf,
			     p_ch15_conf, p_ch14_conf, p_ch13_conf, p_ch12_conf, p_ch11_conf,
			     p_ch10_conf, p_ch9_conf,  p_ch8_conf,  p_ch7_conf,  p_ch6_conf,
			     p_ch5_conf,  p_ch4_conf,  p_ch3_conf,  p_ch2_conf,  p_ch1_conf, p_ch0_conf};
//==============================================================================
// Generate for ack signal
genvar a;
generate for (a=0;a<31;a=a+1)
begin: gen_ack
assign intf_pri.o_ack[a] = intf_pri.dma_chsel_ack &  intf_pri.str_inst.regfile_chsel_ch_csr[a][5] & (intf_pri.chsel_dma_sel_val == a);
end
endgenerate


//==============================================================================
//Generate  for valid signal generation
genvar j;
generate for (j=0;j<31;j=j+1)
begin: gen_vld
always_comb begin
l_ch_valid[j] = l_arr_ch_conf[j][0] & intf_pri.str_inst.regfile_chsel_ch_csr[j][0] & 
		(intf_pri.str_inst.regfile_chsel_ch_csr[j][5] ? (intf_pri.i_dma_req[j] & !intf_pri.o_ack[j]) : 1'b1);

end
end
endgenerate // gen_vld


always @ (posedge intf_pri.i_clk or posedge intf_pri.i_reset)
begin
	if (intf_pri.i_reset == 'b1)
		l_dma_chsel_ack = 'b0;
	else if (intf_pri.dma_chsel_ack == 'b1)  
		l_dma_chsel_ack = 'b1;
	else if (l_prienc_state == p_pri_enc_idle) 
		l_dma_chsel_ack = 'b0;
end
 
//==============================================================================
// State machine

always @ (posedge intf_pri.i_clk or posedge intf_pri.i_reset)
begin
	if (intf_pri.i_reset == 'b1)
	begin
	   l_prienc_state <= p_pri_enc_idle; 
	   prienc_fifo_wr <= 8'b0; 
	end
	else
	begin
	case (l_prienc_state)
 	p_pri_enc_idle :
	begin	
	if (|l_ch_valid)
		begin
	   	l_prienc_state <= p_chk_ch_valid;
		end	 
      	   prienc_priarb_start_arb <= 'b0;
	   l_ch_num <= 'd0;
	   prienc_fifo_wr <= 8'b0; 
	end
	p_chk_ch_valid :
	begin
	// valid check & decide priority and write fifo
	prienc_fifo_wr <= 8'b0;
	if (l_ch_valid[l_ch_num] == 1'b1)
	begin

//fork_blk : fork 
fork 
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd0 && fifo_prienc_full['d0] == 'b0)
		begin
			prienc_fifo_wr['d0] <= 1'b1;
			prienc_fifo_data['d0] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else 
			prienc_fifo_wr['d0] <= 'b0;
		
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd1)
		begin
			prienc_fifo_wr[1] <= 1'b1;
			prienc_fifo_data[1] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else 
			prienc_fifo_wr[1] <= 'b0;
		
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd2)
		begin
			prienc_fifo_wr[2] <= 1'b1;
			prienc_fifo_data[2] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[2] <= 1'b0;
	
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd3)
		begin
			prienc_fifo_wr[3] <= 1'b1;
			prienc_fifo_data[3] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[3] <= 1'b0;

		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd4)
		begin
			prienc_fifo_wr[4] <= 1'b1;
			prienc_fifo_data[4] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[4] <= 1'b0;
		
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd5)
		begin
			prienc_fifo_wr[5] <= 1'b1;
			prienc_fifo_data[5] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[5] <= 1'b0;
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd6)
		begin
			prienc_fifo_wr[6] <= 1'b1;
			prienc_fifo_data[6] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[6] <= 1'b0;
	
		if (intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13] == 'd7)
		begin
			prienc_fifo_wr[7] <= 1'b1;
			prienc_fifo_data[7] <=  intf_pri.str_inst.regfile_chsel_ch_csr[l_ch_num][15:13];
		end
		else
			prienc_fifo_wr[7] <= 1'b0;
join //: fork_blk

	end // eof if (l_ch_num == 'd31)
  
	if (l_ch_num == 'd31)
	begin
	   if (l_dma_chsel_ack)
		begin
	   		l_prienc_state <= p_pri_enc_idle;
	   		l_ch_num  <= 'd0;
		end
	   prienc_priarb_start_arb <= 'b1;
	   prienc_fifo_wr <= 8'b0;
	end
 	else	
		l_ch_num++;
	end // p_chk_ch_valid
	endcase
	end // else reset
end // always blk

endmodule


// Pending thing
// 1	When fifo is full, the start arbiter should trigger and wait for fifo
// empty. : To be implemented *****
 
