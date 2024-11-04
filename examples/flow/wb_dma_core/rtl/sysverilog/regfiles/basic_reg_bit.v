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
// Name of the module 	: basic register file
// Author 	  	: Bhavana kshirsagar
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 
// Updated on 		: 
// Purpose of module	: registerfile working model.
// Comments		:
// ********************************************************************************************


module basic_reg_bit(intf_wb_top.regfile rintf,input i_breg_enable,output o_breg_reg);

bit i_breg_enable;
logic  o_breg_reg;
logic  l_basic_reg;
logic [31:0] l_data;
logic l_wr;
logic l_rd;
logic l_set_dma_regfile_done;

parameter  p_reset_reg  =  32'h00000000;
parameter  p_read  	=  32'hffffffff;
parameter  p_write 	=  32'hffffffff;
parameter  p_read_clear =  32'hffffffff;
parameter  have_cbuf 	=  1'b1;    
parameter  p_ch_csr	=  1'b0; 	// To signify the csr reg
parameter  p_ch_num     =  5'b00000; 	// To signify the ch num assigned to reg 
parameter  p_int_src    =  1'b0; 	// To signify the Interrupt src reg

assign o_breg_reg = (l_rd) ? l_basic_reg & p_read[0] & p_read_clear[0] : l_basic_reg & p_read[0] ;

always @ (posedge rintf.i_clk)
begin
	l_data <= rintf.i_wr_data;
	l_wr   <= rintf.i_wr;
	l_rd   <= (i_breg_enable & rintf.i_rd);
end

always_ff @(posedge rintf.i_clk or posedge rintf.i_reset) 
	l_set_dma_regfile_done <=  (rintf.i_reset) ? 'b0 : rintf.dma_regfile_done;


always @(posedge rintf.i_clk or posedge rintf.i_reset) 
begin
	if (rintf.i_reset)
	begin
		l_basic_reg <= p_reset_reg[0];
	end
	else
	if (i_breg_enable && l_wr)
	begin
		l_basic_reg <= l_data[0] & p_write[0];

	end

	if (i_breg_enable && l_rd)
	begin
		l_basic_reg <= l_basic_reg & p_read[0] & p_read_clear[0];
	end
/*
	if (p_ch_csr ) // && (p_ch_num == rintf.chsel_dma_sel_val)) // Subha added logic
	begin
		l_basic_reg[10] <= ((p_ch_num == rintf.chsel_dma_sel_val) & rintf.dma_regfile_busy) ? 1'b1 : 1'b0; 
	end	
	if (p_ch_csr && (p_ch_num == rintf.chsel_dma_sel_val) && rintf.dma_regfile_done && l_basic_reg[6] == 'b0)
	begin  // Will be set only when ARS bit is cleared
		l_basic_reg[11] <=  1'b1;
//		$display ("Setting ch_done of channel %d ",p_ch_num); 
	end

	if (p_ch_csr && (p_ch_num == rintf.chsel_dma_sel_val) && rintf.dma_regfile_err)
	begin
		l_basic_reg <= l_basic_reg | 32'h00001000;
		//$display ("Setting ch_err of channel %d ",p_ch_num); 
	end

	if (p_ch_csr && (p_ch_num == rintf.chsel_dma_sel_val) && rintf.dma_regfile_done && (l_basic_reg[18] == 'b1))
	begin //INT_CH_DONE is set
		l_basic_reg[21] <= 1'b1; 
		//$display ("Setting int_ch_done of channel %d ",p_ch_num); 
	end

	if (p_ch_csr && (p_ch_num == rintf.chsel_dma_sel_val) && rintf.dma_regfile_err && (l_basic_reg[17] == 'b1))
	begin //INT_CH_ERR is set
		l_basic_reg <= l_basic_reg | 32'h00100000;
		//$display ("Setting int_ch_err of channel %d ",p_ch_num); 
	end

	if (p_ch_csr && (p_ch_num == rintf.chsel_dma_sel_val) && rintf.dma_regfile_done) // && (l_basic_reg[19] == 'b1))
	begin //INT_CH_CHK_SZ is set
		l_basic_reg[22] <= 1'b1; 
	//	$display ("Setting int_ch_chk_sz of channel %d ",p_ch_num); 
	end

	if (p_int_src & (l_set_dma_regfile_done == 'b0 & rintf.dma_regfile_done == 'b1))
	begin 
		l_basic_reg[rintf.chsel_dma_sel_val] <= 'b1;
	//	$display ("Setting Int of channel %d ",p_ch_num); 
	end
	else if (p_int_src & (l_set_dma_regfile_done == 'b1 & l_rd == 'b1))
		l_basic_reg[rintf.chsel_dma_sel_val] <= 'b0;

	if (p_ch_csr & rintf.dma_regfile_done)
	begin 
		l_basic_reg[0] <= 1'b0; 
	//	$display ("Re-Setting ch_en"); 
	end
*/
end

endmodule
    
