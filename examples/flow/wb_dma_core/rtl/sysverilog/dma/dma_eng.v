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
// Name of the module 	: Dma Engine (dma_eng.v)
// Author 	  	: Subha Amancherla
// Project name 	: Wishbone DMA/Bridge core
// Created on		: 1st, sept  2003
// Updated on 		: 
// Purpose of module	: Functionality of DMA engine is incorporated in here
// Comments		:
// ********************************************************************************************


`include "inc_addr.v"

module mod_dma_eng (intf_wb_top.dma_eng intf_dma_eng);
 
   enum bit [3:0] { p_dma_idle = 0, p_dma_pause, p_dma_update, p_dma_read, p_dma_write, p_dma_ld_desc_csr, p_dma_ld_src_addr, 
	 	p_dma_ld_dest_addr, p_dma_ld_next_desc, p_dma_wr_csr_done} e_state;

	reg [10:0] 		l_dma_nstate;  	 	// next state
	reg [10:0] 		l_dma_pstate;   	// present state
	bit 			b_chunk_done; 
	bit 			b_ld_desc;

	logic [31:0] 		l_desc_data;
	bit 			b_read;
	bit 			b_read_r;
	bit 			b_write;
	bit 			b_write_r;
	bit 			b_m0_we;
	bit 			b_m1_we;
	logic [11:0]		l_tsz_cnt;
	bit 			b_m0_go;
	logic [1:0]		l_desc_cnt;
	wire			b_incr_src_addr   = intf_dma_eng.chsel_dma_csr[`INC_SRC];
	wire			b_incr_dest_addr  = intf_dma_eng.chsel_dma_csr[`INC_DST];
	
	logic [29:0]		l_adr0_cnt, l_adr1_cnt;
	logic [29:0]		l_adr0_cnt_next, l_adr1_cnt_next;
	logic [29:0]		l_adr0_cnt_next1, l_adr1_cnt_next1;
	bit			b_adr0_inc, b_adr1_inc;

	logic [8:0]		b_chunk_cnt;
	bit			b_chunk_dec;

	logic [31:0]		mast0_adr, mast1_adr;

	bit			b_tsz_dec;

	bit			de_txsz_we;
	bit			de_csr_we;
	bit			de_adr0_we;
	bit			de_adr1_we;
	bit			ld_desc_sel;
	
	logic			l_chunk_cnt_is_0_d;
	bit			b_chunk_cnt_is_0_r;
	logic			l_tsz_cnt_is_0_d;
	bit			b_tsz_cnt_is_0_r;

	bit			b_rd_ack, b_wr_ack;
	bit			b_rd_ack_r;

	logic			l_chunk_0;
	logic			l_done;
	logic			l_dma_done_d;
	logic			l_dma_done_r;
	logic			l_dma_abort_r;
	logic			l_next_ch;
	logic			l_read_hold, l_write_hold;
	logic			l_write_hold_r;

	logic			l_ptr_set;

	logic			l_mast0_drdy_r;
	logic			l_paused;





// ====================================================================
// Misc Logic

always_ff @(posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
	l_dma_done_r <=  (intf_dma_eng.i_reset == 1'b1) ? 'b0 : intf_dma_eng.dma_regfile_done;

// Address Counter 0 (Source Address)
always @(posedge intf_dma_eng.i_clk )
	begin
		if(intf_dma_eng.chsel_dma_start || l_ptr_set)	
			l_adr0_cnt <=  intf_dma_eng.chsel_dma_a0[31:2];
		else
		if(b_adr0_inc & b_incr_src_addr)	
			l_adr0_cnt <=  l_adr0_cnt_next;
	end

// ====================================================================
// 30 Bit Incrementor 
wb_dma_inc30r u0(.clk(intf_dma_eng.i_clk),
		 .in (l_adr0_cnt	),
		 .out(l_adr0_cnt_next1 	)
		);


always_comb l_adr0_cnt_next[1:0] = l_adr0_cnt_next1[1:0];

// For counter 
genvar cnt;
generate for (cnt= 2; cnt< 30; cnt++)
begin :counter0
always_comb l_adr0_cnt_next[cnt] = intf_dma_eng.chsel_dma_am0[cnt] ? l_adr0_cnt_next1[cnt] : l_adr0_cnt[cnt];
end //  counter0
endgenerate

// Address Counter 1 (Destination Address)
always @(posedge intf_dma_eng.i_clk )
	begin
	if(intf_dma_eng.chsel_dma_start | l_ptr_set)		l_adr1_cnt <=  intf_dma_eng.chsel_dma_a1[31:2];
	else
	if(b_adr1_inc & b_incr_dest_addr)	l_adr1_cnt <=  l_adr1_cnt_next;
end

// 30 Bit Incrementor 
wb_dma_inc30r u1(.clk(intf_dma_eng.i_clk),
 		 .in(l_adr1_cnt		),
		 .out(l_adr1_cnt_next1 	)
		);


always_comb l_adr1_cnt_next[1:0] = l_adr1_cnt_next1[1:0];

// For counter 
generate for (cnt= 2; cnt< 30; cnt++)
begin :counter1
always_comb l_adr1_cnt_next[cnt] = intf_dma_eng.chsel_dma_am1[cnt] ? l_adr1_cnt_next1[cnt] : l_adr1_cnt[cnt];
end //  counter1
endgenerate

// ====================================================================
// Chunk Counter
always @(posedge intf_dma_eng.i_clk )
	if(intf_dma_eng.chsel_dma_start) b_chunk_cnt <=  intf_dma_eng.chsel_dma_sz[24:16];
	else
	if(b_chunk_dec & !b_chunk_cnt_is_0_r)	b_chunk_cnt <=  b_chunk_cnt - 9'h1;

always_comb 
	l_chunk_cnt_is_0_d = (b_chunk_cnt == 9'h0);

always @(posedge intf_dma_eng.i_clk)
	b_chunk_cnt_is_0_r <=  l_chunk_cnt_is_0_d;

// Total Size Counter
always @(posedge intf_dma_eng.i_clk )
	if(intf_dma_eng.chsel_dma_start | l_ptr_set)  l_tsz_cnt <=  intf_dma_eng.chsel_dma_sz[11:0];
	else
	if(b_tsz_dec & ! b_tsz_cnt_is_0_r)	l_tsz_cnt <=  l_tsz_cnt - 12'h1;

always_comb 
	l_tsz_cnt_is_0_d = (l_tsz_cnt == 12'h0) & !intf_dma_eng.chsel_dma_sz[15];

always_comb
	b_tsz_cnt_is_0_r =  l_tsz_cnt_is_0_d;


// Counter Control Logic
always_comb
	b_chunk_dec =  b_read & !b_read_r;

always_comb
	b_tsz_dec =  b_read & !b_read_r;

always_comb
	b_adr0_inc = b_rd_ack & b_read_r;


// ====================================================================
// regfile ch_sel signals
always_comb 
	b_adr1_inc = b_wr_ack & b_write_r;

// Done logic
always @ (posedge intf_dma_eng.i_clk ) 
	l_chunk_0 <=  (intf_dma_eng.chsel_dma_sz[24:16] == 9'h0);

always_comb l_done 				= l_chunk_0 ? l_tsz_cnt_is_0_d : (l_tsz_cnt_is_0_d | l_chunk_cnt_is_0_d);
always_comb intf_dma_eng.dma_regfile_done 	= l_dma_done_d & l_done;
always_comb intf_dma_eng.dma_regfile_done_all 	= l_dma_done_d & (b_tsz_cnt_is_0_r | (intf_dma_eng.i_dma_nd & l_chunk_cnt_is_0_d));

always_comb
	intf_dma_eng.dma_chsel_next_ch =  intf_dma_eng.dma_regfile_done;

// Register Update Outputs
always_comb intf_dma_eng.dma_regfile_txsz = ld_desc_sel ? intf_dma_eng.wbif_dma_mast0_idata[11:0] : l_tsz_cnt;
always_comb intf_dma_eng.dma_regfile_adr0 = ld_desc_sel ? intf_dma_eng.wbif_dma_mast0_idata : {l_adr0_cnt, 2'b00};
always_comb intf_dma_eng.dma_regfile_adr1 = ld_desc_sel ? intf_dma_eng.wbif_dma_mast0_idata : {l_adr1_cnt, 2'b00};
always_comb intf_dma_eng.dma_regfile_csr  = intf_dma_eng.wbif_dma_mast0_idata;

// Abort logic
always_comb
	l_dma_abort_r =  intf_dma_eng.regfile_dma_stop | intf_dma_eng.wbif_dma_mast0_err | intf_dma_eng.wbif_dma_mast1_err;

always_comb	intf_dma_eng.dma_regfile_err  = l_dma_abort_r;
always_comb 	intf_dma_eng.dma_regfile_busy = (!l_dma_pstate[p_dma_idle]);


always_ff @(posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
        b_read_r <=  (intf_dma_eng.i_reset == 'b1) ? 'b0 : b_read;
   
always_ff @(posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
        b_write_r <=  (intf_dma_eng.i_reset == 'b1) ? 'b0 : b_write;
        
        
// ====================================================================
// Data Path
always_comb
	 intf_dma_eng.dma_wbif_mast0_odata = b_m0_we ? {20'h0, l_tsz_cnt} : 
				intf_dma_eng.chsel_dma_csr[`SRC_SEL] ? intf_dma_eng.wbif_dma_mast1_idata : 
				intf_dma_eng.wbif_dma_mast0_idata;
always_comb 
	intf_dma_eng.dma_wbif_mast1_odata = intf_dma_eng.chsel_dma_csr[`SRC_SEL] ? intf_dma_eng.wbif_dma_mast1_idata : 
					 intf_dma_eng.wbif_dma_mast0_idata;

// Address Path
always @(posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
        intf_dma_eng.dma_wbif_mast0_addr <=  b_m0_go ?
                (b_m0_we ? intf_dma_eng.chsel_dma_swpt : {intf_dma_eng.chsel_dma_desc[31:4], l_desc_cnt, 2'b00}) :
                b_read ? {l_adr0_cnt, 2'b00} : {l_adr1_cnt, 2'b00};

always @(posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
        intf_dma_eng.dma_wbif_mast1_addr <=  b_read ? {l_adr0_cnt, 2'b00} : {l_adr1_cnt, 2'b00};
                

// ====================================================================
// CTRL
always_comb l_write_hold 	= (b_read | b_write) & l_write_hold_r;
always_comb l_write_hold_r 	=  b_read | b_write;
always_comb l_read_hold 	= l_done ? b_read : (b_read | b_write);
                
always_comb intf_dma_eng.dma_wbif_mast0_start = (!intf_dma_eng.chsel_dma_csr[`SRC_SEL] & l_read_hold) |
					     (!intf_dma_eng.chsel_dma_csr[`DEST_SEL] & l_write_hold) | b_m0_go;
always_comb intf_dma_eng.dma_wbif_mast1_start = ( intf_dma_eng.chsel_dma_csr[`SRC_SEL] & l_read_hold) | 
					     ( intf_dma_eng.chsel_dma_csr[`DEST_SEL] & l_write_hold);
                
always_comb intf_dma_eng.dma_wbif_mast0_wrnrd = b_m0_go ? b_m0_we : (!intf_dma_eng.chsel_dma_csr[`DEST_SEL] & b_write);
always_comb intf_dma_eng.dma_wbif_mast1_wrnrd = intf_dma_eng.chsel_dma_csr[`DEST_SEL] & b_write;

always_comb b_rd_ack = (intf_dma_eng.chsel_dma_csr[`SRC_SEL] ? intf_dma_eng.wbif_dma_mast1_drdy : intf_dma_eng.wbif_dma_mast0_drdy);
always_comb b_wr_ack = (intf_dma_eng.chsel_dma_csr[`DEST_SEL] ? intf_dma_eng.wbif_dma_mast1_drdy : intf_dma_eng.wbif_dma_mast0_drdy);
                
always_comb intf_dma_eng.dma_wbif_mast0_wait = !((!intf_dma_eng.chsel_dma_csr[`SRC_SEL] & b_read) | 
					    (!intf_dma_eng.chsel_dma_csr[`DEST_SEL] & b_write)) & !b_m0_go;
always_comb intf_dma_eng.dma_wbif_mast1_wait = !(( intf_dma_eng.chsel_dma_csr[`SRC_SEL] & b_read) | 
					    ( intf_dma_eng.chsel_dma_csr[`DEST_SEL] & b_write));
                                
always_comb l_mast0_drdy_r =  intf_dma_eng.wbif_dma_mast0_drdy;
                
always_comb  intf_dma_eng.dma_chsel_ack = intf_dma_eng.dma_regfile_done;

// ====================================================================
// State machine
always @ (posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
	begin
		if (intf_dma_eng.i_reset == 'b1)
                begin
		l_dma_nstate <= 11'b00000001;	// Default keep state
		l_dma_done_d <= 'b0;
                end
		else
		begin
		//l_dma_nstate [p_dma_pause]		<= intf_dma_eng.regfile_dma_pause ? 1'b1 : 1'b0;	
		b_m0_go 	 		 	<= 'b0;
//		intf_dma_eng.dma_wbif_mast1_start 	  	<= 'b0;
		intf_dma_eng.dma_paused			<= 'b0; 	

		//l_dma_nstate <= 8'b00000000;	

	unique	case (1'b1) 

		l_dma_nstate[p_dma_idle] : 
		begin
			l_dma_done_d <= 'b0;
			if ((intf_dma_eng.chsel_dma_start == 1'b1) & (intf_dma_eng.chsel_dma_csr[`USE_ED] == 1'b0))
			begin 
				l_dma_nstate 		  <= 11'b00000001000;
			end 
			else if (intf_dma_eng.chsel_dma_start == 1'b1 & intf_dma_eng.chsel_dma_csr[`USE_ED] == 1'b1)
			begin	
				l_dma_nstate 		         <= 11'b00000100000;
			end	
			else
			begin
				l_dma_nstate 		  <= 11'b00000000001;
			end

		end

		l_dma_nstate[p_dma_pause] : 
		begin
			intf_dma_eng.dma_paused <= 1'b1;
			if (intf_dma_eng.regfile_dma_pause == 1'b0)
			begin
				$display ("DMA :l_dma_pstate[p_dma_pause]"); 
				intf_dma_eng.dma_paused 		 <= 1'b0;
				l_dma_nstate <= 11'b00000000001; 
			end
			else 
			begin
				l_dma_nstate <= 11'b00000000010; 
			end
		end

		l_dma_nstate[p_dma_read] :	// Read From Source 
		begin
			if (intf_dma_eng.regfile_dma_stop == 1'b1)
			begin	
				l_dma_nstate 		  <= 11'b00000000100;
			end
			else if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
			begin
				l_dma_nstate 		  <= 11'b00000010000;
				b_write			   <= 1'b1;
				b_read 			   <= 1'b0; 
			end

			else	
			begin
				b_read 			   <= 1'b1;
				l_dma_nstate 		  <= 11'b00000001000;
			end
		end

		l_dma_nstate[p_dma_write] :	// Write To Destination
		begin
                        if (intf_dma_eng.regfile_dma_stop == 1'b1  || l_done == 1'b1)
			begin
				b_write			    <= 1'b0;	
				l_dma_nstate 		  <= 11'b00000000100;
			end

			else if ((intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1) &&
				 (b_ld_desc == 1'b1))
			begin
				b_write			    <= 1'b0;	
				l_dma_nstate 		  <= 11'b00000000100;
			end

			else if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
			begin
				b_read 			  <= 1'b1;
				b_write			  <= 1'b0;
				l_dma_nstate 		  <= 11'b00000001000;
			end

			else
				l_dma_nstate 		  <= 11'b00000010000;
		end

		l_dma_nstate[p_dma_ld_desc_csr] :	// Load Descriptor from memory to registers 
		begin
			if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
			begin
				l_dma_nstate 		  <= 11'b00000100000;
			end
			else
			begin
				l_dma_nstate 		  <= 11'b00001000000;
			end
		end

		l_dma_nstate[p_dma_ld_src_addr] : 
		begin
			if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
			begin
				l_dma_nstate 		  <= 11'b00010000000;
			end
			else
			begin
				l_dma_nstate 		  <= 11'b00001000000;
			end
		end
		l_dma_nstate[p_dma_ld_dest_addr] : 
		begin
			if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
				l_dma_nstate 		  <= 11'b00010000000;
			else
				l_dma_nstate 		  <= 11'b00001000000;
		end

		l_dma_nstate[p_dma_ld_next_desc] : 
		begin
			if (intf_dma_eng.wbif_dma_mast0_drdy == 1'b1 || intf_dma_eng.wbif_dma_mast1_drdy == 1'b1)
			begin
				l_dma_nstate 		  <= 11'b00100000000;

			end
			else
				l_dma_nstate 		  <= 11'b00010000000;
		end

		l_dma_nstate[p_dma_update] :	// Update Registers
		begin
			l_dma_done_d <= 'b1;
			if ((intf_dma_eng.regfile_dma_stop == 1'b1) || (l_dma_done_d == 'b1)) 
			begin
				l_dma_nstate 		  <= 11'b00000000001;
			end	
			else if (b_ld_desc == 1'b1 && l_desc_data[`EOL] == 1'b1)  
			begin	
				b_m0_go 		  <= 'b1;	
				l_dma_nstate 		  <= 11'b01000000000;
			end
			else if (intf_dma_eng.chsel_dma_csr [`ARS]  == 1'b1 && intf_dma_eng.i_dma_rest  == 1'b1)
			begin	
				l_dma_nstate 		  <= 11'b00000001000;
			end	
			else
			begin	
				l_dma_done_d <= l_dma_done_d ? 'b0 : 'b1;
				l_dma_nstate 		  <= 11'b00000000100;
			end
	
		end		

		l_dma_nstate[p_dma_wr_csr_done] :
			begin
			l_dma_nstate 		  <= 11'b00000000001;
			l_dma_done_d <= 'b0;
			$display ("DMA : l_dma_pstate[p_dma_wr_csr_done]");
			end
	endcase 
	end
	end // always_comb

always @ (posedge intf_dma_eng.i_clk or posedge intf_dma_eng.i_reset)
	begin
		if (intf_dma_eng.i_reset == 'b1)
		l_dma_pstate <= 11'b0000001;
		else
		l_dma_pstate <= l_dma_nstate;	
	end  // always_ff


endmodule // dma_eng
