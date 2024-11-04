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
// Name of the module   : WISHBONE SLAVE
// Author               : Meena Rani
// Project name         : Wishbone DMA/Bridge core
// Created on           : 08/29/2003
// Updated on           :
// Purpose of module    : Wishbone Slave are capable of receiving bus cycles
// Comments             :
// *************************************************

module u_wbif_slave(intf_wb_top.wb_if intf_slv,wb_pass pt);

logic rf_sel;
logic l1, l2;
/////////////////////////////////////////////////////////////////////
//
// Logic for rf_sel Pass through or reg file selection is done here
// This define selects how the slave interface determines if
// the internal register file or pass through mode are selected.
// This should be a simple address decoder. "wb_addr_i" is the
// WISHBONE address bus (32 bits wide).
// NOTE: The entire pass-through mode is implemented in combinatorial
// logic only. So the more address lines we look at and compare here
// the higher will be the initial delay when pass-through mode is selected.
// Here we look at the top 8 address bit. If they are all 1, the
// register file is selected. Use this with caution !!!
//`define WDMA_REG_SEL            (intf_slv.i_slv0_addr[31:28] == rf_addr)

//assign rf_sel = ((intf_slv.i_slv0_addr[31:28] == p_rf_addr) || 
//		 (intf_slv.i_slv1_addr[31:28] == p_rf_addr)) ? 1'b1 : 1'b1; // Subha 11/05

assign rf_sel = ((intf_slv.i_slv0_addr[31:28] == p_rf_addr) ||
		(intf_slv.i_slv0_addr[31:28] == p_rf_addr)) 
		 ? 1'b1 : 1'b0; // Subha 11/05


//  END OF Logic for Pass through selection
//
////////////////////////////////////////////////////////////////////


///////////// PASS THROUGH  LOGIC

always_comb 
begin
//pt.pt0_sel_out = (!rf_sel & intf_slv.i_slv0_strb) ? 1'b1 : 1'b0;      //When HIGH Pass through mode is Active
//pt.pt1_sel_out = !rf_sel & intf_slv.i_slv1_strb? 1'b1 : 1'b0;      //When HIGH Pass through mode is Active
pt.pt0_sel_out = (!rf_sel & intf_slv.i_slv0_strb & intf_slv.i_slv0_cyc); // When HIGH Pass through mode is Active
pt.pt1_sel_out = (!rf_sel & intf_slv.i_slv1_strb & intf_slv.i_slv1_cyc); //When HIGH Pass through mode is Active

{intf_slv.o_slv0_ack,intf_slv.o_slv0_err,intf_slv.o_slv0_retry,intf_slv.o_mast0_data} = pt.pt0_sel_out ? pt.slv0_pt_data_in : {intf_slv.wbif_regfile_ack,1'b0,1'b0,intf_slv.regfile_wbif_data};

{intf_slv.o_slv1_ack,intf_slv.o_slv1_err,intf_slv.o_slv1_retry,intf_slv.o_mast1_data} = pt.pt1_sel_out ? pt.slv1_pt_data_in : {intf_slv.wbif_regfile_ack,1'b0,1'b0,intf_slv.regfile_wbif_data};

pt.slv0_pt_data_out = {intf_slv.i_mast0_data,intf_slv.i_slv0_addr,intf_slv.i_slv0_strb,intf_slv.i_slv0_byte_sel,intf_slv.i_slv0_we,intf_slv.i_slv0_cyc};

pt.slv1_pt_data_out = {intf_slv.i_mast1_data,intf_slv.i_slv1_addr,intf_slv.i_slv1_strb,intf_slv.i_slv1_byte_sel,intf_slv.i_slv1_we,intf_slv.i_slv1_cyc};

end

//////////// Register file logic

always_ff @(posedge intf_slv.i_clk)
   intf_slv.i_wr_data <= intf_slv.i_mast0_data;

always_ff @(posedge intf_slv.i_clk)
    intf_slv.i_wr_addr <= intf_slv.i_slv0_addr;

always_ff @(posedge intf_slv.i_clk)
   intf_slv.i_wr <= rf_sel & intf_slv.i_slv0_cyc & intf_slv.i_slv0_strb & intf_slv.i_slv0_we & !intf_slv.wbif_regfile_ack; 


always_ff @(posedge intf_slv.i_clk)
intf_slv.wbif_regfile_ack <= (intf_slv.i_wr | intf_slv.i_rd) & intf_slv.i_slv0_cyc & intf_slv.i_slv0_strb & !intf_slv.wbif_regfile_ack;

always_ff @(posedge intf_slv.i_clk)
  intf_slv.i_rd <= rf_sel & intf_slv.i_slv0_cyc & intf_slv.i_slv0_strb & !intf_slv.i_slv0_we & !intf_slv.wbif_regfile_ack ;


endmodule
