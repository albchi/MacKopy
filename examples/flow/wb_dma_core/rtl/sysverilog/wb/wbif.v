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
// Name of the module   : WISHBONE INTERFACE
// Author               : Meena Rani
// Project name         : Wishbone DMA/Bridge core
// Created on           : 08/29/2003
// Updated on           :
// Purpose of module    :Wishbone interface defiens Master and Slave interface
//                       capable of generating and receiving Bus cycles  
// Comments             :
// *************************************************

interface wb_pass;
// Pass Through Interface
logic           pt0_sel_in;          // Pass Through Mode Selected
logic           pt1_sel_in;          // Pass Through Mode Selected
logic  [70:0]  mast0_pt_data_in;     // Grouped WISHBONE inputs
logic  [70:0]  mast1_pt_data_in;     // Grouped WISHBONE inputs
logic  [34:0]  mast1_pt_data_out;    // Grouped WISHBONE outputs
logic  [34:0]  mast0_pt_data_out;    // Grouped WISHBONE outputs

// Pass through Interface
logic          pt0_sel_out;          // Pass Through Mode Active
logic          pt1_sel_out;         // Pass Through Mode Active
logic [70:0]  slv0_pt_data_out;     // Grouped WISHBONE out signals
logic [70:0]  slv1_pt_data_out;     // Grouped WISHBONE out signals
logic   [34:0]  slv1_pt_data_in;    // Grouped WISHBONE in signals
logic   [34:0]  slv0_pt_data_in;    // Grouped WISHBONE in signals

endinterface:wb_pass

module wbif(intf_wb_top.wb_if intf_top); 

wb_pass pt();

//INTERCONNECTING PASS THROUGH SIGNALS 
always_comb begin
pt.pt1_sel_in = pt.pt0_sel_out;
pt.pt0_sel_in = pt.pt1_sel_out;
pt.mast1_pt_data_in = pt.slv0_pt_data_out;
pt.slv0_pt_data_in  = pt.mast1_pt_data_out;
pt.mast0_pt_data_in = pt.slv1_pt_data_out;
pt.slv1_pt_data_in  = pt.mast0_pt_data_out;
end

//Instantiating Master and Slave modules
u_wbif_mast u_mast(intf_top,pt);
u_wbif_slave u_slave(intf_top,pt); 

endmodule
