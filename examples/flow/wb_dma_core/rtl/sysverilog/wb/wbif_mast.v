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
// Name of the module   : WISHBONE MASTER
// Author               : Meena Rani
// Project name         : Wishbone DMA/Bridge core
// Created on           : 08/29/2003
// Updated on           :
// Purpose of module    :Master interface capable of generating bus cycles
// Comments             :
// *************************************************

module u_wbif_mast(intf_wb_top.wb_if intf_wbif,wb_pass pt);

bit dma_wbif_mast0_cyc,dma_wbif_mast0_we,dma_wbif_mast0_strb,
    dma_wbif_mast1_cyc,dma_wbif_mast1_we,dma_wbif_mast1_strb;

logic [3:0] dma_wbif_mast0_byte_sel,dma_wbif_mast1_byte_sel;

////////////  PASS THROUGH  INTERFACE LOGIC

always_comb begin

{intf_wbif.o_slv0_data,intf_wbif.o_mast0_addr,intf_wbif.o_mast0_strb, intf_wbif.o_mast0_byte_sel,intf_wbif.o_mast0_we, intf_wbif.o_mast0_cyc} = pt.pt0_sel_in ? 
    pt.mast0_pt_data_in : {intf_wbif.dma_wbif_mast0_odata,intf_wbif.dma_wbif_mast0_addr,dma_wbif_mast0_strb,dma_wbif_mast0_byte_sel,dma_wbif_mast0_we,dma_wbif_mast0_cyc};  

{intf_wbif.o_slv1_data,intf_wbif.o_mast1_addr,intf_wbif.o_mast1_strb, intf_wbif.o_mast1_byte_sel,intf_wbif.o_mast1_we, intf_wbif.o_mast1_cyc} = pt.pt1_sel_in ?                                       
    pt.mast1_pt_data_in : {intf_wbif.dma_wbif_mast1_odata,intf_wbif.dma_wbif_mast1_addr,dma_wbif_mast1_strb,dma_wbif_mast1_byte_sel,dma_wbif_mast1_we,dma_wbif_mast1_cyc};

pt.mast0_pt_data_out = {intf_wbif.i_mast0_ack,intf_wbif.i_mast0_err,intf_wbif.i_mast0_retry,intf_wbif.i_slv0_data}; 

pt.mast1_pt_data_out = {intf_wbif.i_mast1_ack,intf_wbif.i_mast1_err,intf_wbif.i_mast1_retry,intf_wbif.i_slv1_data}; 

intf_wbif.wbif_dma_mast0_err  = intf_wbif.i_mast0_err; 
intf_wbif.wbif_dma_mast0_drdy = intf_wbif.i_mast0_ack;

intf_wbif.wbif_dma_mast1_err  = intf_wbif.i_mast1_err; 
intf_wbif.wbif_dma_mast1_drdy = intf_wbif.i_mast1_ack;

end

/////////// DMA INTERFACE LOGIC
always_ff  @(posedge intf_wbif.i_clk)
begin
  dma_wbif_mast0_cyc <= intf_wbif.dma_wbif_mast0_start;
  dma_wbif_mast1_cyc <= intf_wbif.dma_wbif_mast1_start;
end

always_ff @(posedge intf_wbif.i_clk)
begin
  dma_wbif_mast0_we <= intf_wbif.dma_wbif_mast0_wrnrd;
  dma_wbif_mast1_we <= intf_wbif.dma_wbif_mast1_wrnrd;
end

always_ff @(posedge intf_wbif.i_clk)
begin
  dma_wbif_mast0_strb <= intf_wbif.dma_wbif_mast0_start & !intf_wbif.dma_wbif_mast0_wait;
  dma_wbif_mast1_strb <= intf_wbif.dma_wbif_mast0_start & !intf_wbif.dma_wbif_mast0_wait;
end

always_ff @(posedge intf_wbif.i_clk)
begin
 dma_wbif_mast0_byte_sel <= 4'hf;
 dma_wbif_mast1_byte_sel <= 4'hf;
end

always_ff @(posedge intf_wbif.i_clk)
begin
  if(intf_wbif.i_mast0_ack)  intf_wbif.wbif_dma_mast0_idata <= intf_wbif.i_slv0_data;
  if(intf_wbif.i_mast1_ack)  intf_wbif.wbif_dma_mast1_idata <= intf_wbif.i_slv1_data;
end

endmodule
