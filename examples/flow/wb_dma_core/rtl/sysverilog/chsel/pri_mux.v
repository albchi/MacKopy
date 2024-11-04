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
// Name of the module   : DMA priority mux 
// Author               : Subha Amancherla 
// Project name         : Wishbone DMA/Bridge core
// Created on           : 09/23/2003
// Updated on           :
// Purpose of module    :
// Comments             :
// *************************************************

`include "inc_addr.v"

module mod_pri_mux (intf_wb_top.ch_sel intf_chmux);

//==============================================================================
//Generate statement for csr selection out of 31 channels
genvar m;
generate for(m=0;m<=30;m=m+1)
begin:mux1
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       m: intf_chmux.chsel_dma_csr = intf_chmux.str_inst.regfile_chsel_ch_csr[m];
endcase
end
end
endgenerate


//==============================================================================
//Generate statement for sz selection out of 31 channels
genvar n;
generate for(n=0;n<=30;n=n+1)
begin:mux2
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       n: intf_chmux.chsel_dma_sz = intf_chmux.str_inst.regfile_chsel_ch_sz[n];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for a0 selection out of 31 channels
genvar o;
generate for(o=0;o<=30;o=o+1)
begin:mux3
always_ff @ (intf_chmux.chsel_dma_sel_val)begin
case(intf_chmux.chsel_dma_sel_val)
       o: intf_chmux.chsel_dma_a0 = intf_chmux.str_inst.regfile_chsel_ch_a0[o];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for a1 selection out of 31 channels
genvar p;
generate for(p=0;p<=30;p=p+1)
begin:mux4
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       p: intf_chmux.chsel_dma_a1 = intf_chmux.str_inst.regfile_chsel_ch_a1[p];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for a1 selection out of 31 channels
genvar q;
generate for(q=0;q<=30;q=q+1)
begin:mux5
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       q: intf_chmux.chsel_dma_am0 = intf_chmux.str_inst.regfile_chsel_ch_am0[q];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for a1 selection out of 31 channels
genvar r;
generate for(r=0;r<=30;r=r+1)
begin:mux6
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       r: intf_chmux.chsel_dma_am1 = intf_chmux.str_inst.regfile_chsel_ch_am1[r];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for a1 selection out of 31 channels
genvar s;
generate for(s=0;s<=30;s=s+1)
begin:mux7
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       s: intf_chmux.chsel_dma_desc = intf_chmux.str_inst.regfile_chsel_ch_desc[s];
endcase
end
end
endgenerate

//==============================================================================
//Generate statement for swpt selection out of 31 channels
genvar t;
generate for(t=0;t<=30;t=t+1)
begin:mux8
always_ff @ (intf_chmux.chsel_dma_sel_val) begin
case(intf_chmux.chsel_dma_sel_val)
       t: intf_chmux.chsel_dma_swpt = intf_chmux.str_inst.regfile_chsel_ch_swpt[t];
endcase
end
end
endgenerate

endmodule
