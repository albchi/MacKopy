/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

//
//      Copyright (c) 2000 by Qualis Design Corporation. All rights reserved.
//      
//
//      This file contains licensed materials and may used and distributed
//      provided that this copyright statement is not removed from the file
//      and that any derivative work contains this copyright notice.
//
//      Qualis Design Corporation            Synopsys, Inc.
//      http://www.qualis.com                http://www.synopsys.com
//
// Description:
//      Bus-functional receiver model for a Utopia interface.
//      The bus-functional model is considered an ATM-layer device.
//
// Author:      $Author: badri $
// Revision:    $Revision: 1.1 $
//

`resetall

module utopia_atm_rx(clk, data, soc, en, empty);

//
// Configuration parameters
//
parameter
         Q_LENGTH = 32;   // Size of Rx cell buffer

output       clk;
input  [7:0] data;
input        soc; 
output       en;  
input        empty;

reg  en;  

//
// Rx cell buffer
//
reg [53*8:1] cell_q [0:Q_LENGTH-1];
integer      rd_ptr;
integer      wr_ptr;


//
// Reset this bus-functional model
//
task reset;
begin
   rd_ptr = 0;
   wr_ptr = 0;
   disable get_cell;
   disable listen;
   get_cell.in_use = 1'b0;

   // Outputs
   en = 1'b1;
end
endtask
initial reset;


//
// Extract the next cell that was received
//
parameter
         BLOCKING  = 1'b1,
         NON_BLOCK = 1'b0;

task get_cell;
   input           blocking;  // BLOCKING or NON_BLOCK
   output [53*8:1] cell;      // The cell
   output          valid;     // May not be valid if buffer
                              // is empty and NON_BLOCK.
   reg  in_use;
begin
   if (in_use) begin
      $write("FATAL: Concurrent invocation of %M.\n");
      $finish;
   end
   in_use = 1'b1;

   begin: return
      // Is the Rx buffer empty?
      if (rd_ptr === wr_ptr) begin
         // Return an invalid cell if non-blocking
         if (!blocking) begin
            cell  = 424'bx;
            valid = 1'b0;
            disable return;
         end

         // Wait for a cell to be avaible
         wait (rd_ptr !== wr_ptr);
      end

      // Return the valid cell at the front of the buffer
      cell   = cell_q[rd_ptr];
      rd_ptr = (rd_ptr + 1) % Q_LENGTH;
      valid  = 1'b1;
   end

   in_use = 1'b0;
end
endtask


//
// Free-running 25MHz Rx clk
//
reg  clk;
always
begin
   clk = 1'b0;
   #20; // ns
   clk = 1'b1;
   #20; // ns
end


//
// Listen to the interface, collecting
// cells into the Rx buffer
//
always
begin: listen
   reg [53*8:1] cell;
   
   // First, wait for room in the Rx buffer
   if (((wr_ptr + 1) % Q_LENGTH) === rd_ptr) begin
      en <= #1 1'b1;
      // Wait for the rd_ptr to change
      wait (((wr_ptr + 1) % Q_LENGTH) !== rd_ptr);
      @ (posedge clk);
   end
   en <= #1 1'b0;

   // Wait for the start of the next cell
   while (soc !== 1'b1 || empty !== 1'b1) @ (posedge clk);

   // We have the first word.
   cell = data;
   
   // Now sample the next 52 consecutive non-empty
   // bytes
   repeat (52) begin
      cell = cell << 8;
      @ (posedge clk);
      while (empty !== 1'b1) @ (posedge clk);
      cell[8:1] = data;
   end

   // Put the new cell in the cell buffer
   cell_q[wr_ptr] = cell;
   wr_ptr = (wr_ptr + 1) % Q_LENGTH;
end

endmodule
