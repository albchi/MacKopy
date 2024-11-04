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
//      Bus-functional transmitter model for a Utopia interface.
//      The bus-functional model is considered an ATM-layer device.
//
// Author:      $Author: badri $
// Revision:    $Revision: 1.1 $
//

`resetall

module utopia_atm_tx(clk, data, soc, en, full);

//
// Configuration parameters
//
parameter
         Q_LENGTH = 32;   // Size of Rx cell buffer

output       clk;
output [7:0] data;
output       soc; 
output       en;  
input        full;

reg [7:0] data;
reg       en;
reg       soc;

//
// Tx cell buffer
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
   disable put_cell;
   disable talk;
   put_cell.in_use = 1'b0;

   // Outputs
   data = 8'hXX;
   soc  = 1'b0;
   en   = 1'b1;
end
endtask
initial reset;


//
// Add the next cell to be transmitted
//
parameter
         BLOCKING  = 1'b1,
         NON_BLOCK = 1'b0;

task put_cell;
   input           blocking;  // BLOCKING or NON_BLOCK
   input  [53*8:1] cell;      // The cell
   output          valid;     // May not be valid if buffer
                              // is full and NON_BLOCK.
   reg  in_use;
   integer this_cell;
begin
   if (in_use) begin
      $write("FATAL: Concurrent invocation of %M.\n");
      $finish;
   end
   in_use = 1'b1;

   valid = 1'b1;

   begin: return
      // Is the Tx buffer full?
      if (((wr_ptr + 1) % Q_LENGTH) === rd_ptr) begin
         // Return an invalid status
         if (!blocking) begin
            valid = 1'b0;
            disable return;
         end

         // Wait for a slot to be avaible
         wait (((wr_ptr + 1) % Q_LENGTH) !== rd_ptr);
      end

      // Add the cell at the end of the buffer
      cell_q[wr_ptr] = cell;
      this_cell      = wr_ptr;
      wr_ptr = (wr_ptr + 1) % Q_LENGTH;
      // If blocking, wait until this cell is transmitted
      if (blocking) begin
         // Wait for the read pointere to go past the
         // location of this cell, indicating that it
         // has been transmitted.
         wait (rd_ptr === this_cell);
         wait (rd_ptr !== this_cell);
      end
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
// Talk to the interface, sending
// cells from the Tx buffer
//
always
begin: talk
   reg [53*8:1] cell;
   
   // First, wait for a cell in the Tx buffer
   if (rd_ptr === wr_ptr) begin
      // Wait for the wr_ptr to change
      wait (rd_ptr !== wr_ptr);
      @ (posedge clk);
   end

   // Grab the cell out of the Tx buffer
   // but don't increment the rd pointer yet.
   // Only do that once the cell has been fully sent.
   cell = cell_q[rd_ptr];

   // Wait for the PHY layer to indicate it
   // can accept a cell/byte
   while (full !== 1'b1) begin
      @ (posedge clk);
   end
   
   // Indicate the start of the next cell
   soc  <= #1 1'b1;
   data <= #1 cell[424:417];
   en   <= #1 1'b0;

   // Now send the next 52 consecutive non-empty
   // bytes
   repeat (52) begin
      cell = cell << 8;
      @ (posedge clk);
      soc  <= #1 1'b0;
      while (full !== 1'b1) begin
         en   <= #1 1'b1;
         @ (posedge clk);
      end
      data <= #1 cell[424:417];
      en   <= #1 1'b0;
   end
   @ (posedge clk);
   en <= #1 1'b1; 

   // Consume the cell out of the buffer
   rd_ptr = (rd_ptr + 1) % Q_LENGTH;
end

endmodule
