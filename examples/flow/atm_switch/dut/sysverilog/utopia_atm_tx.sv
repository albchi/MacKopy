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

module utopia_atm_tx(atm_interface.tx tx_i);

//
// Configuration parameters
//
parameter
         Q_LENGTH = 32;   // Size of Rx cell buffer

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
   tx_i.data = 8'hXX;
   tx_i.soc  = 1'b0;
   tx_i.en   = 1'b1;
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
   input  [53*8:1] cell1;      // The cell
   output          valid;     // May not be valid if buffer
                              // is tx_i.empty_full and NON_BLOCK.
   reg  in_use;
   integer this_cell;
begin
   if (in_use) begin
      $write("FATAL: Concurrent invocation of %M.\n");
      $finish;
   end
   in_use = 1'b1;

   valid = 1'b1;

   begin: return1
      // Is the Tx buffer tx_i.empty_full?
      if (((wr_ptr + 1) % Q_LENGTH) === rd_ptr) begin
         // Return an invalid status
         if (!blocking) begin
            valid = 1'b0;
            disable return1;
         end

         // Wait for a slot to be avaible
         wait (((wr_ptr + 1) % Q_LENGTH) !== rd_ptr);
      end

      // Add the cell at the end of the buffer
      cell_q[wr_ptr] = cell1;
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
// Free-running 25MHz Rx tx_i.clk
//
always
begin
   tx_i.clk = 1'b0;
   #20; // ns
   tx_i.clk = 1'b1;
   #20; // ns
end


//
// Talk to the interface, sending
// cells from the Tx buffer
//
always
begin: talk
   reg [53*8:1] cell1;
   
   // First, wait for a cell in the Tx buffer
   if (rd_ptr === wr_ptr) begin
      // Wait for the wr_ptr to change
      wait (rd_ptr !== wr_ptr);
      @ (posedge tx_i.clk);
   end

   // Grab the cell out of the Tx buffer
   // but don't increment the rd pointer yet.
   // Only do that once the cell has been fully sent.
   cell1 = cell_q[rd_ptr];

   // Wait for the PHY layer to indicate it
   // can accept a cell/byte
   while (tx_i.empty_full !== 1'b1) begin
      @ (posedge tx_i.clk);
   end
   
   // Indicate the start of the next cell
   tx_i.soc  <= #1 1'b1;
   tx_i.data <= #1 cell1[424:417];
   tx_i.en   <= #1 1'b0;

   // Now send the next 52 consecutive non-empty
   // bytes
   repeat (52) begin
      cell1 = cell1 << 8;
      @ (posedge tx_i.clk);
      tx_i.soc  <= #1 1'b0;
      while (tx_i.empty_full !== 1'b1) begin
         tx_i.en   <= #1 1'b1;
         @ (posedge tx_i.clk);
      end
      tx_i.data <= #1 cell1[424:417];
      tx_i.en   <= #1 1'b0;
   end
   @ (posedge tx_i.clk);
   tx_i.en <= #1 1'b1; 

   // Consume the cell out of the buffer
   rd_ptr = (rd_ptr + 1) % Q_LENGTH;
end

endmodule
