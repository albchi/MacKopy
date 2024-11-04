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

module utopia_atm_rx(atm_interface.rx rx_i);

//
// Configuration parameters
//
parameter
         Q_LENGTH = 32;   // Size of Rx cell buffer

//
// Rx cell1 buffer
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
   rx_i.en = 1'b1;
end
endtask
initial reset;


//
// Extract the next cell1 that was received
//
parameter
         BLOCKING  = 1'b1,
         NON_BLOCK = 1'b0;

task get_cell;
   input           blocking;  // BLOCKING or NON_BLOCK
   output [53*8:1] cell1;      // The cell1
   output          valid;     // May not be valid if buffer
                              // is rx_i.empty_full and NON_BLOCK.
   reg  in_use;
begin
   if (in_use) begin
      $write("FATAL: Concurrent invocation of %M.\n");
      $finish;
   end
   in_use = 1'b1;

   begin: return1
      // Is the Rx buffer rx_i.empty_full?
      if (rd_ptr === wr_ptr) begin
         // Return an invalid cell1 if non-blocking
         if (!blocking) begin
            cell1  = 424'bx;
            valid = 1'b0;
            disable return1;
         end

         // Wait for a cell1 to be avaible
         wait (rd_ptr !== wr_ptr);
      end

      // Return the valid cell1 at the front of the buffer
      cell1   = cell_q[rd_ptr];
      rd_ptr = (rd_ptr + 1) % Q_LENGTH;
      valid  = 1'b1;
   end

   in_use = 1'b0;
end
endtask


//
// Free-running 25MHz Rx rx_i.clk
//
always
begin
   rx_i.clk = 1'b0;
   #20; // ns
   rx_i.clk = 1'b1;
   #20; // ns
end


//
// Listen to the interface, collecting
// cell1s into the Rx buffer
//
always
begin: listen
   reg [53*8:1] cell1;
   
   // First, wait for room in the Rx buffer
   if (((wr_ptr + 1) % Q_LENGTH) === rd_ptr) begin
      rx_i.en <= #1 1'b1;
      // Wait for the rd_ptr to change
      wait (((wr_ptr + 1) % Q_LENGTH) !== rd_ptr);
      @ (posedge rx_i.clk);
   end
   rx_i.en <= #1 1'b0;

   // Wait for the start of the next cell1
   while (rx_i.soc !== 1'b1 || rx_i.empty_full !== 1'b1) @ (posedge rx_i.clk);

   // We have the first word.
   cell1 = rx_i.data;
   
   // Now sample the next 52 consecutive non-rx_i.empty_full
   // bytes
   repeat (52) begin
      cell1 = cell1 << 8;
      @ (posedge rx_i.clk);
      while (rx_i.empty_full !== 1'b1) @ (posedge rx_i.clk);
      cell1[8:1] = rx_i.data;
   end

   // Put the new cell1 in the cell1 buffer
   cell_q[wr_ptr] = cell1;
   wr_ptr = (wr_ptr + 1) % Q_LENGTH;
end

endmodule
