/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

//tasks to read from / write to memory via memory controller

task read_mem;
      input [7:0] address;
      output [7:0] data;
      begin
	 @(negedge clk);
	 busAddr = address;
	 busRdWr_N = 1'b1;
	 adxStrb = 1'b1;
	 @(negedge clk);
	 adxStrb = 1'b0;
	 repeat(2) @(negedge clk);
	 data = busData;
	 if ($test$plusargs("debug")) begin
	    $display("[%0t] read_memsys: address %0h data %0h",
		     $time,
		     address,
		     data);
	 end
      end
endtask // read_mem

 reg [7:0] tb_busData;
 assign busData = tb_busData;

task write_mem;
      input [7:0] address;
      input [7:0] data;
      begin
	 @(posedge clk);
	 #1;
	 busAddr = address;
	 tb_busData = data;
	 busRdWr_N = 1'b0;
	 adxStrb = 1'b1;
	 @(posedge clk);
	 #1;
	 busRdWr_N = 1'b1;
	 adxStrb = 1'b0;
	 tb_busData = 8'bzzzzzzzz;
	 repeat(4) @(posedge clk);
	 if ($test$plusargs("debug")) begin
	    $display("[%0t] write_mem: address %0h data %0h",
		     $time,
		     address,
		     data);
	 end
      end
endtask // write_mem
