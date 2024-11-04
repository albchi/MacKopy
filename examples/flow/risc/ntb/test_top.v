/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`timescale 1ns / 10ps


module test_top;
      parameter simulation_cycle = 10 ;
  
      reg           SystemClock ;
      wire          clk ;
      wire          reset ;
      wire  [10:0]  paddr ;
      wire  [11:0]  pdata ;
      wire  [7:0]   portain ;
      wire  [7:0]   portbout ;
      wire  [7:0]   portcout ;
      wire  [7:0]   expdin ;
      wire  [7:0]   expdout ;
      wire  [6:0]   expaddr ;
      wire          expread ;
      wire          expwrite ;
      wire  [7:0]   debugw ;
      wire  [10:0]  debugpc ;
      wire  [11:0]  debuginst ;
      wire  [7:0]   debugstatus ;
      wire          Xtraffic;
      wire  [1:0]   hwy; 
      wire  [1:0]   cntry; 
      wire  [7:0]   aluout;
      wire          fwe;
      wire          wwe;

      assign clk = SystemClock;

      cpu_test vshell( //  veralite test program instantiated here
          .SystemClock ( SystemClock ),
    	  .\test.clk ( clk ),
       	  .\test.reset ( reset ),
          .\test.paddr ( paddr ),
          .\test.pdata ( pdata ),
          .\test.portain ( portain ),
          .\test.portbout ( portbout ),
          .\test.portcout ( portcout ),
          .\test.expdin ( expdin ),
          .\test.expdout ( expdout ),
          .\test.expaddr ( expaddr ),
          .\test.expread ( expread ),
          .\test.expwrite ( expwrite ),
          .\test.debugw ( debugw ),
          .\test.debugpc ( debugpc ),
          .\test.debuginst ( debuginst ),
          .\test.debugstatus ( debugstatus ),
          .\test.Xtraffic ( Xtraffic ),
          .\test.hwy ( hwy ),
          .\test.cntry ( cntry ),
          .\test.aluout ( test_top.dut.aluout ),
          .\test.fwe ( test_top.dut.idec.fwe ),
          .\test.wwe ( test_top.dut.idec.wwe )
           );

`ifdef emu        // Design modules instantiated here
/* DUT is in emulator, so not instantiated here */
`else
      cpu dut(
    	.clk ( clk ),
    	.reset ( reset ),
    	.paddr ( paddr ),
    	.pdata ( pdata ),
    	.portain ( portain ),
    	.portbout ( portbout ),
    	.portcout ( portcout ),
    	.expdin ( expdin ),
    	.expdout ( expdout ),
    	.expaddr ( expaddr ),
    	.expread ( expread ),
    	.expwrite ( expwrite ),
    	.debugw ( debugw ),
    	.debugpc ( debugpc ),
    	.debuginst ( debuginst ),
    	.debugstatus ( debugstatus )
         );


      pram pram1(
        .clk     (clk),
   	.address (paddr),
   	.we      (1'b0),   // this testbench doesn't allow writing to PRAM
   	.din     (12'b0),  // this testbench doesn't allow writing to PRAM
   	.dout    (pdata)
         );


      exp exp( 
   	.clk     (clk), 
   	.reset   (reset), 
   	.expdin  (expdin), 
   	.expdout (expdout), 
   	.expaddr (expaddr), 
   	.expread (expread), 
   	.expwrite (expwrite), 
   	.hwy     (hwy), 
   	.cntry   (cntry),
   	.X       (Xtraffic)
        ); 
  

`endif


 /* Initial block which generates the system clock. */

     initial
       begin
         SystemClock = 0 ;
         forever
           begin
             #(simulation_cycle/2)
             SystemClock = ~SystemClock ;
           end
       end



 /*  Task to load pram with the inputs for the basic test & ddstest  */

     task hdl_load_pram;  // begin of task
       input rom_file;
       reg [20*20-1:0]  rom_file;

       begin
         #1;
         $display ("--Loading program memory with %0s--", rom_file);
         $readmemh (rom_file, test_top.pram1.mem);
       end
     endtask  // end of the task



/* 
  task to extract the alu operands and outputs and then
  pass on to veralite side  
*/

     task get_alu;
       output  [7:0]    alu_out;
       output           cout; 
       output           zout;
       output integer   a;
       output integer   b;
       output integer   op;
       output integer   cin;

       begin
  	 alu_out = test_top.dut.alu.y;
 	 cout    = test_top.dut.alu.cout;
 	 zout    = test_top.dut.alu.zout;
 	 op      = test_top.dut.alu.op;
         a       = test_top.dut.alu.a;
         b       = test_top.dut.alu.b;
	 cin     = test_top.dut.alu.cin;
       end
     endtask


/* 
  task to load pram with the random data generated in 
  veralite memory for the random test. 
*/

     task hdl_random_load_pram;
       input[10:0] ran_addr;
       input[11:0]  ran_data;
       begin
         test_top.pram1.mem[ran_addr] = ran_data;
       end
     endtask


 /* initial block to dump the signals of the design. */

    initial
      begin
        $dumpvars;
        $dumpfile("risc8.dump");
      end

endmodule  
