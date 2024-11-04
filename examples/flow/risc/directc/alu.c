/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

/*########################################################################
#									 #
#		C implementation of the ALU Logic			 #
#	It takes two oprand from the CPU and a carry in and do the 	 #
#	logical operation based on the type of the operation and 	 #
#	result in the output with carry out and zero flag out		 #
#									 #
########################################################################*/

#include <stdio.h>
#include <math.h>

enum ALUOP { ADD,AND,OR,XOR,COM,ROR,ROL,SWAP,SUB };

int alu_dir (int a, int b, int OpCode,int c_in, int *c_out,  int *z_out)

{
    int OUT ;

     switch ( OpCode )
     {
         case  ADD : {
                       OUT = (0x000000ff & a) + (0x000000ff & b );
                       if ( (a + b ) > 0xff)
                        *c_out = 1;
                       else
                        *c_out = 0; 
                       break;
                        
                     }
         case  AND : {
                       OUT = a & b;
                       *c_out = 0;
                       break;
                     }

         case  OR  : {
                       OUT  = a | b;
                       *c_out = 0;
                       break;
                     }
         case  XOR  :{
                       OUT  = a ^ b;
                       *c_out = 0;
                       break;
                     }
         case  COM  :{
                       OUT  = ~a ;
                       *c_out = 0;
                       break;
                     }
         case  ROR  :{
                       OUT  =  ((a & 0xff) >> 1) | ((c_in & 0x01) << 7) ;
                       *c_out = (a & 0x01);
                       break;
                     }
         case  ROL  :{
                       OUT =  ((a & 0x07f) << 1) | (c_in & 0x01) ;
                       *c_out = (a & 0xff) >> 7;
                       break;
                     }
         case SWAP  :{
                       OUT =  ((a & 0x0f) << 4) | ((a & 0xff) >> 4) ;
                       *c_out = 0;
                       break;
                     }
         case SUB   :{
                       OUT = (a & 0xff) - (b & 0xff);
                       /*printf(" OUT = %d \n", OUT);*/
                         *c_out =abs((~(OUT >>8 & 0x1)) & 0x1);
                       break;
                     }

     }

     if ( (OUT & 0xff) == 0 )
         *z_out = 1;
      else 
         *z_out = 0;

     /* printf(" Result : %x  ,carry : %d ", (OUT & 0xff),*c_out); */

    return (0xff & OUT);
}

