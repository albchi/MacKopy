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
#		C implementation of the DECODER Logic			 #
#	It takes the Instuction, decodes it  and returns the type of	 #
#	operation (ALU_OP) which CPU executes, desination for storing 	 #
#	the executed output and the MNEMONIC string. 			 #
#								         #
########################################################################*/	

#include <stdio.h>

/* INSTUCTION TYPES   */
enum INST_TYPE { BYTE,BIT,CONT,LIT };

/* CPU Operation Types */
enum ALUOP { ADD,AND,OR,XOR,COM,ROR,ROL,SWAP,SUB };


int decode_instruction (int InSt, int *dist, char **mnemonic )
{
     int byte_t, bit_11_to_6,bit_9_8;
     enum INST_TYPE  type;
     enum ALUOP Operation;

/*
      InSt[11:10] 00 -> Byte oriented insturctions
      InSt[11:10] 01 -> Bit oriented insturctions
      InSt[11:10] 10 -> Control instructions
      InSt[11:10] 11 -> Literal instructions

      dist = 0  destination for W 
      dist = 1  destination for F
*/


     if (InSt == 0)
      {   Operation = ADD; /* NOP */
          *dist = 0;
          *mnemonic = "NOP";
      }

     else
     switch ( type = ((InSt & 0xfff) >> 10) ) /* check for the type of*/ 
                                              /* instruction 11:10*/
     {
        case BYTE:
                 {
                    switch (byte_t = (InSt & 0x00000fff) ) /* 12 bit instruction*/
                    {

                       case  0x2 :{
                                   Operation = OR;    /* OPTION k*/
                                   *dist = 1;
                                   *mnemonic = "OPTION";
                                   break;
                                  }

                       case  0x3 :{
                                   Operation = ADD;    /* SLEEP */
                                   *dist = 0;
                                   *mnemonic = "SLEEP";
                                   break;
                                  }

                       case  0x4 :{
                                   Operation = ADD;    /* CLRWDT */
                                   *dist = 0;
                                   *mnemonic = "CLRWDT";
                                   break;
                                  }

                       default :
                               {
                                  if ( byte_t <= 0x7 )
                                  {

                                     Operation = OR; /* TRIS 5,6,7*/
                                     *dist = 0;
                                     *mnemonic = "TRIS";
                                     break;
                                  }

                                  else
                                  {
                                    if( ((InSt  & 0x20) >> 5)  ) /* check 5 bit */
                                                                 /* for d field */
                                      *dist = 1;
                                    else
                                      *dist = 0;

                                    /* bit 11:6 specific to byte oriented 
                                       instructions */

                                    switch ( bit_11_to_6 = ((InSt & 0xfff) >> 6) )
                                    {

                                     case 0x07   :{
                                                   Operation = ADD;   /* ADDWF */
                                                  Operation = ADD;    /* ADDWF */
                                                   *mnemonic = "ADDWF";
                                                   break;
                                                  }
                                     case 0x05   :{
                                                   Operation = AND;   /* ANDWF */
                                                   *mnemonic = "ANDWF";
                                                   break;
                                                  }
                                     case 0x01   :{
                                                    if ((InSt >> 5) & 0x1)
                                                    {
                                                       Operation = XOR;  /* CLRF */
                                                       *mnemonic = "CLRF";
                                                    }
                                                    else
                                                    {
                                                       Operation = XOR;  /* CLRW */
                                                       *mnemonic = "CLRW";
                                                    }
                                                    break;
                                                  }
                                     case 0x09   :{
                                                    Operation = COM;  /* COMF */
                                                    *mnemonic = "COMF";
                                                    break;
                                                  }
                                     case 0x03   :{
                                                    Operation = SUB;  /* DECF */
                                                    *mnemonic = "DECF";
                                                    break;
                                                  }
                                     case 0x0B   :{
                                                    Operation = SUB;  /* DECFSZ */
                                                    *mnemonic = "DECFSZ";
                                                    break;
                                                  }
                                     case 0x0A   :{
                                                    Operation = ADD;  /* INCF */
                                                    *mnemonic = "INCF";
                                                    break;
                                                  }
                                     case 0x0F   :{
                                                    Operation = ADD;  /* INCFSZ */
                                                    *mnemonic = "INCFSZ";
                                                    break;
                                                 }
                                     case 0x04   :{
                                                    Operation = OR ;  /* IORWF */
                                                    *mnemonic = "IORWF";
                                                    break;
                                                  }
                                     case 0x08   :{
                                                    Operation = OR ;  /* MOVF */
                                                    *mnemonic = "MOVF";
                                                    break;
                                                  }
                                     case 0x00   : {
                                                    if ((InSt >> 5) & 0x1)
                                                    {  Operation = OR;  /* MOVWF */
                                                       *mnemonic = "MOVWF";
                                                    }
                                                    else
                                                    {   Operation = 0;  /* NOP */
                                                        *mnemonic = "Unknown";
                                                    }
                                                    break;
                                                   }
                                     case 0x0D   :{
                                                    Operation = ROL ;  /* RLF */
                                                    *mnemonic = "RLF";
                                                    if((InSt >> 5) & 0x1) {
                                                      *dist = 1;
                                                    } else {
                                                      *dist = 0;
                                                    }                                                 
                                                    break;
                                                  }
                                     case 0x0C   :{
                                                    Operation = ROR;   /* RRF */
                                                    *mnemonic = "RRF";
                                                    break;
                                                  }
                                     case 0x02   :{
                                                    Operation = SUB;   /* SUBWF */
                                                    *mnemonic = "SUBWF";
                                                    break;
                                                  }
                                     case 0x0E   :{ Operation = SWAP;  /* SWAPF */
                                                    *mnemonic = "SWAPF";
                                                    break;
                                                  }
                                     case 0x06   :{ Operation = XOR;   /* XORWF */
                                                    *mnemonic = "XORWF";
                                                    break;
                                                  }

                                     default     :{
                                                    *mnemonic = "UnKnown";
                                                    Operation = 0;
                                                    break;
                                                  }

                                    } /* end switch */


                                  }

                               }  /* end default */
                    }
                  break;
                 }
        case BIT : {  /* BIT Oriented ref file operations */
                     if((bit_9_8 = ((InSt & 0x03ff) >> 8)) == 0)
                     {
                        Operation = AND;           /* BCF */
                        *mnemonic = "BCF";
                        *dist = 1;

                     }
                     else if( bit_9_8 == 1 )
                     {
                        Operation = OR;           /* BSF */
                        *mnemonic = "BSF";
                        *dist = 1;

                     }
                     else if( bit_9_8 == 2 )
                     {
                        Operation = AND;           /* BTFSC */
                        *mnemonic = "BTFSC";
                        *dist = 0;

                     }
                     else if( bit_9_8 == 3 )
                     {
                        Operation = AND;           /* BTFSS */
                        *mnemonic = "BTFSS";
                        *dist = 0;

                     }

                     break;
                   }



        case CONT : {  /* Control reg files operations */

                     if((bit_9_8 = ((InSt & 0x03ff) >> 8)) == 0)
                     {  Operation = OR;             /* RETLW */
                        *mnemonic = "RETLW";
                        *dist = 0;
                     }
                     else if( bit_9_8 == 1 )
                     {  Operation = OR;            /* CALL */
                        *mnemonic = "CALL";
                        *dist = 0;
                     }
                     else if( (bit_9_8 >> 1)  == 1 )
                     {  Operation = OR;             /* GOTO */
                        *mnemonic = "GOTO";
                        *dist = 0;
                     }
                     break;
                    }

        case LIT  : {  /* Literal operations */

                     if((bit_9_8 = ((InSt & 0x03ff) >> 8)) == 0)
                     {
                        Operation = OR;            /* MOVLW */
                        *mnemonic = "MOVLW";
                        *dist = 0;
                     }
                     else if( bit_9_8 == 1 )
                     {   Operation = OR;            /* IORLW */
                        *mnemonic = "IORLW";
                        *dist = 0;
                     }
                     else if( bit_9_8 == 2 )
                     {  Operation = AND;           /* ANDLW */
                        *mnemonic = "ANDLW";
                        *dist = 0;
                     }
                     else if( bit_9_8 == 3 )
                     {  Operation = XOR;           /* XORLW */
                        *mnemonic = "XORLW";
                        *dist = 0;
                     }
                     break;
                    }
      }  /* end of main switch */

/*     printf("  MNEMONIC  : %s , dest : %d , Operation : %d \n", 
                 *mnemonic,*dist,Operation); */

 return Operation;

}

