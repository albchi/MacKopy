INDF    equ     H'00'   ; Magic register that uses INDIRECT register
INDF    equ     H'00'   ; Magic register that uses INDIRECT register
TIMER0  equ     H'01'   ; Timer register
STATUS  equ     H'03'   ; STATUS register F3
FSR     equ     H'04'   ; INDIRECT Pointer Register
portc   equ     H'07'   ; I/O register F7
DDSCTL  equ     H'7E'   ; DDS Control Register.
DDSSTEP equ     H'7F'   ; DDS Step Register.
STATEDEV equ    H'7D'   ;Status of device register
CARRY   equ     H'00'   ; Carry bit in STATUS register
ZERO    equ     H'02'   ; Zero bit in STATUS register
W       equ     H'00'   ; W indicator for many instruction (not the address!)
x equ H'0A'   ;our general variable

start:
           clrw
           tris    portc           ; PORTC is Output
           movwf   portc           ; PORTc <= 00
           movlw H'04'             ;w=H'04
           movwf x                 ;x=H'04
dev1:      movlw   DDSCTL          ;Write H'00 value to DDSCTL thru indirect addressing
           movwf   FSR
           movlw   H'00'
           movwf   INDF
           movlw   H'00'
           movwf   portc           ; Ouput PORTC <= 00
           movlw STATEDEV          ;Check the state value for state0
           movwf FSR
           movf INDF,0
           xorlw H'00'
           btfss STATUS,ZERO
           NOP
           goto state0_to_0
state0_to_0:
           movlw   DDSCTL          ;Write H'01 value to DDSCTL thru indirect addressing
           movwf   FSR
           movlw   H'01'
           movwf   INDF
           movlw   H'01'
           movwf   portc           ; Ouput PORTC <= 01
           movlw STATEDEV          ;Check the state value for state0 again if X=0 state will be same
           movwf FSR
           movf INDF,0
           xorlw H'00'
           btfss STATUS,ZERO
           goto state0_to_1       ;GOTO state 1
           goto dev1       ;GOTO state 0

state0_to_1:
           NOP                    ;Delays added
           movlw STATEDEV          ;Check the state value for state0 again if X=0 state will be same
           movwf FSR
           movf INDF,0
           xorlw H'01'
           btfss STATUS,ZERO
           goto dev1                  ;GOTO state 1
           goto state1_to_2       ;GOTO state 1
state1_to_2:
           NOP
           movlw   DDSCTL         ;DDSCTL=2
           movwf   FSR
           movlw   H'02'
           movwf   INDF
           movlw   H'02'           ;portc=2
           movwf   portc           ; PORTC <= 02
           movlw STATEDEV          ;Read state vaule for state2
           movwf FSR
           movf INDF,0
           xorlw H'02'
           btfss STATUS,ZERO       ;If zero goto state3 else goto dev1
           goto dev1    
           goto state2_to_3
state2_to_3:
           movlw   DDSCTL         ;DDSCTL=3
           movwf   FSR
           movlw   H'03'
           movwf   INDF
           movlw   H'03'           ;portc=3
           movwf   portc           ; PORTC <= 03
loop3:         
           movlw STATEDEV          ;Read state vaule for state3
           movwf FSR
           movf INDF,0
           xorlw H'03'
           btfss STATUS,ZERO       ;If zero goto state4 else goto state3
           goto state3_to_4     
           goto state3_to_3

state3_to_3:
           movlw   DDSCTL          ;DDSCTL=04
           movwf   FSR
           movlw   H'04'
           movwf   INDF
           movlw   H'04'
           movwf   portc           ; PORTC <= 05
           movlw STATEDEV          ;Read state vaule for state3
           movwf FSR
           movf INDF,0
           xorlw H'03'
           btfss STATUS,ZERO
           goto state3_to_4       
           goto state2_to_3
state3_to_4:
           NOP
           NOP
           movlw STATEDEV          ;Read state vaule for state4
           movwf FSR
           movf INDF,0
           xorlw H'04'
           btfss STATUS,ZERO       
           goto state3_to_3
           goto dev1
           END
