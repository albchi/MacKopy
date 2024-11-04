//-----------------------------------------------------------------------------
// This confidential and proprietary software may be used only as authorized
// by a licensing agreement from Synopsys Inc. In the event of publication,
// the following notice is applicable:
//
// (C) COPYRIGHT 2013 SYNOPSYS INC.  ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------------
//
// Description : AMS Checkers
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef _SV_AMS_CHECKERS_SV_
`define _SV_AMS_CHECKERS_SV_

////////////////////////////////////////////////////////////
// Class: sv_ams_generic_types
//   This class defines a generic SV types
//

class sv_ams_generic_types;
   // Enum: mode_e
  // This enumerated type defines available sychronization schemes
  typedef enum {
                SYNCHRONOUS,
                ASYNCHRONOUS_REAL,
                ASYNCHRONOUS_SPICE,
                ASYNCHRONOUS_VAMS
                } mode_e;

  // Enum: type_e
  // This enumerated type defines available checkers
  typedef enum {
                THRESHOLD,
                WINDOW,
                STABLE,
                FRAME,
                SLOPE
                } type_e;
endclass

////////////////////////////////////////////////////////////
// Class: sv_ams_generic_checker
//   This class defines a generic SV checker that should be derived
//   for verifying a given property.
//  The <sv_ams_generic_checker> class allows the checker to become
//  controllable and attached to an <ams_src_if> interface, which
//  can monitor analog signal synchronously or asynchronously.
//
//    It is *virtual* and should be *extended*.

virtual class sv_ams_generic_checker#(sv_ams_generic_types::mode_e MODE = sv_ams_generic_types::SYNCHRONOUS) extends uvm_driver#(sv_ams_real);
  

  protected virtual ams_src_if aif;
  bit started;

  // Function: new
  //
  // The <new> function is used to construct <sv_ams_generic_checker> object derivatives.
  //
  // Arguments:
  //  - *name* defines the transactor instance name
  //  - *parent* defines the transactor parent
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // Function: build_phase
  // Assigns the virtual interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_resource_db#(virtual ams_src_if)::read_by_name(get_full_name(), "uvm_ams_src_if", aif)) 
      `uvm_error("TESTERROR", $sformatf("%s %s", "no bus interface uvm_ams_src_if available at path=", get_full_name()));

    this.aif = aif;
  endfunction 
 
  // Function: dump_msg
  //  The <dump_msg> function dumps messages with a given severity level.
  //  It ignores the message if the severity is below the sv severity.
  //
  // Arguments:
  //  - *msg* contains the message to be issued
  function void dump_msg(string msg);
    `uvm_info(get_full_name(), msg, UVM_LOW);
  endfunction

  // Task: sample
  //   This task should be overriden. It implement the checker sampling scheme
  //   i.e. when to perform the check
  virtual protected task sample();
      if(MODE==sv_ams_generic_types::SYNCHRONOUS)
         @(this.aif.sck);
      else
         @(this.aif.sck.v); // TO DO, Add support for VAMS, SPICE, etc.
  endtask

  // Task: check_assert
  //   This task should be overriden. It implement the checker behavior.
  //   i.e. what to verify
  virtual protected task check_assert();
    `uvm_fatal(get_name(), $psprintf("You need to override %M"));
  endtask

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
    while(1) begin
      wait(started == 1);
      this.sample();
      this.check_assert();
    end
    join_none
  endtask

endclass

////////////////////////////////////////////////////////////
// Class: sv_ams_threshold_checker
//   This transactor checks that a signal as specified
//   in its interface doesn't rise or fall above/below a pre-defined threshold.
//   The signal direction and threshold are defined with
//   the *THR* and *DIR* parameters
//
// _Parameters_:
//  - *THR* defines the <sv_ams_threshold_checker> threshold value (in V) 
//  - *DIR* defines the <sv_ams_threshold_checker> direction value.
//    (+1: rising, -1: falling) 
class sv_ams_threshold_checker #(real THR=0.0, int DIR=1,
                                  sv_ams_generic_types::mode_e MODE=sv_ams_generic_types::SYNCHRONOUS) 
                                extends sv_ams_generic_checker#(MODE);
  local real threshold;
  local int direction;

  // Function: new
  //
  // The <new> function is used to construct <sv_ams_threshold_checker> object;
  //
  // Arguments:
  //  - *name* defines the transactor instance name
  //  - *parent* defines the transactor parent
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    this.threshold = THR;
    this.direction = DIR;
  endfunction
    
  // Function: set_params
  //
  //  The <set_params> function specifies new *threshold* and *direction* values 
  //
  // Arguments:
  //  - *threshold* defines the <sv_ams_threshold_checker> threshold value (in V) 
  //  - *direction* defines the <sv_ams_threshold_checker> direction value.
  //    (+1: rising, -1: falling) 
  function void set_params(real threshold, int direction);
    this.threshold = threshold;
    this.direction = direction;
  endfunction
    
  task check_assert();
    if(direction == +1 && aif.sck.v > threshold)
      dump_msg($psprintf("Vin=%0.3f is above Thr=%0.3f", 
                                        aif.sck.v, threshold));
    if(direction == -1 && aif.sck.v < threshold)
      dump_msg($psprintf("Vin=%0.3f is below Thr=%0.3f", aif.sck.v, threshold));
  endtask
endclass
  
////////////////////////////////////////////////////////////
// Class: sv_ams_stability_checker
//   This transactor checks that a signal as specified
//   in its interface remains equal to a reference voltage +/- tolerance. 
//   The reference and tolerance are defined with
//   *REF* and *TOL* parameters.
//
// _Parameters_:
//  - real *REF* defines the <sv_ams_stability_checker> reference value (in V) 
//  - real *TOL* defines the <sv_ams_stability_checker> tolerance (default=10%)

class sv_ams_stability_checker #(real REF=0.0, real TOL=0.1,
                                  sv_ams_generic_types::mode_e MODE=sv_ams_generic_types::SYNCHRONOUS) 
                                extends sv_ams_generic_checker#(MODE);
  local real reference;
  local real tolerance;

  // Function: new
  //
  // The <new> function is used to construct <sv_ams_threshold_checker> object;
  //
  // Arguments:
  //  - *name* defines the transactor instance name
  //  - *parent* defines the transactor parent
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    this.reference = REF;
    this.tolerance = TOL;
  endfunction
    
  // Function: set_params
  //
  //  The <set_params> function specifies new *reference* and *tolerance* values 
  //
  // Arguments:
  //  - *reference* defines the <sv_ams_threshold_checker> reference voltage (in V) 
  //  - *tolerance* defines the <sv_ams_threshold_checker> tolerance (0.1 = 10%)

  function void set_params(real reference, real tolerance);
    this.reference = reference;
    this.tolerance = tolerance;
  endfunction
    
  task check_assert();
    if((aif.sck.v < ((1-tolerance)*reference)) || (aif.sck.v > ((1+tolerance)*reference)))
      dump_msg($psprintf("Vin=%0.3f is out of Vref=%0.3f +/- %0.3f percent", 
                                        aif.sck.v, reference, 100* tolerance));
  endtask
endclass
  
////////////////////////////////////////////////////////////
// Class: sv_ams_slew_checker
//   This transactor checks that a signal as specified
//   in its interface steadily rises or falls above or below a pre-defined slew rate.
//   The slew rate and above/below checks are defined with
//   the *SLEW* and *IN_OUT* parameters
//
// _Parameters_:
//  - *SLEW* defines the <sv_ams_threshold_checker> slew rate (in V/ns) 
//  - *IN_OUT* defines the <sv_ams_threshold_checker> mode. 
// 	0: Indicates that slew rate is always *below* *SLEW*
// 	1: Indicates that slew rate is always *above* *SLEW*

class sv_ams_slew_checker #(real SLEW=0.1, bit IN_OUT=1,
                                  sv_ams_generic_types::mode_e MODE=sv_ams_generic_types::SYNCHRONOUS) 
                                 extends sv_ams_generic_checker#(MODE);

  local real slew;
  local real vref;
  local bit in_out;

  // Function: new
  //
  // The <new> function is used to construct <sv_ams_threshold_checker> object;
  //
  // Arguments:
  //  - *name* defines the transactor instance name
  //  - *parent* defines the transactor parent
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    this.slew = SLEW;
    this.in_out = IN_OUT;
    this.vref = 0.0;
  endfunction
    
  // Function: set_params
  //
  //  The <set_params> function specifies new *slew* and *in_out* values 
  //
  // Arguments:
  //  - *slew* defines the <sv_ams_threshold_checker> slew rate (in V) 
  //  - *in_out* defines the <sv_ams_threshold_checker> comparison mode.
  // 	0: Indicates that slew rate is *below* *SLEW*
  // 	1: Indicates that slew rate is *above* *SLEW*

  function void set_params(real slew, bit in_out);
    this.slew = slew;
    this.in_out = in_out;
  endfunction
    
  task check_assert();
    if(in_out == 0 && fabs(aif.sck.v-vref) < slew)
      dump_msg($psprintf("Vin=%0.3f slew rate is below slew=%0.3f. It is expected to remain above this value.", 
                                        aif.sck.v, slew));
    if(in_out == 1 && fabs(aif.sck.v-vref) > slew)
      dump_msg($psprintf("Vin=%0.3f slew rate is above slew=%0.3f. It is expected to remain below this value.", 
                                        aif.sck.v, slew));
    vref <= aif.sck.v;
  endtask
endclass
  
////////////////////////////////////////////////////////////
// Class: sv_ams_frequency_checker
//   This transactor checks that a signal frequency as specified
//   in its interface remains stable with a given tolerance.
//   The signal voltage min/max, frequency and tolerance are defined with
//   the *VMIN*, *VMAX, *FREQ* and *TOL* parameters
//   The *TP* parameter specifies the enclosing module time precision
//   (as specified with `timescale prec/unit)
//
// _Parameters_:
//  - *VMIN* defines the <sv_ams_frequency_checker> min voltage (in V) 
//  - *VMAX* defines the <sv_ams_frequency_checker> max voltage (in V) 
//  - *FREQ* defines the <sv_ams_frequency_checker> expected frequency (in Hz) 
//  - *TP* defines the <sv_ams_frequency_checker> enclosing module time precision
//  - *TOL* defines the <sv_ams_threshold_checker> frequency tolerance (0.01=1%)

class sv_ams_frequency_checker #(real VMIN=0.0, 
                                  real VMAX=1.0, 
                                  real FREQ=1.0E6, 
                                  real TP=1.0E-9, 
                                  real TOL=1.0E-2)
                                extends sv_ams_generic_checker;
  local real frequency;
  local real vmin;
  local real vmax;
  local real time_precision;
  local real tolerance;

  // Function: new
  //
  // The <new> function is used to construct <sv_ams_threshold_checker> object;
  //
  // Arguments:
  //  - *name* defines the transactor instance name
  //  - *parent* defines the transactor parent
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    this.vmin = VMIN;
    this.vmax = VMAX;
    this.frequency = FREQ;
    this.time_precision = TP;
    this.tolerance = TOL;
  endfunction
    
  // Function: set_params
  //
  //  The <set_params> function specifies new 
  //   min/max voltages, frequency/tolerance and time precision.
  //
  // Arguments:
  //  - *vmin* defines the <sv_ams_frequency_checker> min voltage (in V) 
  //  - *vmax* defines the <sv_ams_frequency_checker> max voltage (in V) 
  //  - *freq* defines the <sv_ams_frequency_checker> expected frequency (in Hz) 
  //  - *time_precision* defines the <sv_ams_frequency_checker> enclosing module time precision
  //  - *tol* defines the <sv_ams_threshold_checker> frequency tolerance (0.01=1%)
  function void set_params(real vmin, real vmax, real freq, real time_precision=1.0E-9, real tol=1.0E-2);
    this.vmin = vmin;
    this.vmax = vmax;
    this.frequency = freq;
    this.time_precision = time_precision;
    this.tolerance = tol;
  endfunction
    
  task sample();
  endtask
    
  task check_assert();
    real t0,t1,act_freq;
    int i=0,j=0;
    fork
      begin: FREQMEAS
        wait (sv_ams_real::cmp(aif.sck.v,vmax,tolerance));
        wait (sv_ams_real::cmp(aif.sck.v,vmin,tolerance));
        t0=$realtime;
  
        wait (sv_ams_real::cmp(aif.sck.v,vmax,tolerance));
        wait (sv_ams_real::cmp(aif.sck.v,vmin,tolerance));
        t1=$realtime;
  
        act_freq=1/(time_precision*(t1-t0));
        disable TIMEOUT;
  
        if (!(sv_ams_real::cmp(act_freq,frequency,tolerance))) 
          dump_msg($psprintf("Expecting freq = %f - got %f with tolerance=%0.3f",
                                          frequency,act_freq,(tolerance*100)));
        else 
          dump_msg($psprintf("Measured freq = %f", frequency));
      end
  
      begin: TIMEOUT
        for (j=0;j<((5/(time_precision*frequency)));j++) #1;
        disable FREQMEAS;
        dump_msg($psprintf("%M timed out!!"));
      end
    join
  endtask
endclass

`endif
 
