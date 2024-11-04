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
// Description : SV Real Base class
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef _SV_AMS_REAL_SV
`define _SV_AMS_REAL_SV
`ifndef SV_AMS_REAL_DEF_ACCURACY
`define SV_AMS_REAL_DEF_ACCURACY 1.0E3
`endif

`ifdef UVM_POST_VERSION_1_1
`ifdef UVM_OBJECT_DO_NOT_NEED_CONSTRUCTOR
`define UVM_SV_REAL_COMPAT_MODE
`endif
`else
`define UVM_SV_REAL_COMPAT_MODE
`endif
  
////////////////////////////////////////////////////////////
// Class: sv_ams_real
//   This class provides easy conversion from real to integer
//   and integer to real. Using this conversion, it becomes possible
//   to randomize a real and perfom functional coverage of real
//
class sv_ams_real extends uvm_sequence_item;
  rand int i;
  protected real r;
  protected real acc;

  `uvm_object_utils_begin(sv_ams_real)
    `uvm_field_int(i, UVM_ALL_ON)
    `uvm_field_real(r, UVM_ALL_ON)
    `uvm_field_real(acc, UVM_ALL_ON)
  `uvm_object_utils_end
    
  // Function: new
  //
  // The <new> function constructs <sv_ams_real> objects.
  //
  // Arguments:
  // - *r* defines the real value
  // - *acc* determines the internal accuracy used for converting real to 
  //    integer in the underlying <sv_ams_real> objects. 
  // - *name* defines the object instance name
  // - Handle to *parent* allows <sv_ams_real> object to recorded
`ifdef UVM_SV_REAL_COMPAT_MODE
  function new(real r=0.0, 
               real acc=`SV_AMS_REAL_DEF_ACCURACY, 
               string name="");
`else
  function new(string name = "",
               real r=0.0, 
               real acc=`SV_AMS_REAL_DEF_ACCURACY);
`endif
    super.new(name);
    this.r = r;
    this.acc = acc;
    this.update_int();
  endfunction


  // Function: set_real
  //   This function sets <sv_ams_real> object real value.
  //
  // Arguments:
  // - *r* defines the real value
  virtual function void set_real(real r);
    this.r = r;
    this.update_int();
  endfunction

  function void update_real();
    this.r = this.i / this.acc;
  endfunction

  function void update_int();
    this.i = this.r * this.acc;
  endfunction

  // Function: get_real
  //   This function returns the <sv_ams_real> object real value.
  virtual function real get_real();
    return this.r;
  endfunction

  // Function: get_int
  //   This function returns the <sv_ams_real> object integer value.
  virtual function int get_int();
    return this.i;
  endfunction

  // Function: urandom
  //   This function randomize a <sv_ams_real> object.
  //   The random distribution is based upon *min*, *max* values
  //   This function returns the random value.
  virtual function real urandom(real min, real max);
    if(max<=min)
      `uvm_error(get_name(), $psprintf("Argument max=%f is less than min=%f", max, min)) 
    else begin
      int mi, ma;
      mi = min * this.acc;
      ma = max * this.acc;
      this.i = ($urandom() % (ma-mi)) + mi;
      this.update_real();
      return this.r;
    end
  endfunction

  // Function: cmp
  //   This function compares *a* and *b* reals with a given *tolerance* (1% by default).
  //
  //   It returns 1 if these reals are equal, 0 otherwise.   
  //   if *b* == 0.0, it compares *a* vs. *tolerance*
  static function bit cmp(real a, real b, real tolerance=1.0E-2);
    real t;

    if(b==0.0)
      t = a;
    else
      t = (a-b)/b;

    if (fabs(t) > tolerance)
      return 0;
    else
      return 1;
  endfunction
    
  function void post_randomize();
    this.update_real();
  endfunction
    
endclass: sv_ams_real
`endif
  
