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
// SV-AMS Source Generators
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef _SV_AMS_IF_SV
`define _SV_AMS_IF_SV

////////////////////////////////////////////////////////////
// Class: ams_src_if
//
//|	interface ams_src_if(input bit clk);
//
// The <ams_src_if> interface contains the <v> real signal
// that can be attached to an analog IP.
//
interface ams_src_if(input bit clk);
   initial 
    uvm_resource_db#(virtual ams_src_if)::set("*", "uvm_ams_src_if", interface::self());

  // real: v 
  //   Real value that can be attached to an analog IP
  real v;

  // Property: dck 
  //	Provides a clocking block with synchronous write-only access to <v>
  clocking dck @(posedge clk);
    default output #0;
    output v;
  endclocking: dck

  // Property: sck 
  //	Provides a clocking block with synchronous read-only access to <v>
  clocking sck @(posedge clk);
    default input #0;
    input v;
  endclocking: sck

  // Property: drive 
  //	Provides a modport with synchronous write-only access to <v>
  modport drive(clocking dck);

  // Property: sample 
  //	Provides a modport with synchronous read-only access to <v>
  modport sample(clocking sck);

  // Property: async_sample 
  //	Provides a modport with asynchronous read/write only access to <v>
  modport async_sample(input clk, input v);

endinterface: ams_src_if

`ifdef __UVM_AMS_SV
////////////////////////////////////////////////////////////
// Class: ams_src_if_wrapper
//
// This class wraps a <ams_src_if> virtual interface to
// an sv_object that can be replaced by factory
//
////////////////////////////////////////////////////////////
class ams_src_if_wrapper extends uvm_object;
  virtual ams_src_if aif;

  // Function: new
  // The <new> function is used to construct <ams_src_if_wrapper> objects.
  //
  // Arguments:
  // - *name* to define the wrapper name
  // - *aif* to pass a handle to the the interface object
  function new(string name, virtual ams_src_if aif);
    super.new(name);
    this.aif = aif;
  endfunction
endclass: ams_src_if_wrapper
`endif

`endif
