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
// SV-AMS Versions
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef SV_AMS_VERSION__SV
`define SV_AMS_VERSION__SV

class sv_ams_version;
   extern function int major();
   extern function int minor();
   extern function int patch();
   extern function string vendor();
   extern function string name();
   extern function void display(string prefix = "");
   extern function string psdisplay(string prefix = "");
endclass: sv_ams_version

// protect
function int sv_ams_version::major();
   major = 0;
endfunction: major

function int sv_ams_version::minor();
   minor = 1;
endfunction: minor

function int sv_ams_version::patch();
   patch = 0;
endfunction: patch


function string sv_ams_version::vendor();
   vendor = "Synopsys";
endfunction: vendor

function string sv_ams_version::name();
    return "SV-AMS";
endfunction

function void sv_ams_version::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function string sv_ams_version::psdisplay(string prefix = "");
   $sformat(psdisplay, "%s %s Version %0d.%0d.%0d (%s)",
            prefix, this.name(), this.major(), this.minor(), this.patch(), this.vendor());
endfunction: psdisplay
// endprotect

`endif // RVM_LP_VERSION__SV
