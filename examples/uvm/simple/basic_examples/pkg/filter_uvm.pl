#!/usr/bin/perl

open (FULLLOG, "+>full.log");
while(<>) {
    printf (FULLLOG $_);
      $print=1;
  ## Fix line count in uvm code
  $_ =~ s/uvm_(.*).svh(.*)/uvm_$1.svh /;
  ## Fix ID count in uvm objects
  $_ =~ s/@([0-9]+)/@(_ID_)/gi;
 # $_ =~ s/@ ([0-9]+)/@ (_ID_)/gi;
  #$_ =~ s/@ \(_ID_\)[a-zA-Z0-9]+/@ (_ID_)/gi;
  #$_ =~ s/=  [a-zA-Z0-9]+/@ (_ID_) _VAL_ /gi;
  $_ =~ s/@ \(_ID_\)[a-zA-Z0-9]+ \= .*/@ (_ID_) = _VAL_/gi;
 # $_ =~ s/=  [a-zA-Z0-9]+/@ (_ID_) _VAL_ /gi;
  
  if($_ =~ /Tool: Chronologic Simulation VCS Release/ ||
     $_ =~ /UVM_INFO :\s*([0-9]+)/ ||
     $_ =~ /\[STOP_REQ\]/ ||
     $_ =~ /UVM_INFO __VCS_HOME__\/etc\/uvm/ ||
     $_ =~ /UVM_INFO (.*)\/etc\/uvm/ ||
     $_ =~ /^--------/ ||
     $_ =~ /^UVM-/ ||
     $_ =~ /\(C\)/ ) {
    $print=0;
}
  if($print) {
      print; $print = 0;
  }

}
