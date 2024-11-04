#!/bin/csh -f


vcs -o simv_ntb_sv_mem_ova -Mdir=csrc_ntb_sv_mem_ova -ntb -ntb_define NTB -ntb_define SYSVERILOG_CONVERSION -ntb_opts compat +define+BADRI+NTB -f octopus_bench.sv.mem.ova.f ../tb/VERA/basic.vr -l comp_ova.log   -ova -ova_report

