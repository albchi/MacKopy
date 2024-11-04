#!/bin/csh -f

vcs -o simv_ntb_sv_mem_sva -Mdir=csrc_ntb_sv_mem_sva -ntb -ntb_define NTB -ntb_define SYSVERILOG_CONVERSION -ntb_opts compat +define+BADRI+NTB+INLINE_SVA -f octopus_bench.sv.mem.sva.f -l comp_sva.log ../tb/VERA/basic.vr -assert enable_diag


