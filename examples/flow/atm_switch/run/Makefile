
all: clean comp_ntb_sv_mem_ova run_ntb_sv_mem_ova comp_ntb_sv_mem_sva run_ntb_sv_mem_sva

comp_ntb_sv_mem_ova:
	vcs -o simv_ntb_sv_mem_ova -Mdir=csrc_ntb_sv_mem_ova -ntb -ntb_define NTB -ntb_define SYSVERILOG_CONVERSION -ntb_opts compat +define+BADRI+NTB -f octopus_bench.sv.mem.ova.f ../tb/VERA/basic.vr -l comp_ova.log   -ova -ova_report


run_ntb_sv_mem_ova:
	        ./simv_ntb_sv_mem_ova -l run_ova.log -ova_report ova.report -ova_max_fail 10 -ova_success -ova_max_success 10



comp_ntb_sv_mem_sva:
	vcs -o simv_ntb_sv_mem_sva -Mdir=csrc_ntb_sv_mem_sva -ntb -ntb_define NTB -ntb_define SYSVERILOG_CONVERSION -ntb_opts compat +define+BADRI+NTB+INLINE_SVA -f octopus_bench.sv.mem.sva.f -l comp_sva.log ../tb/VERA/basic.vr -assert enable_diag

run_ntb_sv_mem_sva:
	./simv_ntb_sv_mem_sva -l run_sva.log  -assert_report sva.report

	
clean:
	\rm -rf csrc* simv* *.log  *.report
