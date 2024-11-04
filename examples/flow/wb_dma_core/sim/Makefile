all: clean comp run 


clean : 
	\rm -rf simv* csrc* *.log
comp: 
	vcs -sverilog -ignore driver_checks ../rtl/sysverilog/top/*.v ../rtl/sysverilog/dma/*.v ../rtl/sysverilog/regfiles/inc_addr.v ../rtl/sysverilog/regfiles/addr_dec.v ../rtl/sysverilog/regfiles/basic_reg.v ../rtl/sysverilog/regfiles/reg_top.v ../rtl/sysverilog/regfiles/mux.v ../rtl/sysverilog/regfiles/reg_file.v ../rtl/sysverilog/chsel/intf_ch_top.v ../rtl/sysverilog/chsel/pri_arb.v ../rtl/sysverilog/chsel/pri_mux.v ../rtl/sysverilog/chsel/pri_enc.v ../rtl/sysverilog/chsel/pri_fifo.v ../rtl/sysverilog/wb/*.v ../bench/verilog/*.v +incdir+../rtl/sysverilog/regfiles/+../rtl/verilog/+../bench/verilog/++libext+.v -l comp.log

run: 
	simv -l run.log

