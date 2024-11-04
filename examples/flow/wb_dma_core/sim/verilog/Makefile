all: clean comp run 


clean : 
	\rm -rf simv* csrc* *.log
comp: 
	vcs -l comp.log ../../rtl/verilog/wb_dma_ch_pri_enc.v ../../rtl/verilog/wb_dma_ch_arb.v \
../../rtl/verilog/wb_dma_pri_enc_sub.v ../../rtl/verilog/wb_dma_ch_sel.v ../../rtl/verilog/wb_dma_top.v \
../../rtl/verilog/wb_dma_ch_rf.v ../../rtl/verilog/wb_dma_rf.v ../../rtl/verilog/wb_dma_wb_if.v \
../../rtl/verilog/wb_dma_wb_mast.v ../../rtl/verilog/wb_dma_wb_slv.v ../../rtl/verilog/wb_dma_de.v \
../../rtl/verilog/wb_dma_inc30r.v ../../bench/verilog/verfiles/test_bench_top_ver.v \
../../bench/verilog/verfiles/wb_slv_model_ver.v ../../bench/verilog/verfiles/wb_mast_model_ver.v \
+incdir+../../rtl/verilog+../../bench/verilog/verfiles


run: 
	simv -l run.log
	
