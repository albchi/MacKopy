
all:	clean comp run
clean:
	\rm -rf simv* csrc* *.log  *dump *vpd vc_hdrs.h

comp:
	vcs  -ntb -f ./risc8_ova.files -cm line+cond+fsm+tgl +vc ../../directc/alu.c ../../directc/decoder.c -l risc8.comp.log -lca 


run:
	./simv +random -cm line+cond+fsm+tgl -ova_report risc8.ova.log -l risc8.run.log

