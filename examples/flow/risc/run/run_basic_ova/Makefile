
all:	clean comp run
clean:
	\rm -rf simv* csrc* *.log  *dump *vpd vc_hdrs.h

comp:
	vcs -l comp.log  -Mupdate -ntb -f risc8_ova.files -debug_access+nomemcbk -debug_region=cell+encrypt  ../../directc/alu.c ../../directc/decoder.c -ova_enable_diag +incdir+../../ova/

run:
	./simv -ova_report risc8.ova.log  
