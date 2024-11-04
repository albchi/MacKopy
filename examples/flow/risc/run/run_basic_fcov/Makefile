
all:	clean comp run

clean:
	\rm -rf simv* csrc* *.log  *dump *vpd vc_hdrs.h

comp:
	vcs -l  comp.log -Mupdate -ntb -f risc8_ova.files +vc ../../directc/alu.c ../../directc/decoder.c -ova_cov +incdir+../../ova/


run:
	./simv  -ova_cov  -l risc8.run.log

