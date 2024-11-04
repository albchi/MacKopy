all : clean comp run clean


clean :
	\rm -rf *~ core.*
	\rm -rf tli_packunpack_*.*
	\rm -rf AN.DB csrc sim* *.log DEFAULT.DB DVEfiles/ \
		*.vpd ucli* vc_hdrs.h \
		.X_dummy* .vlogan* .vcs_* .*.swp 

OPT =  -cc gcc -cpp g++ -tlm2 -cflags -DUSER_PAYLOAD -cflags -g

UVM	=	-ntb_opts uvm-1.2

VCS_OPT =  -cc gcc -cpp g++ -q -nc -cpp g++ -cc gcc -timescale=1ns/1ps -l vcs.log -cm_xmldb \
	  -sverilog -gen_obj -sysc \
	+incdir+.. \
	+incdir+${VCS_HOME}/etc/systemc/tlm/tli \
	$(UVM)


comp : 
	syscan -cc gcc -cpp g++ -tli payload.tli \
		payload.h
	syscan ${OPT} target.cpp
	syscan ${OPT} initiator.cpp
	syscan ${OPT} tli_packunpack_my_payload.cpp
	syscan ${OPT} payload_conv.cpp
	syscan ${OPT} sc_top.cpp:sc_top     
	vcs  ${VCS_OPT} top.v

run  :
	./simv +UVM_NO_RELNOTES -l run.log | grep -v 'tmp'
