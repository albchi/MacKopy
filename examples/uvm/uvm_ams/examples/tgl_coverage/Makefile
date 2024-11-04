ifndef UVM_HOME
UVM = -ntb_opts uvm-1.2 +incdir+$(VCS_AMS_HOME)
else
UVM = $(UVM_HOME)/src +incdir+$(VCS_AMS_HOME)
endif

all:
	vcs +ad=ns_msv.init +cli+3 top.v -debug_access+all  -R -cm line+tgl
	urg -dir ./simv.vdb -format text
	@echo "--- See Files in UrgReport ---"

clean:
	rm -rf simv* .vlogansetup.env .vlogansetup.args .gui_support
	rm -rf csrc/ cm.log outputs/ genie.log urgReport/ opendatabase.log digital_output.vcd
	rm -rf DVEfiles/ digital_output.vcd.vpd
