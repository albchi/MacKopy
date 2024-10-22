set ENV_DIR ..
set RTL_DIR $ENV_DIR/design
set SVA_DIR $ENV_DIR/sva

# Options:
set design packet_ctrl
set vcs "
   ${RTL_DIR}/packet_ctrl.sv
   ${SVA_DIR}/packet_ctrl_checker.sv
"

# Set Formal Mode with FPV
set_fml_appmode FPV

# Enable Witness Trace Generation
set_fml_var fml_witness_on true

read_file -sva -top $design -format sverilog -vcs "$vcs"

create_clock clk -period 100

create_reset rst -sense high
sim_run -stable
sim_save_reset

#fvcover cov_pkt_sop -clock clk -expr {pkt_sop}
#fvcover cov_pkt_eop -clock clk -expr {pkt_eop}
#fvcover cov_link_fsm_stabled -clock clk -expr {link_fsm==2'b01}
#fvcover cov_link_fsm_waitack -clock clk -expr {link_fsm==2'b10}

check_fv

