set ASSUME 1
set GUARANTEE 0
set FIFODEPTH 8
set FIFOWIDTH 32
set SVA_DIR ../sva
set RTL_DIR ../design

# Options:
set design fifo_ctrl
if {$ASSUME==1} {
   set vcs " \
     +define+FIFODEPTH=${FIFODEPTH} \
     +define+FIFOWIDTH=${FIFOWIDTH} \
     ${RTL_DIR}/fifo_ctrl.sv \
     ${SVA_DIR}/scoreboard.sv \
     ${SVA_DIR}/fifo_ctrl_checker.sv \
     ${SVA_DIR}/bind_fifo_ctrl_checker.sv \
     ${SVA_DIR}/fifo_abs.sv \
     ${SVA_DIR}/bind_fifo_abs.sv \
     -assert svaext \
   "
} elseif {$GUARANTEE==1} {
   set vcs " \
     +define+FIFODEPTH=${FIFODEPTH} \
     +define+FIFOWIDTH=${FIFOWIDTH} \
     ${RTL_DIR}/fifo_ctrl.sv \
     ${SVA_DIR}/fifo_abs.sv \
     ${SVA_DIR}/bind_fifo_abs.sv \
     -assert svaext \
   "
} else {
   set vcs " \
     +define+FIFODEPTH=${FIFODEPTH} \
     +define+FIFOWIDTH=${FIFOWIDTH} \
     ${RTL_DIR}/fifo_ctrl.sv \
     ${SVA_DIR}/scoreboard.sv \
     ${SVA_DIR}/fifo_ctrl_checker.sv \
     ${SVA_DIR}/bind_fifo_ctrl_checker.sv \
     -assert svaext \
   "
}
# Enable all Formal Debug Modes
set_fml_appmode FPV

# Enable Witness Trace Generation
set_fml_var fml_witness_on true

# Enable Coverage Trace Generation
#set_fml_var fml_cov_gen_trace on

read_file -sva -top $design -format sverilog -vcs "$vcs"

create_clock clk -period 100

create_reset resetn -low

sim_run -stable

if {$ASSUME==1} {
   sim_set_state wptr -apply 'x
   sim_set_state rptr -apply 'x
}
sim_save_reset

if {$ASSUME==1} {
   snip_driver fifo_full
   fvassume *fa_wr_rd_ptr_eq_aftr_rst*
   fvassume *fa_fifo_not_full_if_empty*
   fvassume *fa_wr_rd_ptr_eq_and_fifo_not_empty_imp_fifo_full*
   fvassume *fa_fifo_full_and_no_pop_imp_fifo_full*
   fvassume *fa_fifo_pop_and_no_push_imp_fifo_not_full*
}


