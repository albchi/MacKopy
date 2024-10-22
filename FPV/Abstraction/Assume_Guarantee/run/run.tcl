set FIFODEPTH 8
set FIFOWIDTH 32
set SVA_DIR ../sva
set RTL_DIR ../design

set_fml_appmode FPV

set design fifo_ctrl
set vcs " \
  +define+FIFODEPTH=${FIFODEPTH} \
  +define+FIFOWIDTH=${FIFOWIDTH} \
  ${RTL_DIR}/fifo_ctrl.sv \
  ${SVA_DIR}/scoreboard.sv \
  ${SVA_DIR}/fifo_ctrl_checker.sv \
  ${SVA_DIR}/bind_fifo_ctrl_checker.sv \
  -assert svaext \
 "
read_file -sva -format sverilog -top $design -vcs "$vcs"

create_clock clk -period 100

create_reset resetn -low

sim_run -stable

sim_save_reset