set_fml_appmode FPV

set LEN_WIDTH 3
set DATA_WIDTH 64
set DATA_INTEG 0
set SPLIT_MODE 0

set ENV_DIR ..
set RTL_DIR ${ENV_DIR}/design
set SVA_DIR ${ENV_DIR}/sva

# Options:
set design ctrl

set vcs "
 +define+DATA_INTEG=${DATA_INTEG}
  +define+SPLIT_MODE=${SPLIT_MODE}
  -pvalue+LEN_WIDTH=${LEN_WIDTH}
  -pvalue+DATA_WIDTH=${DATA_WIDTH}
  ${RTL_DIR}/ctrl.sv
  ${SVA_DIR}/ctrl_checker.sv
  ${SVA_DIR}/bind_ctrl_checker.sv
"
read_file -sva -top $design -format sverilog -vcs "$vcs"

create_clock CLK -period 100
create_reset RESETn -low

sim_run
sim_save_reset
