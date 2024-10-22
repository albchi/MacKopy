
if { ![info exists LEN_WIDTH ] } {
  set LEN_WIDTH 3
}
if { ![info exists DATA_WIDTH ] } {
  set DATA_WIDTH 64
}
if { ![info exists DATA_INTEG ] } {
  set DATA_INTEG 0
}
if { ![info exists SPLIT_MODE ] } {
  set SPLIT_MODE 0
}
if { ![info exists WORKERS ] } {
  set WORKERS 4
}

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

# Enable all Formal Debug Modes
set_fml_appmode FPV

# Enable Witness Trace Generation
set_fml_var fml_witness_on true

read_file -sva -top $design -format sverilog -vcs "$vcs"

create_clock CLK -period 100
create_reset RESETn -low

sim_run
sim_save_reset

if { ${WORKERS} > 4 } {
  set_grid_usage -type rsh=${WORKERS}
}

check_fv

