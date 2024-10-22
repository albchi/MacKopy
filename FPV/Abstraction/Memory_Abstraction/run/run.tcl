set_fml_appmode FPV

read_file -sva -format sverilog -top tb_alu -vcs {-sverilog ../design/alu.sv ../sva/tb_alu.sv}

create_clock clk -period 100
set_change_at random_start -clock clk
set_change_at random_addr -clock clk
set_fml_var fml_witness_on true

create_reset rst_n -low
sim_run 1
sim_save_reset

set_fml_var fml_max_time 15M

check_fv
