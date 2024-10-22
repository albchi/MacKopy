set_fml_appmode FPV

# blackbox memory in design
set_blackbox -cells {dut.mem}

# Another way of doing this
#snip_driver {dut.mem_out}
#fvassume -expr {dut.mem_out==dut.abs_mem.mem_out}

read_file -sva -format sverilog -top tb_alu -vcs {-sverilog ../design/alu.sv ../sva/tb_alu.sv ../sva/abs_memory_model.sv}

create_clock clk -period 100
set_change_at random_start -clock clk
set_change_at random_addr -clock clk
set_fml_var fml_witness_on true

create_reset rst_n -low
sim_run 1
sim_save_reset

set_fml_var fml_max_time 15M

check_fv
