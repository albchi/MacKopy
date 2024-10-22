# Set App mode to FPV
set_fml_appmode FPV

# Signoff Config Setup
#signoff_config -type {line branch fault_conn}
signoff_config -type all

# Set the design top in a variable
set top fifo

# Set fault injection scope
fta_init -fast_sanity -scope {fifo}

# Compile design
read_file -top $top -format sverilog -sva \
          -vcs {-f ../design/filelist.flist ./fifo_sva.sv\
          +define+LAB_PART_B}

# Define clock
create_clock clk -period 100 -initial 0

# Define reset active level - here it is active low
create_reset resetn -low

# Run simulation phase for reset
sim_run -stable 

# Save reset state
sim_save_reset

# Set max proof time - wall clock time
set_fml_var fml_max_time 5M

# Set GRID usage for parallel proofs
#set_grid_usage -type rsh=30

# FPV - Property Verification
check_fv -block

