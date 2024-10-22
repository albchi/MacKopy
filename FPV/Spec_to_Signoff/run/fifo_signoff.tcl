# Set App mode to FPV
set_fml_appmode FPV

# Set the design top in a variable
set top fifo

# Compile design
read_file -top $top -format sverilog -sva \
  -vcs {-f ../design/filelist.flist ../sva/fifo_sva.sv}

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
