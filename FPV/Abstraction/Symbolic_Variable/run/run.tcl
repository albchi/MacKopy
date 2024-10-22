#Set the design top in a variable
set top fifo

# enable witness trace for property 
set_fml_var fml_witness_on true


# Compilation
# single step analyze + elaborate
read_file -top $top -format sverilog -sva -vcs {-f ../design/filelist.flist}


# define the clock
create_clock clk -period 100 -initial 0

# define the reset and active level - here it is active low
create_reset resetn -low

#Setup grid
#set_grid_usage -type RTDA=12 -control { nc run -wl -ep -r redhat x86_64 RAM/32000}

