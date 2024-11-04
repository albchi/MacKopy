config topcfg;
        design  ubus_tb_top;
        partition package uvm_pkg;
        partition cell dut_dummy;
        partition cell test; 
        default liblist  DEFAULT;
endconfig
