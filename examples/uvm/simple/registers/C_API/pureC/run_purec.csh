gcc -c -I$DIR -I.. -I../../../include/ -I../../../include/pureC -DSNPS_REG_NOP -DSNPS_REG_DEBUG main_purec.cpp
gcc -c -I. -I.. -I../../../include/ -I../../../include/pureC -DSNPS_REG_NOP -DSNPS_REG_DEBUG sys_driver.cpp
gcc -lstdc++ -o a.out main_purec.o sys_driver.o
a.out
