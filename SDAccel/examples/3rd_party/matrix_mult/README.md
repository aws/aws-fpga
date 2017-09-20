# Third party matrix multiply OpcnCL example.
## Compiling and running.
* The steps to compile and run are the same as those used for the SDAccel examples with the exception that the host program would need the -hw=&lt;mode> switch when running in emulation mode.


* For the complete guide on compiling and running the SDAccel examples, see [this](../../../README.md).

* To run in software emulation mode, use the following commands.
 ```
make clean
source $XILINX_SDX/settings64.sh
make TARGETS=sw_emu DEVICES=$AWS_PLATFORM all
./main -hw=sw_emu
```

* To run in hardware emulation mode, use the following commands.
 ```
make clean
source $XILINX_SDX/settings64.sh
make TARGETS=hw_emu DEVICES=$AWS_PLATFORM all
./main -hw=hw_emu
```

* To run on an F1 instance, use the following commands.
 ```
make clean
source $XILINX_SDX/settings64.sh
make TARGETS=hw DEVICES=$AWS_PLATFORM all
./main
```

* For more information on running this example on an F1 instance, see [this](../../../README.md#runonf1).