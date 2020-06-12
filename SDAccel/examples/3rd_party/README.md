# Porting third party OpenCL to SDAccel
* In the interest of providing more examples for the user, we present this guide that tells how to port third party OpenCL examples to the SDAccel flow.
* In this guide, we show the changes necessary to port third party host code and kernel code for 2 different examples.
* We also show some [differences between the third party OpenCL and Xilinx SDAccel implementations](#xilinx-and-third-party-implementation-differences) that the user should be aware of.

## The file structure of the third party examples used in this guide.
 * The following shows the common file structure of the third party examples used in this guide.
```
<example_name>/README.html
<example_name>/Makefile
<example_name>/device/<example_name>.cl
<example_name>/host/src/main.cpp
common/readme.css
common/inc/AOCLUtils/scoped_ptrs.h
common/inc/AOCLUtils/aocl_utils.h
common/inc/AOCLUtils/opencl.h
common/inc/AOCLUtils/options.h
common/src/AOCLUtils/opencl.cpp
common/src/AOCLUtils/options.cpp
```
* The files in the `common` directory are the same throughout both examples.

## The third party examples used in this guide.
  * The first is the [vector_addition](https://www.altera.com/support/support-resources/design-examples/design-software/opencl/vector-addition.html) example.
  * The second is the [fft(1D)](https://www.altera.com/support/support-resources/design-examples/design-software/opencl/fft-1d.html) example.

## Changes to the host code.

 * The changes needed for the **vector_addition** host code can be found [here](vector_addition) in the file named vector_addition_main.cpp.diff.
 * The changes needed for the **fft1d** host code can be found [here](fft1d) in the file named fft1d_main.cpp.diff.
 * All the modified dependency files can be found in the [SDAccel/examples/3rd_party/common](common) directory.

## Changes to the kernel code.

* The kernel code, found in the &lt;example_name>/device directory, will most likely need modifications.
* The **vector addition** kernel does not need changes.
* The **fft1d** example needs several changes due to the differences between the third party and Xilinx implementations.
* The changes needed for the fft1d.cl file are found [here](fft1d) in the file named fft1d_fft1d.cl.diff.
* See table below regarding [implementation differences between third party and Xilinx](#xilinx-and-third-party-implementation-differences).

* The &lt;example_name>/device/twid_radix4_8.cl file will get many warnings about casting from double to float.
* The shell commands below will cast the double constant values to float.

```sh
sed 's/\([0-9]\)\( \{0,\}[,}]\)/\1f\2/g' twid_radix4_8.cl > tmp
mv tmp twid_radix4_8.cl
```
* The script above can be found [here](fft1d) named cast_float_const.sh.

## Changes to the Makefile.

* The third party Makefile can be replaced by a version that is similar to the SDAccel example Makefiles.
* For example, for the third party **vector_addition** code, the Makefile can be found [here](vector_addition).
* The **fft1d** example Makefile can be found [here](fft1d).  


## Compiling and running.
* The steps to compile and run would be the same as those used for the SDAccel examples with the exception that the host program would need the -hw=&lt;mode> switch when running in emulation mode.
* For the complete guide on compiling and running the SDAccel examples, see [this](../../README.md).

* To run in software emulation mode, use the following commands.
 ```
make clean
make TARGETS=sw_emu DEVICES=$AWS_PLATFORM all
./main -hw=sw_emu
```

* To run in hardware emulation mode, use the following commands.
 ```
make clean
make TARGETS=hw_emu DEVICES=$AWS_PLATFORM all
./main -hw=hw_emu
```

* To run on an F1 instance, use the following commands.
 ```
make clean
make TARGETS=hw DEVICES=$AWS_PLATFORM all
./main
```

* For more information on running this example on an F1 instance, see [this](../../README.md#runonf1).

## Xilinx and third party Implementation Differences
#### Host Code
| third party FPGA     | Xilinx     |
| :------------- | :------------- |
| third party's device_info* APIs | OpenCL APIs: clGetPlatformIDs or clGetPlatformIds or clGetDeviceIds |
| findPlatform("&lt;third_party>") | clGetPlatformInfo or findPlatform("Xilinx") |
| createProgramFromBinary | clCreateProgramWithBinary |
| CL_MEM_BANK_*_&lt;third_party> | XCL_MEM_DDR_BANK* |
| .aocx file | .xclbin file |
| CL_DEVICE_TYPE_ALL | CL_DEVICE_TYPE_ACCELERATOR |

#### Kernel Code
| third party FPGA | Xilinx |
| :------------- | :------------- |
| read/write_&lt;third_party>_channel | read/write_pipe_block |
| channel  keyword | pipe keyword |
| \_\_attribute__(8) | \_\_attribute__((xcl_reqd_pipe_depth(16))) |
| kernel name and kernel argument name can be the same | kernel_name and kernel arguments' name should be different |
| Implictly converting double type to float type | Explicitly converted double type to float type |
| declares and initializes an struct object together | declare an struct object and then initialize it separately |

## SUPPORT
For more information check the [SDAccel User Guides](http://www.xilinx.com/support/documentation-navigation/development-tools/software-development/sdaccel.html?resultsTablePreSelect=documenttype:SeeAll#documentation)

For questions and to get help on this project or your own projects, visit the [SDAccel Forums](https://forums.xilinx.com/t5/SDAccel/bd-p/SDx)

## REVISION HISTORY

Date    | Readme Version | Revision Description
--------|----------------|-------------------------
SEP2017 | 1.0            | Initial release
