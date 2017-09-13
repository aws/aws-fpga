# Porting third party OpenCL to SDAccel
* In the interest of providing more examples for the user, we present this guide that tells how to port third party OpenCL examples to the SDAccel flow.
* In this guide, we show the changes necessary to port third party host code and kernel code for 2 different examples.
* We also show some [differences between the third party OpenCL and Xilinx SDAccel implementations](#xilinx-and-third-party-implementation-differences) that the user should be aware of.
* There is a third example (matrix_mult, not discussed here) available at SDAccel/examples/3rd_party.

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
 * The host code *main.cpp* has dependencies found in *common/inc/AOCLUtils/{inc,src}*.
 * The *main.cpp* file and its dependencies need the following changes to work with SDAccel.

#### The following are the changes needed for the *vector_add* host code.

diff -u0 **third_party**/vector_add/host/src/main.cpp **sdaccel**/vector_add/host/src/main.cpp
```diff
--- third_party/vector_add/host/src/main.cpp       2017-05-09 22:47:50.000000000 +0000
+++ sdaccel/vector_add/host/src/main.cpp  2017-09-12 18:55:22.172000000 +0000
@@ -70,0 +71,2 @@
+std::string hwtype = "hw";
+
@@ -85,0 +88,3 @@
+  if(options.has("hw")) {
+    hwtype = options.get<std::string>("hw");
+  }
@@ -123 +128 @@
-  platform = findPlatform("Intel");
+  platform = findPlatform("Xilinx");
@@ -125 +130 @@
-    printf("ERROR: Unable to find Intel FPGA OpenCL platform.\n");
+    printf("ERROR: Unable to find Xilinx FPGA OpenCL platform.\n");
@@ -143,2 +148,4 @@
-  std::string binary_file = getBoardBinaryFile("vector_add", device[0]);
-  printf("Using AOCX: %s\n", binary_file.c_str());
+  std::string fname = "xclbin/vector_add."+ hwtype + "." + VERSION_STR;
+  printf("Looking for %s.\n",fname.c_str());
+  std::string binary_file = getBoardBinaryFile(fname.c_str(), device[0]);
+  printf("Using XCLBIN: %s\n", binary_file.c_str());

```

#### The following are the changes needed for the *fft1d* host code.

diff -r **third_party**/fft1d/host/src/main.cpp **sdaccel**/fft1d/host/src/main.cpp
```diff
--- third_party/fft1d/host/src/main.cpp    2017-05-09 22:47:43.000000000 +0000
+++ sdaccel/fft1d/host/src/main.cpp       2017-09-12 16:18:56.072000000 +0000
@@ -61,0 +62 @@
+std::string hwtype = "hw";
@@ -94,3 +94,0 @@
-  if(!init()) {
-    return false;
-  }
@@ -104,0 +103,3 @@
+  if(options.has("hw")) {
+    hwtype = options.get<std::string>("hw");
+  }
@@ -110,0 +112,4 @@
+  if(!init()) {
+    return false;
+  }
+
@@ -163 +168 @@
-  d_outData = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_BANK_2_ALTERA, sizeof(float2) * N * iterations, NULL, &status);
+  d_outData = clCreateBuffer(context, CL_MEM_READ_WRITE , sizeof(float2) * N * iterations, NULL, &status);
@@ -336 +341 @@
-  platform = findPlatform("Intel");
+  platform = findPlatform("Xilinx");
@@ -363,2 +368,4 @@
-  std::string binary_file = getBoardBinaryFile("fft1d", device);
-  printf("Using AOCX: %s\n\n", binary_file.c_str());
+  std::string fname = "xclbin/fft1d."+ hwtype + "." + VERSION_STR;
+  printf("Looking for %s.\n",fname.c_str());
+  std::string binary_file = getBoardBinaryFile(fname.c_str(), device);
+  printf("Using XCLBIN: %s\n\n", binary_file.c_str());
```

#### There are two dependency files that need the following changes.

diff -u0 **third_party**/common/src/AOCLUtils/opencl.cpp **sdaccel**/common/src/AOCLUtils/opencl.cpp
```diff
--- third_party/common/src/AOCLUtils/opencl.cpp    2016-11-23 22:32:29.000000000 +0000
+++ sdaccel/common/src/AOCLUtils/opencl.cpp       2017-09-12 19:06:23.001000000 +0000
@@ -35 +34,0 @@
-static const char *const VERSION_STR = "161";
@@ -369 +368 @@
-    printf("AOCX file '%s' does not exist.\n", binary_file_name);
+    printf("XCLBIN file '%s' does not exist.\n", binary_file_name);
@@ -446 +445 @@
-  std::string file_name = std::string(prefix) + ".aocx";
+  std::string file_name = std::string(prefix) + ".xclbin";
@@ -457 +456,3 @@
-  size_t end = device_name.find(" :");
+  size_t begin = device_name.find(":",0);
+  size_t end = device_name.find(":",begin+1);
+
@@ -459 +460 @@
-    std::string board_name(device_name, 0, end);
+    std::string board_name(device_name, begin+1, end-(begin+1));
@@ -460,0 +462,3 @@
+    end = board_name.find("-",0);
+    printf("Warning:  Defaulting to the XCLBIN file compiled in HW mode.  Try -hw=hw_emu or -hw=sw_emu if you want to run in emulation mode.\n");
+    board_name = "hw";
@@ -462 +466 @@
-    file_name = std::string(prefix) + "_" + board_name + "_" + VERSION_STR + ".aocx";
+    file_name = "xclbin/" + std::string(prefix) + "." + board_name + "." + VERSION_STR + ".xclbin";
@@ -470 +474 @@
-  return std::string(prefix) + ".aocx";
+  return std::string(prefix) + ".xclbin";
```
diff -u0 **third_party**/common/inc/AOCLUtils/opencl.h **sdaccel**/common/inc/AOCLUtils/opencl.h
```
--- third_party/common/inc/AOCLUtils/opencl.h      2016-11-23 20:38:30.000000000 +0000
+++ sdaccel/common/inc/AOCLUtils/opencl.h 2017-09-11 17:05:32.551000000 +0000
@@ -37,0 +38,2 @@
+
+static const char *const VERSION_STR = "xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0";
```

## Changes to the kernel code.
* The kernel code, found in the &lt;example_name>/device directory, will most likely need modifications.
* The vector addition kernel does not need changes.
* The FFT (1D) example needs several changes due to the differences between the third party and Xilinx implementations.
* See table below regarding [implementation differences between third party and Xilinx](#xilinx-and-third party-implementation-differences).

diff -u0 **third_party**/fft1d/device/fft1d.cl **sdaccel**/fft1d/device/fft1d.cl
```diff
--- third_party/fft1d/device/fft1d.cl      2017-05-09 22:47:43.000000000 +0000
+++ sdaccel/fft1d/device/fft1d.cl 2017-09-12 19:21:02.120000000 +0000
@@ -49 +49 @@
-#pragma OPENCL EXTENSION cl_intel_channels : enable
+//#pragma OPENCL EXTENSION cl_intel_channels : enable
@@ -64 +64,9 @@
-channel float2 chanin[8] __attribute__((depth(CONT_FACTOR*8)));
+
+pipe float2 chanin0 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin1 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin2 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin3 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin4 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin5 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin6 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
+pipe float2 chanin7 __attribute__((xcl_reqd_pipe_depth(CONT_FACTOR*8)));
@@ -68 +76 @@
-  #pragma unroll
+  __attribute__((opencl_unroll_hint()))
@@ -137,2 +145,2 @@
-__attribute__((reqd_work_group_size(CONT_FACTOR * POINTS, 1, 1)))
-kernel void fetch (global float2 * restrict src) {
+kernel __attribute__((reqd_work_group_size(CONT_FACTOR * POINTS, 1, 1)))
+void fetch (global float2 * restrict src) {
@@ -145 +153 @@
-  local float2 buf[BUF_SIZE];
+  local float2 buf[BUF_SIZE] __attribute__((xcl_array_partition(block,8,1)));
@@ -156,2 +164,2 @@
-  #pragma unroll
-  for (uint k = 0; k < POINTS; k++) {
+  __attribute__((opencl_unroll_hint()))
+  for (uint k = 0; k < POINTS; k+=2) {
@@ -160 +167,0 @@
-
@@ -163,4 +170,4 @@
-  #pragma unroll
-  for (uint k = 0; k < POINTS; k++) {
-    uint buf_addr = bit_reversed(k,3) * CONT_FACTOR * POINTS + lid;
-    write_channel_intel (chanin[k], buf[buf_addr]);
+  uint buf_addr[8];
+  __attribute__((opencl_unroll_hint()))
+  for(uint k=0;k<8;k++) {
+    buf_addr[k] = bit_reversed(k,3) * CONT_FACTOR * POINTS + lid;
@@ -167,0 +175,12 @@
+  // bit_reversed reverses the bit locations of the value given.
+  // The second parameter is the width of the number (in bits) to reverse.
+  // Only the non-symmetric numbers are changed.  E.g. 001,011,100,110 -> 100,110,100,110
+    write_pipe (chanin0, &buf[buf_addr[0]]);
+    write_pipe (chanin1, &buf[buf_addr[1]]);
+    write_pipe (chanin2, &buf[buf_addr[2]]);
+    write_pipe (chanin3, &buf[buf_addr[3]]);
+    write_pipe (chanin4, &buf[buf_addr[4]]);
+    write_pipe (chanin5, &buf[buf_addr[5]]);
+    write_pipe (chanin6, &buf[buf_addr[6]]);
+    write_pipe (chanin7, &buf[buf_addr[7]]);
+
@@ -180,2 +199,2 @@
-__attribute((task))
-kernel void fft1d(global float2 * restrict dest,
+kernel __attribute((reqd_work_group_size(1, 1, 1))) //task))
+void fft1d(global float2 * restrict dest,
@@ -218,8 +237,9 @@
-      data.i0 = read_channel_intel(chanin[0]);
-      data.i1 = read_channel_intel(chanin[1]);
-      data.i2 = read_channel_intel(chanin[2]);
-      data.i3 = read_channel_intel(chanin[3]);
-      data.i4 = read_channel_intel(chanin[4]);
-      data.i5 = read_channel_intel(chanin[5]);
-      data.i6 = read_channel_intel(chanin[6]);
-      data.i7 = read_channel_intel(chanin[7]);
+
+      read_pipe(chanin0,&data.i0);
+      read_pipe(chanin1,&data.i1);
+      read_pipe(chanin2,&data.i2);
+      read_pipe(chanin3,&data.i3);
+      read_pipe(chanin4,&data.i4);
+      read_pipe(chanin5,&data.i5);
+      read_pipe(chanin6,&data.i6);
+      read_pipe(chanin7,&data.i7);
```

* The &lt;example_name>/device/twid_radix4_8.cl file will get many warnings about casting from double to float.
* The shell commands below will cast the double constant values to float.

```sh
sed 's/\([0-9]\)\( \{0,\}[,}]\)/\1f\2/g' twid_radix4_8.cl > tmp
mv tmp twid_radix4_8.cl
```

## Changes to the Makefile.

* The third party Makefile can be replaced by a version that is similar to the SDAccel example Makefiles.
* For example, for the third party **vector_add** code, the Makefile would be as below.

```shell
COMMON_REPO := $(SDACCEL_DIR)/SDAccel/examples/xilinx

include $(COMMON_REPO)/utility/boards.mk
include $(COMMON_REPO)/libs/xcl/xcl.mk
include $(COMMON_REPO)/libs/opencl/opencl.mk

main_SRCS=$(wildcard host/src/*.cpp ../common/src/AOCLUtils/*.cpp) $(xcl_SRCS)
main_HDRS=$(xcl_HDRS)

main_CXXFLAGS=$(xcl_CXXFLAGS) $(opencl_CXXFLAGS)  -I../common/inc/
main_LDFLAGS=$(opencl_LDFLAGS) -lrt

EXES=main

# Kernel                                                         
vector_add_SRCS=./device/vector_add.cl
vector_add_CLFLAGS= -k vector_add

#Specifying Fifo depth for Dataflow
vector_add_CLFLAGS+=--xp "param:compiler.xclDataflowFifoDepth=32"

XOS=vector_add

# xclbin
vector_add_XOS=vector_add
XCLBINS=vector_add

# check
check_EXE=main
check_XCLBINS=vector_add
CHECKS=check

# Compilation flags
ifeq ($(DEBUG),1)
CXXFLAGS += -g
else
CXXFLAGS += -O2
endif

# Compiler
CXX := g++

include $(COMMON_REPO)/utility/rules.mk
```
* The **FFT(1D)** example would be the same except with the phrase `fft1d` replacing `vector_add`.  
* Also, because there are multiple kernels defined in one kernel file for `fft1d`, comment out the ``<kernel>_CFLAGS= -k <kernel>`` line.

## Compiling and running.
* The steps to compile and run would be the same as those used for the SDAccel examples with the exception that the host program would need the -hw=&lt;mode> switch when running in emulation mode.
* To run in hardware emulation mode, use the following commands.

```
make clean
source $XILINX_SDX/settings64.sh
make TARGETS=hw_emu DEVICES=$AWS_PLATFORM all
./main -hw=hw_emu
```

## Xilinx and third party Implementation Differences
#### Host Code
| third party FPGA     | Xilinx     |
| :------------- | :------------- |
| third party's device_info* APIs | OpenCL APIs: clGetPlatformIDs or clGetPlatformIds or clGetDeviceIds |
| findPlatform("Intel") | clGetPlatformInfo or findPlatform("Xilinx") |
| createProgramFromBinary | clCreateProgramWithBinary |
| CL_MEM_BANK_*_third party | XCL_MEM_DDR_BANK* |
| .aocx file | .xclbin file |
| CL_DEVICE_TYPE_ALL | CL_DEVICE_TYPE_ACCELERATOR |

#### Kernel Code
| third party FPGA | Xilinx |
| :------------- | :------------- |
| read/write_third party_channel | read/write_pipe_block |
| channel  keyword | pipe keyword |
| \_\_attribute__(8) | \_\_attribute__((xcl_reqd_pipe_depth(16))) |
| kernel name and kernel argument name can be the same | kernel_name and kernel arguments' name should be different |
| Implictly converting double type to float type | Explicitly converted double type to float type |
| declares and initializes an struct object together | declare an struct object and then initialize it separately |

## SUPPORT
For more information check here:
[SDAccel User Guides][]

For questions and to get help on this project or your own projects, visit the [SDAccel Forums][].

## REVISION HISTORY

Date    | Readme Version | Revision Description
--------|----------------|-------------------------
SEP2017 | 1.0            | Initial release



[SDAccel Forums]: https://forums.xilinx.com/t5/SDAccel/bd-p/SDx
[SDAccel User Guides]: http://www.xilinx.com/support/documentation-navigation/development-tools/software-development/sdaccel.html?resultsTablePreSelect=documenttype:SeeAll#documentation
