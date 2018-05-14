# Migrating to dynamic DSA (2017.4 SDx)                           

## If using multiple DDR banks
* The --xp map_connect option has been removed and replaced with the -sp option which provides a much simpler syntax to specify system port mappings.
* The following shows how an existing map_connect option must be changed for 2017.4.
  * (2017.1) --xp misc:map_connect=add.kernel.krnl_idct_1.M_AXI_GMEM.core.OCL_REGION_0.M00_AXI
  * (2017.4) --sp krnl_idct_1.m_axi_gmem:bank0
 
 
## If using the HLS header files (for instance for AP datatypes or hls::stream)
* The location of the HLS header files has changed.
* The following shows how the include pathname must be changed for 2017.4
  * (2017.1) -I$(XILINX_SDACCEL)/Vivado_HLS/include/
  * (2017.4) -I$(XILINX_SDACCEL)/include
 
 
## If using RTL kernels
* The RTL kernel packaging script must set two properties on the RTL IP prior to running the package_xo command.
  * (2017.4) Add the following properties to the RTL kernel packaging script (package_kernel.tcl):
```  
set_property sdx_kernel true [ipx::current_core]
set_property sdx_kernel_type rtl [ipx::current_core]
``` 
 
## If using more than one xclbin file
* If using more than one xclbin file, the first must be released before second is loaded.        
  * (2017.1) Host code may look like this:
```  
  clCreateProgramWithBinary(xclbin1);  // load first xclbin
  ...                                  // run with first xclbin
  clCreateProgramWithBinary(xclbin2);  // load second xclbin
  ...                                  // run with second xclbin
``` 
  * (2017.4) In the host code, free the current xclbin using clReleaseProgram() and clReleaseKernel() before proceeding to load subsequent xclbin files.
```  
  clCreateProgramWithBinary(xclbin1);  // load first xclbin
  ...                                  // run with first xclbin
  clReleaseProgram();                  // release program
  clReleaseKernel();                   // release kernel
  clCreateProgramWithBinary(xclbin2);  // load second xclbin
  ...                                  // run with second xclbin
  clReleaseProgram();                  // release program
  clReleaseKernel();                   // release kernel
``` 
 
## If requiring generation of profiling reports
* Profiling hardware no longer pre-built in the platform. Instead, it is added compile time to the design.
* This requires an update to the xocc command options.     
  * (2017.4) Add the -profile_kernel option the xocc command to enable profile instrumentation when compiling the kernel; set profile=true in the sdaccel.ini file to collect profile data when running the application.
  
## Additional resources
* [SDAccel Development Enviroment - Changes for 2017.4](https://www.xilinx.com/html_docs/xilinx2017_4/sdaccel_doc/jdl1512623841682.html)
* [SDAccel Development Enviroment - Whats new for 2017.4](https://www.xilinx.com/html_docs/xilinx2017_4/sdaccel_doc/rke1512623904797.html)
* [SDAccel Development Enviroment - Migration Summary](https://www.xilinx.com/html_docs/xilinx2017_4/sdaccel_doc/jru1513128364984.html)


  
