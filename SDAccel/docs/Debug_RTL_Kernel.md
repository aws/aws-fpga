Hardware Debug of SDAccel RTL Kernel Design
======================

This file contains the following sections:

1. Overview
2. Instantiating Debug cores in your RTL Kernel design
3. Host code changes to support debugging
4. Building the executable, creating the AFI, and executing the host code
5. Start debug servers


## 1. Overview
The sections below give you a brief explanation of the steps required to debug your SDAccel RTL kernel design.  They include instantiating the ILA/debug cores in your RTL kernel, pausing the execution of the host code at the appriopriate stage to ensure the setup of ILA triggers, building the running the host code and starting the debug servers to debug the design in hardware.  

## 2. Instantiating Debug cores in your RTL kernel design

You need to instantiate debug cores like the Integrated Logic Analyzer(ILA), Virtual Input/Output(VIO) etc in your application RTL kernel code.

The ILA Debug IP can be created and added to the RTL Kernel in a couple of ways. 


1. Open the ILA IP customization wizard in the Vivado GUI and customize the ILA and instantiate it in the RTL code – similar to any other IP in Vivado.


2. Create the ILA IP on the fly using TCL.  A snippet of the create_ip TCL command is shown below. The example below creates the ILA IP with 7 probes and associates properties with the IP.

```
	create_ip -name ila -vendor xilinx.com -library ip -module_name ila_0
	
	set_property -dict [list CONFIG.C_PROBE6_WIDTH {32} CONFIG.C_PROBE3_WIDTH {64} CONFIG.C_NUM_OF_PROBES {7} CONFIG.C_EN_STRG_QUAL {1} CONFIG.C_INPUT_PIPE_STAGES {2} CONFIG.C_ADV_TRIGGER {true} CONFIG.ALL_PROBE_SAME_MU_CNT {4} CONFIG.C_PROBE6_MU_CNT {4} CONFIG.C_PROBE5_MU_CNT {4} CONFIG.C_PROBE4_MU_CNT {4} CONFIG.C_PROBE3_MU_CNT {4} CONFIG.C_PROBE2_MU_CNT {4} CONFIG.C_PROBE1_MU_CNT {4} CONFIG.C_PROBE0_MU_CNT {4}] [get_ips ila_0]
```

This TCL file should be added as an RTL Kernel source in the Makefile of your design


Now you are ready to instantiate the ILA Debug core in your RTL Kernel. The RTL code snippet below is an ILA that monitors the output of a combinatorial adder.

		// ILA monitoring combinatorial adder
		ila_0 i_ila_0 (
			.clk(ap_clk),              // input wire        clk
			.probe0(areset),           // input wire [0:0]  probe0  
			.probe1(rd_fifo_tvalid_n), // input wire [0:0]  probe1 
			.probe2(rd_fifo_tready),   // input wire [0:0]  probe2 
			.probe3(rd_fifo_tdata),    // input wire [63:0] probe3 
			.probe4(adder_tvalid),     // input wire [0:0]  probe4 
			.probe5(adder_tready_n),   // input wire [0:0]  probe5 
			.probe6(adder_tdata)       // input wire [31:0] probe6
		);

## 3. Host code changes to support debugging

The application host code  needs to be modified to ensure you can set up the ILA trigger conditions **prior** to  running the kernel. 
The host code shown below introduces the wait for the setup of ILA Trigger conditions and the arming of the ILA.

src/host.cpp

		void wait_for_enter(const std::string& msg)
		{
		    std::cout << msg << std::endl;
		    std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
		}
    
		...
    
		cl::Program::Binaries bins = xcl::import_binary_file(binaryFile);
		devices.resize(1);
		cl::Program program(context, devices, bins);
		cl::Kernel krnl_vadd(program,"krnl_vadd_rtl");
		
		wait_for_enter("\nPress ENTER to continue after setting up ILA trigger...");
		
		//Allocate Buffer in Global Memory
		
		...
    
		//Launch the Kernel
		q.enqueueTask(krnl_vadd);



## 4. Building the executable, creating the AFI and executing the host code

- **Build the executable** in your design directory (`your_design_directory`) by running the steps below:

```
	cd your_design_directory

	make all DEVICES=$AWS_PLATFORM
```

- **Creating and registering the AFI**

Please note, the angle bracket directories need to be replaced according to the user setup.

```	
	$SDACCEL_DIR/tools/create_sdaccel_afi.sh -xclbin=your_design.hw.xilinx_aws-vu9p-f1-04261818_dynamic_5_0.xclbin -o=your_design.hw.xilinx_aws-vu9p-f1-04261818_dynamic_5_0.awsxclbin -s3_bucket=<bucket-s3_dcp_key=<f1-dcp-folder-s3_logs_key=<f1-logs>
```

- **Setup and Execute**

```
		$ sudo sh
		# source /opt/Xilinx/SDx/2017.4.rte.dyn/setup.sh
		# ./host
```
This produces the following output: 
```
			Device/Slot[0] (/dev/xdma0, 0:0:1d.0)
			xclProbe found 1 FPGA slots with XDMA driver running
			platform Name: Xilinx
			Vendor Name : Xilinx
			Found Platform
			XCLBIN File Name: vadd
			INFO: Importing ./binary_container_1.awsxclbin
			Loading: './binary_container_1.awsxclbin'
			Successfully skipped reloading of local image.
			
			Press ENTER to continue after setting up ILA trigger...
```		
		

## 5. Start Debug Servers

#### Starting Debug Servers on Amazon F1 instance
Instructions to start the debug servers on an Amazon F1 instance can be found [here](../../hdk/docs/Virtual_JTAG_XVC.md).
Once you have setup your ILA triggers and armed the ILA core, you can now Press Enter on your host to continue execution of the application and RTL Kernel.

