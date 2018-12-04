# Debug HLS Performance: Limited memory ports.

In an ideal FPGA implementation, the kernel will process 1 data sample per clock cycle. In the High-Level Synthesis (HLS) technology used in SDAccel, this is referred to an II=1 implementation, where II is the Initiation Interval of design, or the number of clock cycles before the design can read new data inputs.

In some cases, the HLS technology is unable to create an II=1 design, and you may see the following message:

```
	INFO: [XOCC 204-61] Pipelining loop 'SUM_LOOP'.
	WARNING: [XOCC 204-69] Unable to schedule 'load' operation ('mem_load_2', /..PATH../MyCode.cl:125) on array 'mem', /..PATH../MyCode.cl:125 due to limited memory ports. Please consider using a memory core with more ports or partitioning the array 'mem'.
	INFO: [XOCC 204-61] Pipelining result: Target II: 1, Final II: 2, Depth: 42.
```
The message notes that this is **due to limited memory ports** and suggests you **partitioning the array 'mem'**. The is explained in more detail below.

# HLS Backgrounder: Mapping to Block-RAM

First, let's review how an array in the C code is implemented in FPGA hardware. The HLS technology used in SDAccel maps an array in the kernel code into a Xilinx Block-RAM.
  
- An array is a collection of elements accessed through an index.
- A Block-RAM is an embedded RAM: a collection of data elements accessed via an address. 

The mapping from an array to a Block-RAM is a very natural mapping. It ensures all arrays in the kernel code are mapped to efficient local memory resources in the FPGA.  

An issue which can present itself, is that the Block-RAMs on the FPGA have only two data ports: only two addresses may be accessed in a single clock cycle. The following kernel code represents code which can limit performance and present a message similar to the one shown above:

```
	int mem[N];
	int sum=0;
	int i;

	SUM_LOOP:for(i=0;i<N;++i){
		sum += mem[i] + mem[i+1] + mem[i+2];
	}
```

The code  performs 3 accesses to the array, and hence 3 accesses to the Block-RAM. Since the Block-RAM only has 2 data ports, it is impossible to perform 3 accesses in a single clock cycle. This in turn means the design cannot process 1 sample per clock (or achieve an II=1). 

# Improving Throughput

In cases where the code does not map ideally onto a Block-RAM resource, an HLS directive or OpenCL attribute may be used to **partition** the array into multiple Block-RAMs. Since this results in the array being implemented with more Block-RAMs, it means more ports to access the data and hence allows more than 2 accesses per clock cycle. 

Full details on the HLS optimization directives are provided in the [SDx Pragma Reference Guide][pragma_ref_guide] however using the code above as an example, we can explain how this optimization is used. 

The **partition** optimization has two primary options. 

- The partition **factor** which specifies how many Block-RAM instances should be used to implement the array. 
- The **type** option specifies how to arrange the data in the newly partitioned array. 

First, let's review the **factor** option. 

**Without** any partitioning, each element in the array is mapped into a single instance of Block-RAM, called **mem** in this example, and data from the array is mapped into the Block-RAM in the same sequence: Block-RAM instance **mem** contains data values 0,1,2,3,..., N-1.

We can partition the array by a **factor** of 2. This will result in 2 Block-RAM instances to implement the array in the C code. For this example, we will refer to these instances as **mem_0** and **mem_1**. Each Block-RAM has two ports, so this allows up to 4 simultaneous accesses to the data. However, the default **type** of partitioning is **block** partitioning, which partitions the array as two halves with the following sequences: 

- Instance **mem_0** contains the array data values  0,1,2,..,(N/2)-1 
- Instance **mem_1** contains the array data values  N/2,(N/2)+1,(N/2)+2,..,N-1
 
In the example code above, the three accesses are sequential, to addresses i, i+1 and i+2. The default partitioning does not help in accessing 3 sequential addresses since, for example, mem[0], mem[1] and mem[2] are still implemented in the same Block-RAM and cannot be accessed simultaneously (only two of them can be accessed in the same clock cycle because all three locations are in the same instance of Block-RAM). 

Another **type** of partitioning, called **cyclic**, arranges the data in the following pattern: 
- Instance **mem_0** contains the array data values 0,2,4,... (N-2)
- Instance **mem_1** contains the array data values 1,3,5,... (N-1)

This allows three sequential addresses to be accessed in the same clock cycle: only two data values are ever in the same Block-RAM and both instances of Block-RAM have two ports each.

# Adding Optimizations to the Kernel code.

For OpenCL kernels, the following attribute is used:

```
	int mem[N] __attribute__((xcl_array_partition(cyclic,2,1)));
```

For C/C++ kernels, the following directive is used:

```
	#pragma HLS ARRAY_PARTITION variable=mem cyclic factor=2 partition
	int mem[N];
```
With these optimizations specified in the C code, the array mem is implemented in 2 Block-RAM and all three sequential values may be accessed in the same clock cycle. This results in a higher performance design. 

[pragma_ref_guide]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1253-sdx-pragma-reference.pdf


