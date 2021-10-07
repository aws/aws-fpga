# Frequently Asked Questions (FAQ)

## Q: What are the clocks available to the RTL kernel on the AWS F1 Platform?
A: There are 3 clocks provided on the AWS F1 Platform. Their names and default frequencies are shown below.
   Among them, DATA_CLK and KERNEL_CLK can be used by the RTL kernel.

    * SYSTEM (clock_main_a0) @ 250 MHz
    * DATA_CLK (clock_extra_b0) @ 250 MHz
    * KERNEL_CLK (clock_extra_c0) @ 500 MHz

**NOTE**: *Frequency scaling can be enabled by Vitis on the kernel clock (DATA_CLK or KERNEL_CLK). This happens when the kernel's timing performance cannot be achieved. Vitis will lower the clock frequency to meet timing. For more details about kernel clock, please refer to [Vitis User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_2/ug1393-vitis-application-acceleration.pdf).*

## Q: What is the lowest frequency Vitis design supported on the AWS F1 Platform?
A: We support creating AFI's from CL's that have been built to work at Frequencies no lower than 80MHz.
   Re-clocking/Loading a dynamic clock frequency lower than 80MHz will also result in an error.
