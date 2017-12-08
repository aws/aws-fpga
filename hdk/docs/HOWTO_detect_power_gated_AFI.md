# AFI Power Gating
 
* The Xilinx UltraScale+ FPGA devices used on the F1 instances have power limits that must be maintained.
* An AFI that tripped an over-current will be clock gated and will show the following effects:
   * AFI fpga-load-local-image will cause cl-id-mismatch (Any AFI load will show this error including the AWS public AFIs)
   * Transactions to CL will trigger timeouts on all Shell to CL interfaces
   * AFI fpga-clear-local-image will also fail and not clear the AFI
   * fpga-describe-local-image won’t necessarily show any failure, except maybe the cl-id-mismatch if you’ve tried to load another AFI.
* If you see these effects, you can use a lower clock frequency in the clock recipes to reduce the power consumed by the AFI. Recovering from a clock gated AFI requires you to terminate the instance.
* [Additional information on how to optimize for power](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_2/ug907-vivado-power-analysis-optimization.pdf)
