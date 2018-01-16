# AFI Power
The Xilinx UltraScale+ FPGA devices used on the F1 instances have a maximum power limit that must be maintained.  If a loaded AFI consumes maximum power, the F1 instance will automatically gate the input clocks provided to the AFI in order to prevent errors within the FPGA. This is called an afi-power-violation. Specifically, when power (Vccint) is greater than 85 watts, the CL will have a power warning bit set. Above that level, the CL is in danger of being clock gated due to an afi-power-violation.

## Preventing power violations
In order to help developers understand how much power their AFIs actually use in the field, AWS now presents power metrics in the fpga-describe-local-image tool. These metrics are updated every minute, and will reflect the most recently measured FPGA power, the average power over the run of the AFI, and the maximum power consumption detected in the run of the AFI. The current and average power consumption will be available on the first power update after the AFI is loaded, while the max power measurements will start after this first update (max power will not include the time immediately after the FPGA is loaded).  

For example,

```
fpga-describe-local-image -S 0 -M
…
Power consumption (Vccint):
   Last measured: 17 watts
   Average: 17 watts
   Max measured: 19 watts
```

Power consumption may drift slightly over time, and may vary from instance to instance. In order to prevent a power violation, it's important to take into account this natural variation, and design with margin accordingly.

In order to help developers avoid these overpower events, the F1 system indicates a afi-power-warning on the CL interface (sh_cl_pwr_state[1:0]) when the FPGA power levels are above 85 watts, and the CL is in danger of having it's clocks disabled. This should allow the CL to self-throttle, or reduce power-hungry optimizations, and avoid having its input clocks disabled.

Power state of the FPGA:  sh_cl_pwr_state[1:0]
0x0 – OK
0x1 – UNUSED
0x2 – afi-power-warning
0x3 – afi-power-violation

## Detecting power-violation
The fpga-describe-local-image command will show that the AFI load has failed due to an afi-power-violation

```
    # fpga-describe-local-image -S 0
    AFI          0       none                    load-failed          7        afi-power-violation        17       0x071417d3
    AFIDEVICE    0       0x1d0f      0xf000      0000:00:1d.0
```

An afi-power-violation can occur either when the FPGA is first loaded, or while the FPGA is running a particularly power-intense workload. If the afi-power-violation occurs during a fpga-load-local-image, the load local image will itself fail with the afi-power-violation error.  After a afi-power-violation, transactions to CL will trigger [timeouts on all Shell to CL interfaces](./HOWTO_detect_shell_timeout.md). 

## Analyze power reports from Vivado
Once the AFI power has been identified on F1, we recommend using Vivado to analyze the design to help reduce power.  First, open the DCP (Design check point) in the Vivado GUI.  Then, run the tcl command within Vivado:
```
report_power –file <path_to_output_file>
```
Below is a snippet of this report. The power supply, Vccint, is the supply for all the FPGA internal logic. The Total (A) is the measure of the current needed by your design.  Reducing total current will reduce your F1 instance power metrics.

```
1.2 Power Supply Summary
------------------------
 
+--------------+-------------+-----------+-------------+------------+
| Source       | Voltage (V) | Total (A) | Dynamic (A) | Static (A) |
+--------------+-------------+-----------+-------------+------------+
| Vccint       |       0.850 |    76.958 |      73.353 |      3.605 |
``` 
The “Detailed Report” section can be used to drill down to see which parts of the design are drawing the most power.

NOTE: This default usage of report_power makes gross assumptions about designs that may not be accurate. Because of this, focus on relative comparisons of values between designs rather than the absolute value. Additional methods to improving the accuracy of report_power are described here:
https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_2/ug907-vivado-power-analysis-optimization.pdf

Using a lower clock frequency from the [supported clock recipe](./clock_recipes.csv) will reduce the power consumed by the AFI.  

## Recovering from clock gating
When an afi-power-violation occurs, the FPGA can still be loaded and cleared, but the clocks cannot be re-enabled without reloading the FPGA. Any AFI load or clear will restore full functionality to the FPGA.


