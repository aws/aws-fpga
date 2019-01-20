# AFI Power
There are 2 power related scenarios that need to be avoided:
1. Exceeding the Maximum FPGA power
1. Ramping too quickly between low power and high power states

## Exceeding Maximum FPGA power
The Xilinx UltraScale+ FPGA devices used on the F1 instances have a maximum power limit that must be maintained.  If a loaded AFI consumes maximum power, the F1 instance will automatically gate the input clocks provided to the AFI in order to prevent errors within the FPGA. This is called an afi-power-violation. Specifically, when power (Vccint) is greater than 85 watts, the CL will have a power warning bit set. Above that level, the CL is in danger of being clock gated due to an afi-power-violation.

## Ramping too Quickly Between Low Power and High Power States
Even though your design may have a max power which is lower than the previously described limit, you might see issues if you rapidly switch between low power and high power states. A common scenario is upon startup the design goes from a low power reset state to the max power state instantly. In failing cases the host will appear to lose contact with the FPGA card and can only recover with an instance stop/restart. To prevent this from happening care must be taken to sequence the design such that it slowly increases the power requirements to max power instead of instantaneously doing so. 

# Measuring FPGA Power - Live or Offline via Vivado
## Live Measurement of FPGA Power
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

## Lowering Power Based on High Power Events Reported by the Shell
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

# Power Savings Techniques
Here are some low power design techniques that can be used to lower the overall power or minimize instantaneous power ramps.

Power is consumed whenever a node in the design switches high or low. Reducing the switching activity will reduce the power requirements. 

**Clock Nets:** The largest component of switching activity are the clock nets in the design. Power is consumed on both transition edges of the clock.  Some common techniques to reduce clock power are:
1. Clocking design at lower frequencies will lower clock power linearly. This isn’t always possible.
1. If the entire design doesn’t need to be clocked at full frequency, create lower frequency clocks for the slower logic.
1. If parts of the logic don’t need to always be clocked, you can gate the clocks to them (AND the clock with an enable signal). The gated clock net will draw no power when it’s gated off.

**Outputs of Sequential Elements:**  Outputs of FF’s and RAMs cause downstream logic to consume power every time they switch. There are many times when these sequential elements don’t need to switch every cycle. Some common techniques to reduce sequential element power are:
1. Add enables to as many FF’s as possible. This will cause the FF’s output to switch less often, lowering power on all downstream nodes.
1. Add chip-selects or read-enables to your RAMs. Same concept as #1.
1. Shift-register structures (LFSR’s, CRC, random number generators, etc.) burn power because their outputs switch. Add enables to these FF’s to switch them only when needed.

**Architectural Power Savings**: A global power savings technique is to control power at the top-level Architectural Level. There is typically a block diagram of the overall design. By gating the clocks to top-level blocks and/or creating enables for the sequential elements in the design, these blocks can be put into low power modes when they aren't being used. It's critical to only enable the blocks that are required for the job.

**Reducing Instantaneous Swings in Power**: Care must be taken to ensure there aren't large swings between low power and high power states. Sequencing the enables to the top-level architectural blocks will allow the design to slowly ramp to max power levels.



