# AFI Power Management
If a loaded AFI consumed more power than maximum power that can be provided by the FPGA, the F1 system will automatically gate the input clocks provided to the AFI in order to prevent errors within the FPGA. This is called an afi-power-violation. Specifically, when Vccint utilization is greater than 85 watts, the CL will have a power warning bit set. Above that level, the CL is in danger of being clock gated due to an afi-power-violation.

## Preventing power violation

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

In order to help developers avoid these overpower events, the F1 system sets a warning bit in the CL (sh_cl_pwr_state) when the FPGA power levels are above 85 watts, and the CL is in danger of having it's clocks disabled. This should allow the CL to self-throttle, or reduce power-hungry optimizations, and avoid having its input clocks disabled.

## Detecting power-violation
The fpga-describe-local-image command will show that the AFI load has failed due to an afi-power-violation

```
    # fpga-describe-local-image -S 0
    AFI          0       none                    load-failed          7        afi-power-violation        17       0x071417d3
    AFIDEVICE    0       0x1d0f      0xf000      0000:00:1d.0
```

An afi-power-violation can occur either when the FPGA is first loaded, or while the FPGA is running a particularly power-intense workload. If the power-violation occurs during a fpga-load-local-image, the load local image will itself fail with the afi-power-violation error.

## Recovering from clock gating

When an afi-power-violation occurs, the FPGA can still be loaded and cleared, but the clocks cannot be re-enabled without reloading the FPGA. Any AFI load or clear should restore full functionality to the FPGA.
