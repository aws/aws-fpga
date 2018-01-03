# Viewing and Configuring Clock Frequencies

F1 customers can both view and configure their AFIs programmed clock frequencies. These features are targeted for SDAccel customers, but are available to all customers. Clock frequencies are presented in Mhz, rounded down (so 136.7 Mhz becomes 136 Mhz). If a customer needs more precision, precision up to 1 hz is available in the SDK. 

For example, the hello world AFI shows clock groups as:

```
fpga-describe-local-image -S 0 -M
…
Clock Group A
  250  125  375  500
Clock Group B
  250  125 
Clock Group C
  300  400
```

To set an AFI’s clock speed, users can add an option to fpga-load-local-image to specify a frequency for clock 0 in a group in Mhz:

```
fpga-load-local-image –S 0 –I <afi_id> -a 90 –b 270 –c 1
```

For each clock group, if the requested clock frequency is slower than the frequency of the clock at ingestion, the clock will be set to the slowest frequency in the actual values column in table 1 which is slower than the request. If the request is slower than any entry in the table (e.g. 1 Mhz), the slowest frequency in the table will be selected. All other clock dividers in the group will be set to a maximum value, usually ~25 times slower than clock 0. If the request is faster than clock 0 of that group was set to on ingestion, the clock group will be left alone and set to the value from ingestion. The actual programmed values will be visible in fpga-describe-local-image after the load. 

Since the actual frequencies are somewhat irregular, a clock group can be loaded with its nominal value, which is the actual frequency in Mhz rounded down. This will mean that a request for 109 Mhz will result in a clock frequency of 109.375 Mhz, rather than the next lowest actual frequency of 97.22 Mhz. This will still not permit any clock value to rise above its ingested value.  
 
Table 1: Supported clock frequencies	

|Nominal values (Mhz)|Actual values (hz)|
|-----|-----|
|87|87500000|
|97|97222222|
|109|109375000|
|125|125000000|
|136|136718750|
|156|156250000|
|166|166666666|
|171|171875000|
|177|177083333|
|182|182291666|
|187|187500000|
|196|196428571|
|218|218750000|
|227|227678571|
|250|250000000|
|265|265625000|
|273|273437500|
|291|291666666|
|318|318750000|
|333|333333333|
|343|343750000|
|364|364583333|
|375|375000000|
|437|437500000|
|458|458333333|
|500|500000000|

