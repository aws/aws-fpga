# Python Bindings

The python bindings are foreign function interface to call AWS SDK FPGA tools used to load AFI, clear slots, describe slots etc that are described in SDK_DIR/userspace/include directory. These bindings are generated and will only work as long as the signatures of the underlying API do not change.


## Example
The illustration here shows how a Python Flask microframework based app can accelerate using FPGA. The acceleration module is a simple byte swapper done in FPGA. The toy app is located in byte_swapper directory.

### Requirements
The example assumes that Flask microframework and SDK are installed. The AFI that will serve to accelerate parts of the microservice is already generated and available to be loaded at the time of app initialization.
```
# Current dir is SDK_DIR/apps/byte_swapper
$ sudo su
$ export BSWAPPER_SLOT=$SLOT
$ export BSWAPPER_AFI=$MY_AFI
$ export BSWAPPER_REG=$PCI_REG
$ flask run
 * Environment: production
   WARNING: Do not use the development server in a production environment.
   Use a production WSGI server instead.
 * Debug mode: off
....
# From a second terminal, send GET queries.
$ curl http://127.0.0.1:5000/?input_data=0x12345678
$ 78563412
```
