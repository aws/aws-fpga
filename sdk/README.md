# AWS EC2 FPGA Software Development Kit

This directory includes the drivers and runtime environment required by any EC2 FPGA Instance. The drivers and tools are used to interact with pre-built AFIs that are loaded to EC2 FPGA Instance FPGAs.

The [SDK userspace directory](./userspace) contains the [Amazon FPGA Image (AFI) Management Tools](./userspace/fpga_mgmt_tools/README.md), which includes both the source code to the AFI Management Tools as well as detailed descriptions of the commands to use on an F1 instance.

The SDK is **NOT** used to build or register AFI, rather it is only used for managing and deploying pre-built AFIs. For building and registering AFIs, please refer to the [HDK](../hdk/README.md).

**NOTE:** This SDK is designed and tested for Linux environments only.

# Quick Start

## Using an AFI on an EC2 FPGA Instance

You can setup and install the SDK with the following few steps.  Note that the first two steps may be skipped if you have already ran them in the above HDK setup.

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source sdk_setup.sh                         # Set up the envronment variables, build and install the SDK


**NOTE:** The `sdk_setup.sh` would install the [FPGA management tools](./userspace/fpga_mgmt_tools/README.md) if they are not already available in `/usr/bin`. The `sdk_setup.sh` requires having `gcc` installed.  if it is not installed, try running the next command to install it on Amazon Linux, Centos or Redhat distributions:

```
$ sudo yum groupinstall -y "Development Tools"
```

## Notes for Ubuntu or other Debian based systems

To install gcc with apt-get, execute:

```
$ sudo apt-get update
$ sudo apt-get install build-essential
```

## Using FPGA as non-root user

SDK supports granting access to FPGA resources and AFI management tools to users other than root. The SDK setup will create a group and make all the device resources members of this group. The user will be added to this group. Variables below help control this feature
* AWS_FPGA_ALLOW_NON_ROOT when set, will turn on the feature.
* AWS_FPGA_SDK_GROUP specifies group that will have access to FPGA and AFI tools. The setup will create the group and add user to this group. User must switch or relogin to have this group membership effective. If unspecified, this will default to "fpgauser".
* AWS_FPGA_SDK_OVERRIDE_GROUP specifies to add user to already existing group specified by AWS_FPGA_SDK_GROUP. If this is unset and AWS_FPGA_SDK_GROUP evaluates to an  existing group, setup will fail.

### Example
Hello world example as non-root user can be demonstrated as below:

```
$ export AWS_FPGA_ALLOW_NON_ROOT=y
$ cd aws-fpga
$ source sdk_setup.sh
$ cd hdk/cl/examples/cl_hello_world/software/runtime
$ make
$ fpga-load-local-image -S0 -I $CL_HELLO_WORLD_AFI
$ ./test_hello_world
AFI PCI  Vendor ID: 0x1d0f, Device ID 0xf000
===== Starting with peek_poke_example =====
Writing 0xefbeadde to HELLO_WORLD register (0x0000000000000500)
=====  Entering peek_poke_example =====
register: 0xdeadbeef
TEST PASSEDResulting value matched expected value 0xdeadbeef. It worked!
Developers are encouraged to modify the Virtual DIP Switch by calling the linux shell command to demonstrate how AWS FPGA Virtual DIP switches can be used to change a CustomLogic functionality:
$ fpga-set-virtual-dip-switch -S (slot-id) -D (16 digit setting)

In this example, setting a virtual DIP switch to zero clears the corresponding LED, even if the peek-poke example would set it to 1.
For instance:
# sudo fpga-set-virtual-dip-switch -S 0 -D 1111111111111111
# sudo fpga-get-virtual-led  -S 0
FPGA slot id 0 have the following Virtual LED:
1010-1101-1101-1110
# sudo fpga-set-virtual-dip-switch -S 0 -D 0000000000000000
# sudo fpga-get-virtual-led  -S 0
FPGA slot id 0 have the following Virtual LED:
0000-0000-0000-0000
$ fpga-set-virtual-dip-switch -S 0 -D 1111111111111111
$ fpga-get-virtual-led  -S 0
FPGA slot id 0 have the following Virtual LED:
1010-1101-1101-1110
```

### Note on using LDAP/NIS users

SDK will only create local group and modify local users. If the system is administered by LDAP or NIS, user must override group creation by AWS_FPGA_SDK_OVERRIDE_GROUP and add user in desired AWS_FPGA_SDK_GROUP group before setup. SDK will detect this membership and only install necessary group permissions to the resources. For this detection to work, the Name Service Switch configuration (see manpage sswitch.conf(5)) must have enumeration of entries for passwd and group for all databases where user/group can exist.

### Prerequisites for using non-root user access feature

* The FPGA must be in cleared state before SDK setup for this feature to take effect.
* SDK uses udev rules to detect changes in device and setup permissions and owners of the resources. Minimum linux  kernel version of 2.6.25 is necessary for udev features used. The SDK also uses shadow utilities (typically shadow-utils package) and glibc-common package tools.
* The feature only ensures the resources and tools are accessible. If the customer logic requires any kernel modules, they must be loaded as root and be set with appropriate permissions/ownership.
* sudo access is needed at the time of setup.
