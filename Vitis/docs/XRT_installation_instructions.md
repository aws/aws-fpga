# Xilinx Runtime (XRT) and Vitis Tool versions

* Xilinx Runtime versions match with the tool that you created your Vitis AFI with. 
* We provide pre-built RPM's for Centos/RHEL/AL2 and instructions for building XRT 
* Use the below table as reference to install and use the correct XRT version for your applications.

| Xilinx Vitis Tool Version | XRT Release Tag | SHA | `xrt` or `xrt-aws` RPM's (Centos/RHEL) |`xrt` or`xrt-aws` RPM's (AL2) |
|---|---|---|---|---|
|2021.2| [202120.2.12.427](https://github.com/Xilinx/XRT/releases/tag/202120.2.12.427) | 2719b6027e185000fc49783171631db03fc0ef79 | [xrt_202120.2.12.0_7.9.2009-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.12.0/Patches/XRT_2021_2/xrt_202120.2.12.0_7.9.2009-x86_64-aws.rpm) [xrt_202120.2.12.0_7.9.2009-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.12.0/Patches/XRT_2021_2/xrt_202120.2.12.0_7.9.2009-x86_64-xrt.rpm) | [xrt_202210.2.13.0_2-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.12.0/Patches/XRT_2021_2/xrt_202210.2.13.0_2-x86_64-aws.rpm) [xrt_202210.2.13.0_2-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.12.0/Patches/XRT_2021_2/xrt_202210.2.13.0_2-x86_64-xrt.rpm)|
|2021.1| [202110.2.11.634](https://github.com/Xilinx/XRT/releases/tag/202110.2.11.634) | 5ad5998d67080f00bca5bf15b3838cf35e0a7b26 | [xrt_202110.2.11.0_7.9.2009-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.11.0/Patches/XRT_2021_1/xrt_202110.2.11.0_7.9.2009-x86_64-xrt.rpm) [xrt_202110.2.11.0_7.9.2009-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.11.0/Patches/XRT_2021_1/xrt_202110.2.11.0_7.9.2009-x86_64-aws.rpm) | [xrt_202110.2.11.0_2-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.11.0/Patches/XRT_2021_1/xrt_202110.2.11.0_2-x86_64-xrt.rpm) [xrt_202110.2.11.0_2-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.11.0/Patches/XRT_2021_1/xrt_202110.2.11.0_2-x86_64-aws.rpm)|
|2020.2| [202020.2.8.743](https://github.com/Xilinx/XRT/releases/tag/202020.2.8.743) | 77d5484b5c4daa691a7f78235053fb036829b1e9 | [xrt_202020.2.8.0_7.9.2009-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.10.0/Patches/XRT_2020_2/xrt_202020.2.8.0_7.9.2009-x86_64-xrt.rpm) [xrt_202020.2.8.0_7.9.2009-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.10.0/Patches/XRT_2020_2/xrt_202020.2.8.0_7.9.2009-x86_64-aws.rpm) | [xrt_202020.2.8.0_2-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.10.0/Patches/XRT_2020_2/xrt_202020.2.8.0_2-x86_64-xrt.rpm) [xrt_202020.2.8.0_2-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.10.0/Patches/XRT_2020_2/xrt_202020.2.8.0_2-x86_64-aws.rpm)|
|2020.1| [202010.2.6.AWS](https://github.com/Xilinx/XRT/releases/tag/202010.2.6.AWS) | d09c4a458c16e8d843b3165dcf929c38f7a32b6f | [xrt_202010.2.6.0_7.7.1908-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.9.0/Patches/XRT_2020_1/xrt_202010.2.6.0_7.7.1908-x86_64-xrt.rpm) [xrt_202010.2.6.0_7.7.1908-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.9.0/Patches/XRT_2020_1/xrt_202010.2.6.0_7.7.1908-x86_64-aws.rpm) | [xrt_202010.2.6.0_2-x86_64-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.9.0/Patches/XRT_2020_1/xrt_202010.2.6.0_2-x86_64-xrt.rpm) [xrt_202010.2.6.0_2-x86_64-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.9.0/Patches/XRT_2020_1/xrt_202010.2.6.0_2-x86_64-aws.rpm)|
|2019.2| [2019.2.0.3](https://github.com/Xilinx/XRT/releases/tag/2019.2.0.3) | 9e13d57c4563e2c19bf5f518993f6e5a8dadc18a | [xrt_201920.2.3.0_7.7.1908-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.8.0/Patches/XRT_2019_2/xrt_201920.2.3.0_7.7.1908-xrt.rpm) [xrt_201920.2.3.0_7.7.1908-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.8.0/Patches/XRT_2019_2/xrt_201920.2.3.0_7.7.1908-aws.rpm) | N/A |

<a name="mpd"></a>
# MPD
From 2019.2 toolset onwards, [Xilinx XRT architecture has been made more modular](https://xilinx.github.io/XRT/master/html/cloud_vendor_support.html).
To be able to do so, the new architecture implements a Message Proxy Daemon in user space that interacts with the management library.
This also allows us to make calls to the management library without requiring privileged access to the user on the host.

## FPGA Developer AMI usecase
Since this Daemon is only required for the Vitis flow, it is disabled by default on the FPGA Developer AMI as we support both the Vitis and The Vivado flows.
The `vitis_runtime_setup.sh` script when called automatically checks for and starts the MPD daemon.
Once MPD Daemon starts up, it loads a 'Default AFI' on all the slots that lets the XOCL driver bind to the device.
Since we only support Device ID 0xF010 for the Vitis workflow, any subsequent loads of AFI's would work seamlessly.

However, after MPD has started if you clear the slot, the cleared slot will show a Device ID 0x1042 and XOCL will not bind.
Therefore, to be able to run your host application again after clearing a slot manually, you will need to restart the MPD service:
            ```sudo systemctl restart mpd```

**Note that MPD service starts asynchronously, so you might have to wait till all the slots are loaded with the Default AFI before your application can run.**
 
## Custom Runtime AMI usecase
On your custom Runtime AMI, MPD will be enabled by default once you install Xilinx XRT.
On startup, MPD will check if the instance has FPGA's and will load the Default AFI's.
After MPD has started if you clear the slot, the cleared slot will show a Device ID 0x1042 and XOCL will not bind.
Therefore, to be able to run your host application again after clearing a slot manually, you will need to restart the MPD service:
            ```sudo systemctl restart mpd```
**Note that MPD service starts asynchronously, so you might have to wait till all the slots are loaded with the Default AFI before your application can run.**

## Default AFI details
The Default AFI loaded is a regular `Hello World` AFI that provides the Device ID 0xF010.

# Centos/RHEL build and install steps

```bash
XRT_RELEASE_TAG=2019.2.0.3 # Substitute XRT_RELEASE_TAG=<TAG from above table>

git clone https://github.com/aws/aws-fpga.git

cd aws-fpga
source vitis_setup.sh
cd $VITIS_DIR/Runtime
export XRT_PATH="${VITIS_DIR}/Runtime/${XRT_RELEASE_TAG}"
git clone http://www.github.com/Xilinx/XRT.git -b ${XRT_RELEASE_TAG} ${XRT_PATH}

cd ${XRT_PATH}
sudo ./src/runtime_src/tools/scripts/xrtdeps.sh

cd build
scl enable devtoolset-6 bash
./build.sh

cd Release
sudo yum reinstall xrt_*.rpm -y
```

# AL2 build and install steps

```bash
XRT_RELEASE_TAG=202010.2.6.AWS # Substitute XRT_RELEASE_TAG=<TAG from above table>

git clone https://github.com/aws/aws-fpga.git

cd aws-fpga
source vitis_setup.sh
cd $VITIS_DIR/Runtime
export XRT_PATH="${VITIS_DIR}/Runtime/${XRT_RELEASE_TAG}"
git clone http://www.github.com/Xilinx/XRT.git -b ${XRT_RELEASE_TAG} ${XRT_PATH}

cd ${XRT_PATH}
sudo ./src/runtime_src/tools/scripts/xrtdeps.sh

cd build
./build.sh

cd Release
sudo yum reinstall xrt_*.rpm -y
```

# Centos/RHEL/AL2 pre-built RPM install steps


```bash
curl -s <xrt rpm link from above table> -o xrt.rpm
curl -s <xrt-aws rpm link from above table> -o xrt-aws.rpm
sudo yum reinstall xrt*.rpm -y
```

# FAQ

*Q:* What should I do if I see this message when I run the host application: ```xclProbe found 1 FPGA slots with xocl driver running
WARNING: AwsXcl - Cannot open userPF: /dev/dri/renderD0
WARNING: AwsXcl isGood: invalid user handle.
WARNING: xclOpen Handle check failed
device[0].user_instance : 0
WARNING: AwsXcl - Cannot open userPF: /dev/dri/renderD0
WARNING: AwsXcl isGood: invalid user handle.
ERROR: xclOpen Handle check failed```

This means that the XOCL driver hasn't been able to bind to the User PF. Please try to restart MPD: `sudo systemctl restart mpd`

*Q:* How do I verify that my device is usable?:
Use the Xilinx `xbutil` utility. If you sourced the `vitis_runtime_setup.sh` script, it should be available in your path.

```
xbutil scan
INFO: Found total 1 card(s), 1 are usable
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
System Configuration
OS name:      Linux
Release:      3.10.0-1062.4.1.el7.x86_64
Version:      #1 SMP Fri Oct 18 17:15:30 UTC 2019
Machine:      x86_64
Model:        HVM domU
CPU cores:    8
Memory:       122724 MB
Glibc:        2.17
Distribution: CentOS Linux 7 (Core)
Now:          Thu Jan 30 03:29:45 2020
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
XRT Information
Version:      2.3.0
Git Hash:     42da4cceb02e0386e0daeaea230bdc86ea40d19a
Git Branch:   2019.2
Build Date:   2020-01-30 02:56:41
XOCL:         2.3.0,42da4cceb02e0386e0daeaea230bdc86ea40d19a
XCLMGMT:      unknown
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 [0] 0000:00:1d.0 xilinx_aws-vu9p-f1_dynamic_5_0(ts=0xabcd) user(inst=128) 
```

An unusable device will show up like this:
```
xbutil scan
INFO: Found total 1 card(s), 1 are usable
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
System Configuration
OS name:      Linux
Release:      3.10.0-1062.4.1.el7.x86_64
Version:      #1 SMP Fri Oct 18 17:15:30 UTC 2019
Machine:      x86_64
Model:        HVM domU
CPU cores:    8
Memory:       122724 MB
Glibc:        2.17
Distribution: CentOS Linux 7 (Core)
Now:          Thu Jan 30 03:29:45 2020
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
XRT Information
Version:      2.3.0
Git Hash:     42da4cceb02e0386e0daeaea230bdc86ea40d19a
Git Branch:   2019.2
Build Date:   2020-01-30 02:56:41
XOCL:         2.3.0,42da4cceb02e0386e0daeaea230bdc86ea40d19a
XCLMGMT:      unknown
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
*[0] 0000:00:1d.0 xilinx_aws-vu9p-f1_dynamic_5_0(ts=0xabcd) user(inst=128)
WARNING: card(s) marked by '*' are not ready, is MPD runing? run 'systemctl status mpd' to check MPD details.```
```

# Additional Documentation
* [XRT Documentation](https://xilinx.github.io/XRT/master/html/)

* [XRT MPD Documentation](https://xilinx.github.io/XRT/master/html/cloud_vendor_support.html)
