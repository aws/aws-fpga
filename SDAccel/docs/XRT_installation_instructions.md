# Xilinx Runtime (XRT) and SDx Tool versions

* Xilinx Runtime versions match with the tool that you created your SDAccel AFI with. 
* We provide pre-built RPM's for Centos/RHEL and instructions for building XRT 
* Use the below table as reference to install and use the correct XRT version for your applications.

| Xilinx SDx Tool Version | XRT Release Tag | SHA | `xrt` and `xrt-aws` pre-built RPM's (Centos/RHEL) |
|---|---|---|---|
|2019.1| [2019.1.0.3](https://github.com/Xilinx/XRT/tree/2019.1.0.3) | 89e25d51313daac5c322dfb4e84707829306d3fe | [xrt_201910.2.2.0_7.7.1908-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.7.0/Patches/XRT_2019_1_0_3/xrt_201910.2.2.0_7.7.1908-xrt.rpm) [xrt_201910.2.2.0_7.7.1908-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.7.0/Patches/XRT_2019_1_0_3/xrt_201910.2.2.0_7.7.1908-aws.rpm) |
|2018.3| [2018.3_RC5](https://github.com/Xilinx/XRT/releases/tag/2018.3_RC5) | 8654da1f0d2bd196c9887bdcfe1479103a93e90a | [xrt_201830.2.1.0_7.6.1810-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.6.0/Patches/XRT_2018_3_RC5/xrt_201830.2.1.0_7.6.1810-xrt.rpm) [xrt_201830.2.1.0_7.6.1810-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.6.0/Patches/XRT_2018_3_RC5/xrt_201830.2.1.0_7.6.1810-aws.rpm) |
|2018.2| [2018.2_XDF.RC5](https://github.com/Xilinx/XRT/releases/tag/2018.2_XDF.RC5) | 65ffad62f427c0bd1bc65b6ea555a810295468b7 | [xrt_201802.2.1.0_7.5.1804-xrt.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-xrt.rpm) [xrt_201802.2.1.0_7.5.1804-aws.rpm](https://aws-fpga-developer-ami.s3.amazonaws.com/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-aws.rpm) |
|2017.4| N/A** | N/A** | N/A** |
** Use XOCL for 2017.4

# Centos/RHEL build and install steps

```bash
XRT_RELEASE_TAG=2019.1_RC2 # Substitute XRT_RELEASE_TAG=<TAG from above table>

git clone https://github.com/aws/aws-fpga.git

cd aws-fpga
source sdaccel_setup.sh
cd $SDACCEL_DIR/Runtime
export XRT_PATH="${SDACCEL_DIR}/Runtime/${XRT_RELEASE_TAG}"
git clone http://www.github.com/Xilinx/XRT.git -b ${XRT_RELEASE_TAG} ${XRT_PATH}

cd ${XRT_PATH}
sudo ./src/runtime_src/tools/scripts/xrtdeps.sh

cd build
scl enable devtoolset-6 bash
./build.sh

cd Release
sudo yum reinstall xrt_*.rpm -y
```

# Centos/RHEL pre-built RPM install steps

### 2019.1

```bash
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.7.0/Patches/XRT_2019_1_RC2/xrt_201910.2.2.0_7.6.1810-xrt.rpm -o xrt.rpm
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.7.0/Patches/XRT_2019_1_RC2/xrt_201910.2.2.0_7.6.1810-aws.rpm -o xrt-aws.rpm
sudo yum reinstall xrt*.rpm -y
```
### 2018.3

```bash
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.6.0/Patches/XRT_2018_3_RC5/xrt_201830.2.1.0_7.6.1810-xrt.rpm -o xrt.rpm
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.6.0/Patches/XRT_2018_3_RC5/xrt_201830.2.1.0_7.6.1810-aws.rpm -o xrt-aws.rpm  
sudo yum reinstall xrt*.rpm -y
```
### 2018.2

```bash
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-xrt.rpm -o xrt.rpm
curl -s https://aws-fpga-developer-ami.s3.amazonaws.com/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-aws.rpm -o xrt-aws.rpm
sudo yum reinstall xrt*.rpm -y
```
