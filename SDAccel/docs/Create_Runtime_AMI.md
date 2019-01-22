# Create a Runtime AMI Starting with an Amazon Linux AMI or Ubuntu                          

## Runtime AMI Compatability Table

  | SDx Version used for AFI Development |	Compatible SDAccel Runtime |
  |--------------------------------------|-----------------------------|
  | 2017.4 |	Runtime installed by sourcing "sdaccel_setup.sh" while using HDK Ver 1.4.X when environment variable    RELEASE_VER=2017.4 |
  | 2018.2 |	AWS FPGA Developer AMI 1.5.0 ( XRT is pre-installed) or [Runtime installed with XRT Version 2.1.0](https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html) |

## 1. Launch a Runtime Instance & Install Required Packages 

### Using Amazon Linux

* Launch an F1 instance using an [Amazon Linux AMI](https://aws.amazon.com/marketplace/pp/B00635Y2IW)
* Install the required updates

````
  $ sudo yum update
````
* Reboot your Runtime Instance to ensure all updates are running.
* Install the required packages
````
  $ sudo yum install git
  $ sudo yum install gcc
  $ sudo yum install gcc-c++          
  $ sudo yum install kernel-headers   
  $ sudo yum install kernel-devel     
  $ sudo yum --enablerepo=epel install ocl-icd ocl-icd-devel opencl-headers
  $ sudo mkdir -p /etc/OpenCL/vendors/
````  

### Using Ubuntu

* Launch an F1 instance using an [Ubuntu 16.04 LTS](https://aws.amazon.com/marketplace/pp/B01JBL2I8U)
* Install the required updates
````
   $ sudo apt-get update  
````
* Reboot your Runtime Instance to ensure all updates are running.
* Install the required packages
````
  $ sudo apt-get install gcc
  $ sudo apt-get install g++          
  $ sudo apt-get install make
  $ sudo apt-get install linux-headers-`uname -r`   
  $ sudo apt-get install linux-libc-dev     
  $ sudo apt-get install ocl-icd-dev ocl-icd-libopencl1 opencl-headers ocl-icd-opencl-dev
  $ sudo mkdir -p /etc/OpenCL/vendors/
````  


## 2. Copy required Xilinx SDAccel Runtime Libraries to the Instance and Reboot your Runtime Instance. 

* Using an instance running [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) or an on-premises machine with access to a Xilinx SDAccel Tools Installation, first source $AWS_FPGA_REPO_DIR/sdaccel_setup.sh  and then run following commands:

* if using Ubuntu or debian distribution set GLIBPATH env variable to Ubuntu. If using any other OS distribution set GLIBPATH to default. 

* set env variable 'XLNXRTE' to intended runtime install directory path.

### **For Vivado SDX 2017.4**

````
   $ export GLIBPATH= <Ubuntu or default -- see note above>
   $ export XLNXRTE=<your runtime install directory path>
   $ mkdir  -p $XLNXRTE/runtime/platforms/$(DSA)/driver
   $ mkdir -p $XLNXRTE/lib/lnx64.o
   $ mkdir -p $XLNXRTE/runtime/bin
   $ mkdir -p $XLNXRTE/runtime/lib/x86_64
   $ cp $SDACCEL_DIR/userspace/src2/libxrt-aws.so $XLNXRTE/runtime/platforms/xilinx_aws-vu9p-f1-04261818_dynamic_5_0/driver/
   $ cp $SDACCEL_DIR/tools/awssak2/xbsak $XLNXRTE/runtime/bin/
   $ cp $XIILNX_SDX/lib/lnx64.o/$GLIBPATH/libstdc++.so* xlnxrte/lib/x86_64/
   $ cp $XIILNX_SDX/runtime/bin/xclbinsplit xlnxrte/runtime/bin/
   $ cp $XIILNX_SDX/runtime/bin/xclbincat xlnxrte/runtime/bin/
   $ cp $SDACCEL_DIR/aws_platform/xilinx_aws-vu9p-f1-04261818_dynamic_5_0/sw/lib/x86_64/libxilinxopencl.so $XLNXRTE/runtime/lib/x86_64/
   $ cp /opt/Xilinx/SDx/2017.4.rte.dyn/setup.sh $XLNXRTE/
   $ cp /opt/Xilinx/SDx/2017.4.rte.dyn/setup.csh $XLNXRTE/
````
* You may need to update path in $XLNXRTE/setup.sh and $XLNXRTE/setup.csh script to match your runtime instance.
* Copy $XLNXRTE directory created to $HOME on your Runtime Instance.

### **For Vivado SDX 2018.2** 

 please refer to [Installing the Xilinx Runtime](https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html) for instructions on how to install runtime on your AMI.
 
 
## 3. Install Runtime Drivers and run your FPGA accelerated application on your Runtime Instance. 
* Log back on to the Runtime Instance:

```
  $ export XILINX_SDX=$HOME/$XLNXRTE
````
* You should be able to [run your FPGA accelerated application as described here](https://github.com/aws/aws-fpga/tree/master/SDAccel#runonf1), without needing to launch a new F1 instance


## 4. Create your Runtime AMI based on your Instance.

* Once you have your application running you should be able to create a Runtime AMI based your Runtime Instance as specified [here](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/creating-an-ami-ebs.html).

## 5. Make Runtime AMI available on the AWS Marketplace

* Please see [Section 5 of the AWS Marketplace Seller's Guide](https://awsmp-loadforms.s3.amazonaws.com/AWS_Marketplace_-_Seller_Guide.pdf#page=19) for more details. 

