# Create a Runtime AMI Starting with an Amazon Linux AMI or Ubuntu                          

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

* Using an instance running [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) or an on-premises machine with access to a Xilinx SDAccel Tools Installation, run the following:

````
   $ mkdir -p xlnxrte/lib/lnx64.o
   $ mkdir -p xlnxrte/runtime/bin
   $ cp $XIILNX_SDX/lib/lnx64.o/libstdc++.so* xlnxrte/lib/lnx64.o/.
   $ cp $XIILNX_SDX/lib/lnx64.o/libxilinxopencl.so xlnxrte/lib/lnx64.o/.
   $ cp $XIILNX_SDX/runtime/bin/xclbinsplit xlnxrte/runtime/bin         
   $ cp $XIILNX_SDX/runtime/bin/xclbincat xlnxrte/runtime/bin
````

* Copy xlnxrte directory created to $HOME on your Runtime Instance.


## 3. Install Runtime Drivers and run your FPGA accelerated application on your Runtime Instance. 
* Log back on to the Runtime Instance:

```
  $ export XILINX_SDX=$HOME/xlnxrte
````
* You should be able to [run your FPGA accelerated application as described here](https://github.com/aws/aws-fpga/tree/master/SDAccel#runonf1), without needing to launch a new F1 instance


## 4. Create your Runtime AMI based on your Instance.

* Once you have your application running you should be able to create a Runtime AMI based your Runtime Instance as specified [here](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/creating-an-ami-ebs.html).

## 5. Make Runtime AMI available on the AWS Marketplace

* Please see [Section 5 of the AWS Marketplace Seller's Guide](https://awsmp-loadforms.s3.amazonaws.com/AWS_Marketplace_-_Seller_Guide.pdf#page=19) for more details. 

