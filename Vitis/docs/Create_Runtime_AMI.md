# Create a Runtime AMI Starting with Amazon Linux 2, Centos or Ubuntu                          

## Runtime AMI Compatibility Table

| Vitis Version used for AFI Development | Compatible Xilinx Runtime                                                                                          |
|----------------------------------------|--------------------------------------------------------------------------------------------------------------------|
| 2021.2                                 | AWS FPGA Developer AMI 1.12.x (XRT is pre-installed) or [XRT](https://xilinx.github.io/XRT/2021.2/html/build.html) |
| 2021.1                                 | AWS FPGA Developer AMI 1.11.x (XRT is pre-installed) or [XRT](https://xilinx.github.io/XRT/2021.1/html/build.html) |
| 2020.2                                 | AWS FPGA Developer AMI 1.10.x (XRT is pre-installed) or [XRT](https://xilinx.github.io/XRT/2020.2/html/build.html) |
| 2020.1                                 | AWS FPGA Developer AMI 1.9.x (XRT is pre-installed) or [XRT](https://xilinx.github.io/XRT/2020.1/html/build.html)  |
| 2019.2                                 | AWS FPGA Developer AMI 1.8.x (XRT is pre-installed) or [XRT](https://xilinx.github.io/XRT/2019.2/html/build.html)  |

## 1. Launch a Runtime Instance & Install Required Packages 

* Launch an F1 instance using [Centos 7](https://aws.amazon.com/marketplace/pp/B00O7WM7QW), Ubuntu or Amazon Linux 2 AMI's.

## 2. Install Runtime Drivers  
* Build XRT on either your runtime or a similar instance using the [XRT build steps](https://xilinx.github.io/XRT/2019.2/html/build.html).
* Install the XRT package on your runtime instance

## 3. Run your FPGA accelerated application on your Runtime Instance.
* Source the runtime setup script:
```
$ source /opt/xilinx/xrt/setup.sh
```
* Run application to verify that it works:
```bash
$ ./helloworld ./vector_addition.awsxclbin 
```
* You might want to add a link to the setup command: `/opt/xilinx/xrt/setup.sh` in the `/etc/profile.d` path to be able to setup on start.

## 4. Create your Runtime AMI based on your Instance.

* Once you have your application running you should be able to create a Runtime AMI based your Runtime Instance as specified [here](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/creating-an-ami-ebs.html).

## 5. Make Runtime AMI available on the AWS Marketplace

* Please see [Section 5 of the AWS Marketplace Seller's Guide](https://awsmp-loadforms.s3.amazonaws.com/AWS_Marketplace_-_Seller_Guide.pdf#page=19) for more details. 
