# Installing SDX 2018.2 tool patch AR71715

## AWS FPGA Developer AMI 
 
 On an instance using FPGA Developer AMI 
 
 * Checkout latest AWS FPGA Developer Kit. 
 * Source [hdk_setup.sh](../../hdk_setup.sh) or [sdaccel_setup.sh](../../sdaccel_setup.sh) 
 * This will automatically download and install the patch.
 * You can verify the patch is installed by running the below command and checking the contents.
     
      ```
        ls -lrt $XILINX_SDX/patches/AR71715
        
      ```

## On premise machine
  
  * **You will need root permissions to be able to install the patch.**
  * Checkout latest AWS FPGA Developer Kit version.
  * Source [hdk_setup.sh](../../hdk_setup.sh) or [sdaccel_setup.sh](../../sdaccel_setup.sh) 
  * This will automatically download and install the patch.
  * You can verify the patch is installed by running the below command and checking the contents.
     
      ```
        ls -lrt $XILINX_SDX/patches/AR71715
        
      ```
  
 ## Manual install
 
 ### Pre-requisites
 
  * **You will need root permissions to be able to install the patch.**
  * Set environment variable `XILINX_SDX` to your SDx installation directory.
  
 ### Download and Install
  
  * Run following commands to download and install the patch
  
 ```
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/AR71715.zip -o AR71715.zip
   sudo mkdir -p $XILINX_SDX/patches
   sudo unzip AR71715.zip -d $XILINX_SDX/patches/AR71715
   sudo cp $XILINX_SDX/scripts/ocl/ocl_util.tcl $tool_dir/scripts/ocl/ocl_util.tcl.bkp
   sudo cp -f $XILINX_SDX/patches/AR71715/sdx/scripts/ocl/ocl_util.tcl $XILINX_SDX/scripts/ocl/ocl_util.tcl
   chmod -R 755 $XILINX_SDX/patches/AR71715
   
  ```
   
 
# Installing Xilinx Runtime (XRT) 2018.2_XDF.RC4
   
  Instructions to install XRT on Centos/RedHat & Ubuntu/Debian can be found [here](https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html).
  
  Xilinx Runtime (XRT) 2018.2_XDF.RC4 release can be found [here](https://github.com/Xilinx/XRT/tree/2018.2_XDF.RC4)
  
  ### Centos/RedHat Linux
  
  Run following commands to download and install XRT 2018.2_XDF.RC4 for 'Centos/RHEL' based distributions
  
  ```
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-xrt.rpm -o xrt_201802.2.1.0_7.5.1804-xrt.rpm
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-aws.rpm -o xrt_201802.2.1.0_7.5.1804-aws.rpm
   sudo yum reinstall -y xrt_201802.2.1.0_7.5.1804-xrt.rpm
   sudo yum reinstall -y xrt_201802.2.1.0_7.5.1804-aws.rpm
   
  ``` 
