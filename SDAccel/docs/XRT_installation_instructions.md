# XRT Installation Instructions

# Installing Xilinx Runtime (XRT) 2018.3 RC3 Patch 1

  * Applicable SDx Tool Version: 2018.3

  * XRT Release Tag:  2018.3.3.1 (SHA: 48cafdc100b29843fd013d371ffba0141db06b7a)
  
  * [Xilinx Runtime (XRT) 2018.3 RC3 Patch 1 release](https://github.com/Xilinx/XRT/releases/tag/2018.3.3.1)
  
 ### Instructions to build & install XRT
 
   Pre-requisite commands used to build XRT for AWS F1 platform for this release
   
  ```
    git clone http://www.github.com/aws/aws-fpga.git
    cd aws-fpga
    source sdaccel_setup.sh
    mkdir $SDACCEL_DIR/Runtime
    cd $SDACCEL_DIR/Runtime
    export XRT_PATH="${SDACCEL_DIR}/Runtime/XRT_20183rc3p1 "
    git clone http://www.github.com/Xilinx/XRT.git -b 2018.3.3.1 ${XRT_PATH}
    cd ${XRT_PATH}
    sudo ./src/runtime_src/tools/scripts/xrtdeps.sh
    cd build
    
  ```
  
  Follow [Xilinx's instructions to build & install XRT on Centos/Redhat & Ubuntu/Debian](https://xilinx.github.io/XRT/master/html/build.html#xrt-for-pcie-platforms) to build XRT for supported OS.
  
  ### Install on Centos/RedHat Linux using prebuilt RPM

 ```
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.6.0/Patches/XRT_2018_3_RC3_Patch1/xrt_201830.2.1.0_7.6.1810-xrt.rpm -o xrt_201830.2.1.0_7.6.1810-xrt.rpm
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.6.0/Patches/XRT_2018_3_RC3_Patch1/xrt_201830.2.1.0_7.6.1810-aws.rpm -o xrt_201830.2.1.0_7.6.1810-aws.rpm
   sudo yum remove -y xrt-aws
   sudo yum remove -y xrt
   sudo yum install -y xrt_201830.2.1.0_7.6.1810-xrt.rpm
   sudo yum install -y xrt_201830.2.1.0_7.6.1810-aws.rpm
   
  ```

# Installing Xilinx Runtime (XRT) 2018.2_XDF.RC4
   
  * Applicable SDx Tool Version: 2018.2

  * XRT Release Tag: 2018.2_XDF.RC4 (SHA: 343186f76f59edd01bc48d84cf67fe22a0a3f338)
   
  * [Xilinx Runtime (XRT) 2018.2_XDF.RC4 release](https://github.com/Xilinx/XRT/tree/2018.2_XDF.RC4)
  
  ### Instructions to build & install XRT
 
   Pre-requisite commands used to build XRT for AWS F1 platform for this release
   
  ```
    git clone http://www.github.com/aws/aws-fpga.git
    cd aws-fpga
 	source sdaccel_setup.sh
	mkdir $SDACCEL_DIR/Runtime
	cd $SDACCEL_DIR/Runtime
	export XRT_PATH="${SDACCEL_DIR}/Runtime/XRT_20182rc4"
	git clone http://www.github.com/Xilinx/XRT.git -b 2018.2_XDF.RC4 ${XRT_PATH}
	cd ${XRT_PATH}
	sudo ./src/runtime_src/tools/scripts/xrtdeps.sh
	cd build
	  
 ```
  Follow [ Xilinx's instructions to build & install XRT on Centos/RedHat & Ubuntu/Debian](https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html) to build XRT for supported OS.
    
  ### Install on Centos/RedHat Linux using prebuilt RPMs
  
  Run following commands to download and install XRT 2018.2_XDF.RC4 for 'Centos/RHEL'
  
  ```
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-xrt.rpm -o xrt_201802.2.1.0_7.5.1804-xrt.rpm
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/xrt_201802.2.1.0_7.5.1804-aws.rpm -o xrt_201802.2.1.0_7.5.1804-aws.rpm
   sudo yum remove -y xrt
   sudo yum install -y xrt_201802.2.1.0_7.5.1804-xrt.rpm
   sudo yum install -y xrt_201802.2.1.0_7.5.1804-aws.rpm
   
  ```

# Installing Xilinx Runtime (XRT) 2018.2_XDF.RC5
   
  * Applicable SDx Tool Version: 2018.2

  * XRT Release Tag: 2018.2_XDF.RC5 (SHA: 65ffad62f427c0bd1bc65b6ea555a810295468b7)
  
  * [Xilinx Runtime (XRT) 2018.2_XDF.RC5 release](https://github.com/Xilinx/XRT/releases/tag/2018.2_XDF.RC5)
  
 ### Instructions to build & install XRT
 
   Pre-requisite commands used to build XRT for AWS F1 platform for this release
    
  ```
    git clone http://www.github.com/aws/aws-fpga.git
    cd aws-fpga
 	source sdaccel_setup.sh
	mkdir $SDACCEL_DIR/Runtime
	cd $SDACCEL_DIR/Runtime
	export XRT_PATH="${SDACCEL_DIR}/Runtime/XRT_20182rc5 "
	git clone http://www.github.com/Xilinx/XRT.git -b 2018.2_XDF.RC5 ${XRT_PATH}
	cd ${XRT_PATH}
	sudo ./src/runtime_src/tools/scripts/xrtdeps.sh
	cd build
  
 ```
  Follow [ Xilinx's instructions to build & install XRT on Centos/RedHat & Ubuntu/Debian](https://www.xilinx.com/html_docs/xilinx2018_2_xdf/sdaccel_doc/ejy1538090924727.html) to build XRT for supported OS.
 
  ### Install on Centos/RedHat Linux using prebuilt RPMs
  
  Run following commands to download and install XRT 2018.2_XDF.RC5 for 'Centos/RHEL'
  
  ```
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-xrt.rpm -o xrt_201802.2.1.0_7.5.1804-xrt.rpm
   curl -s https://s3.amazonaws.com/aws-fpga-developer-ami/1.5.0/Patches/XRT_2018_2_XDF_RC5/xrt_201802.2.1.0_7.5.1804-aws.rpm -o xrt_201802.2.1.0_7.5.1804-aws.rpm
   sudo yum remove -y xrt-aws
   sudo yum remove -y xrt
   sudo yum install -y xrt_201802.2.1.0_7.5.1804-xrt.rpm
   sudo yum install -y xrt_201802.2.1.0_7.5.1804-aws.rpm
   
  ```
