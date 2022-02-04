#!/bin/bash 

# Amazon FPGA Hardware Development Kit
#                                     
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#                                                                        
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is  
# located at                                                                 
#                                                                            
#    http://aws.amazon.com/asl/                                              
#                                                                            
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or  
# implied. See the License for the specific language governing permissions and
# limitations under the License.                                              

set -e

script=${BASH_SOURCE[0]}
full_script=$(readlink -f $script)
script_name=$(basename $full_script)

source $AWS_FPGA_REPO_DIR/shared/bin/set_common_functions.sh
source $AWS_FPGA_REPO_DIR/shared/bin/set_common_env_vars.sh
script_dir=$(dirname $full_script)


debug=0

function usage {
   info_msg "USAGE: $script_name [-h|-help] [-s3_bucket=<bucket_name>] [-s3_dcp_key=<S3_folder_of_dcp>] [-s3_logs_key=<S3_folder_of_logs>] [-xclbin=<xclbin_filename>] [-o=<awsxclbin_filename>] [-awsprofile=<aws_profile_name>]"                                                                                               
}                                                                                                              

function help {
  info_msg "$script_name"
  info_msg " "           
  info_msg "Vitis AFI Creation"
  info_msg " "                   
  info_msg "create_vitis_afi.sh assumes you have:"
  info_msg "  (*) Read the README on Github and understand the Vitis workflow (Vitis/README.md)"
  info_msg "  (*) Generated an XCLBIN using the Vitis Build flow"                                 
  info_msg "  (*) Ready to create an AFI and test on F1.  Your kernel has been validated using SW/HW Emulation."                                                                                                              
  info_msg "create_vitis_afi.sh will:"                                                                       
  info_msg "  (1) Extract three parts from your XCLBIN:  DCP (.dcp) , clocks data(.json) and build metadata (.json)"                           
  info_msg "  (2) Generates a Manifest file for AFI creation that sets the clocks based on your achieved target freq from your build"                                                                                         
  info_msg "  (3) Prepares tar file for AFI creation process"                                                  
  info_msg "  (4) Calls aws ec2 create-fpga-image"                                                             
  info_msg "  (5) Creates new XCLBIN (called AWSXCLBIN) that is composed of: Metadata and AGFI-ID"             
  echo " "                                                                                                     
  usage                                                                                                        
}                                                                                                              

if [ "$1" == "" ]
then             
    err_msg "Invalid usage"
    usage                  
    exit 1                 
fi                         

while [ "$1" != "" ]; do
    PARAM=`echo $1 | awk -F= '{print $1}'`
    VALUE=`echo $1 | awk -F= '{print $2}'`
    case $PARAM in                        
        -h | --help)                      
            help                          
            exit                          
            ;;                            
        -xclbin)                          
            xclbin=$VALUE                 
            ;;                            
        -o)                               
            awsxclbin=$VALUE              
            ;;                            
        -aws_profile_name)                
            aws_profile_name=$VALUE       
            ;;                            
        -s3_bucket)                       
            s3_bucket=$VALUE              
            ;;                            
        -s3_logs_key)                     
            s3_logs=$VALUE                
            ;;                            
        -s3_dcp_key)                      
            s3_dcps=$VALUE                
            ;;                            
        *)                                
            err_msg "Unknown parameter \"$PARAM\""
            usage                                 
            exit 1                                
            ;;                                    
    esac                                          
    shift                                         
done                                              

if [ "$RELEASE_VER" == "" ]
then
    err_msg "Env variable RELEASE_VER not set, did you source sdaccel_setup.sh?"
    exit 1
fi

if [[ -e "$xclbin" ]]
then                 
    info_msg "Found xclbin '$xclbin'"
else                                 
    err_msg "File '$xclbin' not found"
    exit 1                            
fi                                    

stripped_xclbin=$(basename $xclbin)
ext_xclbin=${stripped_xclbin##*.}  
stripped_xclbin=${stripped_xclbin%.*}

info_msg "$stripped_xclbin"

if [ "$awsxclbin" == "" ]
then                     
    awsxclbin=$stripped_xclbin
fi                            


if [ "$awsxclbin" != "$stripped_xclbin" ]
then                                     
    warn_msg "$awsxclbin does not match $stripped_xclbin"
    warn_msg "For github examples, -o <xclbin_filename> must be equal to $stripped_xclbin"
fi                                                                                        

if [[ -e "$awsxclbin" ]]
then                    
    err_msg "File '$awsxclbin' already exists"
    exit 1                                    
fi                                            

if [ ":$s3_bucket" == ":" ]
then                       
    err_msg "Invalid s3_bucket"
    usage                      
    exit 1                     
fi                             

# s3 logs is not required
# s3 dcp key is required 
if [ "$s3_dcps" == "" ]  
then                     
    err_msg "Invalid s3_dcps key"
    usage                        
    exit 1                       
fi                               

timestamp=$(date +"%y_%m_%d-%H%M%S")

#Steps
#1. Strip XCLBIN to get DCP for ingestion
#2. Create Manifest file                 
#3. Prepare ingestion tar file           
#4. Call create-fpga-image               
#5. Manipulate the AFI ID                
#6. Create awsxclbin                     

#STEP 1
#Strip XCLBIN to get DCP for ingestion
#/opt/xilinx/xrt/bin/xclbinsplit -o ${timestamp} $xclbin
/opt/xilinx/xrt/bin/xclbinutil --dump-section BUILD_METADATA:JSON:${timestamp}_build.json --dump-section CLOCK_FREQ_TOPOLOGY:JSON:${timestamp}_clocks.json --dump-section BITSTREAM:RAW:${timestamp}_SH_CL_routed.dcp -i $xclbin
if [[ -e "${timestamp}_SH_CL_routed.dcp" ]]
then
    info_msg "Split DCP from xclbin: ${timestamp}_SH_CL_routed.dcp"
else                                                          
    err_msg "File ${timestamp}_SH_CL_routed.dcp not found"         
    exit 1                                                    
fi                                                            
if [[ -e "${timestamp}_build.json" ]]                         
then                                                          
    info_msg "The build Metadata from xclbin: ${timestamp}_build.json"
else                                                               
    err_msg "File ${timestamp}_build.json not found"               
    exit 1                                                         
fi                                                                 
if [[ -e "${timestamp}_clocks.json" ]]                         
then                                                          
    info_msg "The clocks Metadata from xclbin: ${timestamp}_clocks.json"
else                                                               
    err_msg "File ${timestamp}_clocks.json not found"               
    exit 1                                                         
fi                                                                 

if [[ -d "to_aws" ]]
then                
    err_msg "Directory to_aws already exists"
    exit 1                                   
fi                                           

mkdir to_aws
cp ${timestamp}_SH_CL_routed.dcp ./to_aws/

#STEP 2
#Create Manifest file
strategy=DEFAULT     
hdk_version=$(grep 'HDK_VERSION' $script_dir/../../hdk/hdk_version.txt | sed 's/=/ /g' | awk '{print $2}')
shell_version=0x04261818
tool_version=v$RELEASE_VER
device_id=0xF010
vendor_id=0x1D0F                                                                                         
subsystem_id=0x1D51                                                                                      
subsystem_vendor_id=0xFEDD                                                                               
# Get XSA info from build metadata
vendor=$(echo `grep -A 6 dsa ./${timestamp}_build.json | grep vendor | sed 's/.*: "//g' | sed 's/",//'`)
board_id=$(echo `grep -A 6 dsa ./${timestamp}_build.json | grep board_id | sed 's/.*: "//g' | sed 's/",//'`)
plat_name=$(echo `grep -A 6 dsa ./${timestamp}_build.json | grep name | sed 's/.*: "//g' | sed 's/",//'`)
major=$(echo `grep -A 6 dsa ./${timestamp}_build.json | grep major | sed 's/.*: "//g' | sed 's/",//'`)
minor=$(echo `grep -A 6 dsa ./${timestamp}_build.json | grep minor | sed 's/.*: "//g' | sed 's/",//'`)
# Get clock info from clock metadata
clock_main_a0=$(echo `grep -B 1 SYSTEM ${timestamp}_clocks.json | grep -o -e '[0-9]*'`)
clock_extra_b0=$(echo `grep -B 2 DATA_CLK ${timestamp}_clocks.json | grep freq | grep -o -e '[0-9]*'`)
clock_extra_c0=$(echo `grep -B 2 KERNEL_CLK ${timestamp}_clocks.json | grep -o -e '[0-9]*'`)

if [[ "$vendor" != "xilinx" && "$board_id" != "aws-vu9p-f1" && "$plat_name" != "shell-v04261818" && "$major" != "201920" && "$minor" != "2" ]]
then                                 
    err_msg "Platform ${vendor}_${board_id}_${plat_name}_${major}_${minor} used to create xclbin is not correct, you should be using xilinx_aws-vu9p-f1_shell-v04261818_201920_3"
    exit                                                                                              
fi                                                                                                    

#Write Manifest File here
hash=$( sha256sum  to_aws/${timestamp}_SH_CL_routed.dcp | awk '{ print $1 }' )
manifest_file="${timestamp}_manifest.txt"                                     
exec 3<>$manifest_file                                                        
echo "manifest_format_version=2" >&3                                          
echo "pci_vendor_id=$vendor_id" >&3                                           
echo "pci_device_id=$device_id" >&3                                           
echo "pci_subsystem_id=$subsystem_id" >&3                                     
echo "pci_subsystem_vendor_id=$subsystem_vendor_id" >&3                       
echo "dcp_hash=$hash" >&3                                                     
echo "shell_version=$shell_version" >&3                                       
echo "dcp_file_name=${timestamp}_SH_CL_routed.dcp" >&3                        
echo "hdk_version=$hdk_version" >&3                                           
echo "tool_version=$tool_version" >&3                                               
echo "date=$timestamp" >&3                                                    
echo "clock_main_a0=$clock_main_a0" >&3                                       
echo "clock_extra_b0=$clock_extra_b0" >&3                                     
echo "clock_extra_c0=$clock_extra_c0" >&3                                     
exec 3>&-                                                                     
exec 3>&-                                                                     

if [[ -e "$manifest_file" ]]
then                        
    info_msg "Generated manifest file '$manifest_file'"
else                                                   
    err_msg "File '$manifest_file' not found"          
    exit 1                                             
fi                                                     
cp $manifest_file to_aws/$manifest_file                


#STEP 3
#Prepare ingestion
tar -cf ${timestamp}_Developer_Vitis_Kernel.tar to_aws/${timestamp}_SH_CL_routed.dcp to_aws/${timestamp}_manifest.txt                                                                                                       
#STEP 4
#Call create-fpga-image
profile_text=""        
if [ "$aws_profile_name" != "" ]
then                            
    profile_text="--profile ${aws_profile_name}"
fi                                              

log_storage_text=""
if [ "${s3_logs}" != "" ]
then
    log_storage_text="--logs-storage-location Bucket=${s3_bucket},Key=${s3_logs}"
fi

aws s3 ${profile_text} cp ${timestamp}_Developer_Vitis_Kernel.tar s3://${s3_bucket}/${s3_dcps}/
aws ec2 ${profile_text} create-fpga-image --name ${stripped_xclbin} --description ${stripped_xclbin} --input-storage-location Bucket=${s3_bucket},Key=${s3_dcps}/${timestamp}_Developer_Vitis_Kernel.tar ${log_storage_text} > ${timestamp}_afi_id.txt


#STEP 5
#Manipulate the AFI ID
test=`grep agfi ${timestamp}_afi_id.txt | awk -F: '{print $2}' | sed 's/ \"//g' | sed 's/\".*//g' | sed ':a;N;$!ba;s/\n/ /g'`
echo -n $test > ${timestamp}_agfi_id.txt
echo ${timestamp}_agfi_id.txt

#STEP 6
#Create .awsxclbin


if [[ "$RELEASE_VER" == "2020.2" || "$RELEASE_VER" == "2021.1" || "$RELEASE_VER" == "2021.2" ]]
then
	/opt/xilinx/xrt/bin/xclbinutil -i $xclbin --remove-section PARTITION_METADATA --replace-section BITSTREAM:RAW:${timestamp}_agfi_id.txt -o ${awsxclbin}.awsxclbin
else
	/opt/xilinx/xrt/bin/xclbinutil -i $xclbin --remove-section PARTITION_METADATA --remove-section SYSTEM_METADATA --replace-section BITSTREAM:RAW:${timestamp}_agfi_id.txt -o ${awsxclbin}.awsxclbin
fi                                              
