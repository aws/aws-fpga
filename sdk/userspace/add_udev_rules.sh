#!/bin/bash

#
# Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

set -x
source /tmp/sdk_root_env.exp
set +x
rm -f /tmp/sdk_root_env.exp
echo "Creating group ${AWS_FPGA_SDK_GROUP}"
getent group ${AWS_FPGA_SDK_GROUP} >/dev/null 2>&1
if [[ $? -eq 0 ]] ; then
	if [ -z ${AWS_FPGA_SDK_OVERRIDE_GROUP} ] ; then
		echo "Group ${AWS_FPGA_SDK_GROUP} already exists. Please export a non existent group name  to AWS_FPGA_SDK_GROUP or export AWS_FPGA_SDK_OVERRIDE_GROUP=y"
		exit 1
	fi
	echo "${AWS_FPGA_SDK_GROUP} already exists, will grant FPGA resource access to this group"
else
	groupadd  ${AWS_FPGA_SDK_GROUP}
	if [[ $? -ne 0 ]] ; then
		echo "Could not group ${AWS_FPGA_SDK_GROUP}"
		exit 1
	fi
fi

echo "Adding user ${SDK_NON_ROOT_USER} into group ${AWS_FPGA_SDK_GROUP}"
getent group ${AWS_FPGA_SDK_GROUP} | grep -qw ${SDK_NON_ROOT_USER}
if [[ $? -eq 0 ]] ; then
	echo "${SDK_NON_ROOT_USER} is already in group ${AWS_FPGA_SDK_GROUP}"
else
	usermod -a -G ${AWS_FPGA_SDK_GROUP} ${SDK_NON_ROOT_USER}
	if [[ $? -ne 0 ]] ; then
		echo "Could not add user ${SDK_NON_ROOT_USER} to group ${AWS_FPGA_SDK_GROUP}"
		exit 1
	fi
fi

# Fail on any unsucessful command
set -e
mkdir -p /opt/aws/bin
# Make a script that will be run to change permissions everytime
# udev rule for the DBDF is matched
echo "Installing permission fix script for udev"
cat >/opt/aws/bin/change-fpga-perm.sh<<EF
#!/bin/bash
set -x
setperm () {
  chmod g=u \$1
	if [[ x\$2 != "x" ]] ; then
		chmod a=u \$1
	fi
}
setgrp() {
	chown root:${AWS_FPGA_SDK_GROUP} \$1
}
setfpgaperm () {
  for f in \$1/*; do
    setperm \$f;
		setgrp \$f
  done
}

devicePath=/sys/bus/pci/devices/\$1
grep -q "0x058000" \$devicePath/class && setfpgaperm "\$devicePath"
setperm /sys/bus/pci/rescan all
EF
chmod 544 /opt/aws/bin/change-fpga-perm.sh

DBDFs=`lspci -Dn |  grep -Ew "1d0f:1042|1d0f:1041" | awk '{print $1}' | sed ':x;N;$!bx;s/\n/ /g'`
minor=0

  rm -f /tmp/9999-presistent-fpga.rules
  for d in $DBDFs ; do
    echo "KERNEL==\"*${d}*\", RUN+=\"/opt/aws/bin/change-fpga-perm.sh '${d}'\"" >> /tmp/9999-presistent-fpga.rules
  done
  for d in $DBDFs ; do
    echo "KERNEL==\"*${d}*\", ACTION==\"add\", RUN+=\"/opt/aws/bin/change-fpga-perm.sh '${d}'\"" >> /tmp/9999-presistent-fpga.rules
  done
  echo "Adding udev rule: 9999-presistent-fpga.rules"
  cp /tmp/9999-presistent-fpga.rules /etc/udev/rules.d/9999-presistent-fpga.rules

## Test the rules for any issues
for d in  $DBDFs ; do
udevadm test --action="add" /sys/bus/pci/devices/${d} >/dev/null 2>&1
done
#
## Make udev daemon aware of rule changes
udevadm control --reload
#
## Trigger the change for rules to avoid a reboot
for d in  $DBDFs ; do
udevadm trigger --action="add"  /sys/bus/pci/devices/${d}
done
