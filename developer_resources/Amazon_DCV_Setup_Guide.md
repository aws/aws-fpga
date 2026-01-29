# Using EC2 Instances with a GUI

## Table of Contents

- [What is Amazon DCV?](#what-is-amazon-dcv)
- [Installing the Amazon DCV Server on an Amazon EC2 Instance](#installing-the-amazon-dcv-server-on-an-amazon-ec2-instance)
  - [Prerequisites](#prerequisites)
  - [Amazon DCV Server Installation](#amazon-dcv-server-installation)
  - [Post-Installation Checks](#post-installation-checks)
  - [Setting a Password for Your Sessions](#setting-a-password-for-your-sessions)
  - [Setting Security Rules to Allow Traffic on Port 8443](#setting-security-rules-to-allow-traffic-on-port-8443)
- [Amazon DCV Client Installation](#amazon-dcv-client-installation)
- [Basic Session Management](#basic-session-management)
  - [Quick Session Startup](#quick-session-startup)

## What is Amazon DCV?

[Amazon DCV](https://docs.aws.amazon.com/dcv/latest/adminguide/what-is-dcv.html) is a high-performance remote
display protocol that provides customers with a secure way to deliver remote desktops and application streaming
from any cloud or data center to any device, over varying network conditions. With Amazon DCV and Amazon EC2,
customers can run graphics-intensive applications remotely on EC2 instances and stream the results to simpler
client machines, eliminating the need for expensive dedicated workstations.

This guide helps customers developing for AWS F2 instances create a virtual desktop running on EC2 instances
based on the [FPGA Developer AMI](../User_Guide_AWS_EC2_FPGA_Development_Kit.md#fpga-developer-ami).
The FPGA Developer AMI has pre-installed tools which are license free. Combined with DCV, this enables
development using Vivado or Vitis' graphical Integrated Design Environment (IDE), which provides an intuitive
graphical user interface (GUI) to visualize FPGA development in the cloud.

## Installing the Amazon DCV Server on an Amazon EC2 Instance

### Prerequisites

1. [Instance and IAM Configuration for DCV Licensing](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-license.html#dcv-lic-req)
2. [Dependency Installation](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-installing-linux-prereq.html#linux-prereq-gui)
    - :warning: DO NOT PERFORM STEP 3! Upgrading may impact the stability of development kit software!
3. [Protocol Setup](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-installing-linux-prereq.html#linux-prereq-wayland)
4. [Driver Installation and Setting Virtual Display Resolution](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-installing-linux-prereq.html#linux-prereq-nongpu)

### Amazon DCV Server Installation

In the [install procedure described here](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-installing-linux-server.html#linux-server-install), follow steps 1 through 5, 7, and 8.
When you get to step 9, do the following:

``` bash
    sudo apt --fix-broken install
    sudo apt install -y mesa-utils
    sudo dpkg -i nice-dcv-gl_2024.0.1096-1_amd64.ubuntu<2404 or 2004>.deb
```

### Post-Installation Checks

[This section of the post-installation check](https://docs.aws.amazon.com/dcv/latest/adminguide/setting-up-installing-linux-checks.html#checks-xserver) should be run to ensure that all aspects of the setup are working as expected.

### Setting a Password for Your Sessions

In order to connect to an Amazon DCV session, you must have a password set for your user on the EC2 instance.
This can be done with this command:

``` bash
sudo passwd $USER
```

### Setting Security Rules to Allow Traffic on Port 8443

In order for Amazon DCV to communicate with your EC2 instance, TCP and UDP traffic must be allowed on port 8443.
This can be accomplished by updating the security group you used to launch your instance.

## Amazon DCV Client Installation

The [Amazon DCV client](https://www.amazondcv.com/) should be installed on your local machine and is used to view your virtual desktop on your EC2 instance.

## Basic Session Management

To begin, run the following two commands:

``` bash
sudo systemctl isolate multi-user.target (Ubuntu 20.04 only)
sudo systemctl restart dcvserver.service
sudo systemctl restart dcvsessionlauncher.service
```

Next, refer to the [session management user guide here](https://docs.aws.amazon.com/dcv/latest/adminguide/managing-sessions.html). This guide will provide you with all of the information you need to customize and manage your Amazon DCV sessions.

### Quick Session Startup

To start a session, use the following command:

``` bash
dcv create-session $your_session_number
dcv list-sessions
Session: '1' (owner:ubuntu type:virtual)
```

You may give your session any number you like, but no two sessions may have the same number.

From this point, you can access your session using the Amazon DCV client on your local machine or via the [DCV console in your web browser](https://docs.aws.amazon.com/dcv/latest/userguide/using-connecting-browser-connect.html).

Enter `https://user@ec2_instance_ip_address:8443` into the `Hostname or IP Address` box and click `Connect`. Next, click "Trust and Connect".

Enter the password you set in [Post-Installation Checks](#post-installation-checks) in the `Password` box and click `Login`.

At this point, you should see your session begin and a virtual desktop displayed after a brief delay.

Any popups about not having a license may be safely ignored. This is a known issue with DCV.

Now, open a terminal and run the following command: `source /etc/profile.d/default_module.sh`. You're now ready to use your GUI-enabled EC2 Instance.

``` bash
ubuntu@ip-1-2-3-4:~$ source /etc/profile.d/default_module.sh
ubuntu@ip-1-2-3-4:~$ vivado -version
vivado v2024.1 (64-bit)
```
