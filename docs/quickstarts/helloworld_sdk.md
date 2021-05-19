# "Hello World" example 

This lab covers the basics of using F1 instances and running a _hello world_ demo provided by Amazon. The development and simulation of the code can be done on a different type of EC2 instance (for example from the [M5 family or the C5 family](https://aws.amazon.com/ec2/instance-types/)). This would be ideal to limit costs. For simplicity, we have undergone the whole lab on a F1 FPGA-equipped instance.

The entire lab can be done through the command line or the AWS console.

The Hello World example will allow us to write to FPGA resgisters and then read them back. We are simulating switches and leds. The idea is to push a series of vdips (series of bits).The vdips are combined with a register through an “AND” function. The output is the vleds.


# 1. Creating an S3 bucket for the Amazon FPGA Image

Before launching and configuring an instance, we are going to create a S3 Bucket which will be needed for the generation of the “AFI” (Amazon FPGA Image). The bucket will contain a *.tar file and logs which are generated with the AFI creation service.

Go the AWS Console, choose the S3 service, and then create a bucket
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga01.png)

Complete with your preferred settings, also by choosing the region. We recommend the region to be the one where your F1 instance is running. In our case, it is eu-west-1.

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga02.png)
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga03.png)
# 2. Launching a F1 EC2 instance

Go on your AWS console. Choose “EC2” within the list of services:

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga04.png)
Click on “Launch Instance”:
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga05.png)
The next step is to choose the Amazon Machine Image (AMI) that you’d like to install on this EC2 instance. The one that we are interested in is the **FPGA Developer AMI.** You can search for it manually or access it through the AWS MarketPlace: [https://aws.amazon.com/marketplace/pp/Amazon-Web-Services-FPGA-Developer-AMI/B06VVYBLZZ](https://aws.amazon.com/marketplace/pp/Amazon-Web-Services-FPGA-Developer-AMI/B06VVYBLZZ)

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga06.png)

The following screen will appear. Click Continue.
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga07.png)
Choose the appropriate instance by filtering with “FPGA”. Note that the f1.2xlarge has one FPGA board whereas the F1.16XLarge has 8 FPGA boards. As previously noted in the introduction, we are performing everything on a F1 instance. In a production environment, you should ideally develop and simulate on another set of machines in order to reduce costs.
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga08.png)

If you do not have a specific VPC and Subnet that you would like to use, leave the instance in the default VPC. Otherwise, choose the appropriate VPC + Subnet
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga09.png)

Choose the appropriate level of Storage :
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga10.png)


Skip the tags configuration.

In Security Group, use an existing Security group allowing port 22/TCP for SSH Access, or create a new one. By default, the group will be open to everyone (0.0.0.0/0). Make sure you restrict this access by specifying your IP or your network.

In addition to SSH on port 22/TCP, you can also decide to add here a rule for remote display protocol. For example, if you decide to remotely access your instance with NICE DCV, you would add the following rule : Add new Rule -> Protocol: TCP -> Port: 8443 with the same source as the ssh rule.

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga11.png)

Finally, click review and Launch. The console will give you the possibility to use an existing keypair or create one and then use it to connect to the instance through SSH :
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga12.png)
You can finally review the instance that has been created and connect to it unto its public IP by using your SSH client software, or through the command line. For example :

    ssh -i “xxx.pem” centos@ec2-xx-xxx-xxx-xxx.compute-1.amazonaws.com

or

    ssh –i “xxx.pem” centos@54.229.28.233

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga13.png)

Once you are connected to the instance, and in order to be able to directly use the AWS services run “**aws configure**” and then enter your access Key ID and Secret Access Key ID.

If you do not have an Access Key yet, go to the AWS Console click on the right top corner on your username
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga14.png)

And then select Access keys (access key ID and secret access key)
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga15.png)

After that, you should git clone the AWS FPGA repo with the command :

    git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR

The repo contains the SDK, HDK and code examples
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga16.png)
CD into the repo, then run

    source hdk_setup.sh

    source sdk_setup.sh

Note that this will take some minutes.

# 3. Synthesizing a Hello World example

Verify the examples that are available :
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga17.png)

Choose cl_hello_world and set the CL_DIR environment variable to the path of the example. You can off course choose and test other examples.

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga18.png)
The “vivado –mode batch” command allows you to make sure that Vivado is installed
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga19.png)

Next run the Vivado synthesis :
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga20.png)
Note that by default, the build runs in the background. It can be useful, especially because the build can take long (a few hours), to see the notification messages in the foreground. This can be done by adding to the .sh script the following : 

    -notify –foreground

# 4. Creating the Amazon FPGA Image

After synthesis, we are going to create the Amazon FPGA Image (AFI) from the specified design checkpoint (DCP).

To create the AFI, the DCP is stored on a S3 bucket. We’re going to use the S3 bucket that we initially created. If you haven’t done so already, you can make sure your credentials are setup correctly (aws configure).

In our case, we have created already a bucket named _fpganerd01_ with subfolders _dcp_ and _logs._ We will thus use the following command to copy the output files from the synthesis to the S3 bucket.

    aws s3 cp $CL_DIR/build/checkpoints/to_aws/*.Developer_CL.tar s3://fpganerd01/dcp/

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga21.png)
We can verify the content of the S3 bucket and DCP folder
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga22.png)

In order to create the Amazon FPGA image (AFI), we use the following command

    aws ec2 create-fpga-image --name <afi-name> --description <afi-description> --input-storage-location Bucket=<dcp-bucket-name>,Key=<path-to-tarball> --logs-storage-location Bucket=<logs-bucket-name>,Key=<path-to-logs>

which, in our example, becomes

    aws ec2 create-fpga-image --name nerd-afi01 --description hello-world-example --input-storage-location Bucket=fpganerd01,Key=dcp/20_09_11-160100.Developer_CL.tar --logs-storage-location Bucket=fpganerd01,Key=logs

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga23.png)

The command outputs two identifiers for the AFI, one regional and the other global. You should write both of them down.

The AFI ID is the main ID that is used to manage the AFI though the AWS CLI and the AWS SDK APIs. The Global FPGA Image Identifier (AGFI ID) is used to refer to an AFI from within an F1 instance, for example to load it into or clear it from a FPGA slot.

Use the describe command to check if the AFI generation is done.

    aws ec2 describe-fpga-images --fpga-image-ids <AFI ID>

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga24.png)

Note the AFI state as “available”. The state needs to turn to available before we can load it to the FPGA. This can take 20 to 30 minutes.

# 5. Running the AFI on the F1 Instance
If you have done the previous steps on a general purpose machine, now is the time to connect to the F1 instance, with the same methodology as described in in the initial steps (SSH, cloning the repo, sourcing sdk_setup.sh).

In our case, we have synthesized the example directly on a F1 instance. We will thus continue directly on the same instance.

The `fpga-describe-local-image` command tells you which AFI is loaded onto a particular FPGA slot. In this particular case, we had a previously loaded AFI which we are going to clear.
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga25.png)

The command to clear the AFI from the slot is the following :

    sudo  fpga-clear-local-image -S 0

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga26.png)
Next, we load the new AFI to the FPGA slot, using the Global ID that we had earlier. We then verify that image the AFI is loaded correctly.

    sudo  fpga-load-local-image -S 0 -I <FpgaImageGlobalId>
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga27.png)
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga28.png)
In order to validate the example, we build a runtime application that matches the loaded AFI. The CL examples have their runtime software in $CL_DIR/software/runtime/

    cd $CL_DIR/software/runtime/

    make all

    sudo ./test_hello_world

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga29.png)
The result encourages you to perform different tests by modifying the Virtual DIP Switch.
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga30.png)
Or

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga31.png)
Or

![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga32.png)
And finally
![](https://aws-fpga-hdk-resources.s3.amazonaws.com/artifacts/images/quickstarts/hello_world/labfpga33.png)

We can summarize the example and our actions as follows :

 - We have written on the register 0xEFBEADDE: **1110111110111110 1010110111011110** (Cf. line 94 of the [test_hello_world.c code](https://github.com/aws/aws-fpga/blob/2fdf23ffad944cb94f98d09eed0f34c220c522fe/hdk/cl/examples/cl_hello_world/software/runtime/test_hello_world.c))
 - The virtual dips we are pushing are combined with the former register with an **AND** function (Cf. line 315 of the [cl_hello_world.sv](https://github.com/aws/aws-fpga/blob/2fdf23ffad944cb94f98d09eed0f34c220c522fe/hdk/cl/examples/cl_hello_world/design/cl_hello_world.sv#L315) code). In practice we are interacting with the last 16 bits of the register:

1010110111011110 **&** 1111111111111111 = 1010-1101-1101-1110 (first example above)

1010110111011110 & 0000000000000000 = 0000-0000-0000-0000 (second example above)
