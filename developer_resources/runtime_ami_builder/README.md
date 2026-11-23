# AWS EC2 F2 FPGA Runtime AMI Builder

After creating an Amazon FPGA Image (AFI), we suggest creating a runtime AMI using the Runtime AMI Builder (RAB). This tool was created to design an AMI to pair with specific accelerated application's needs. Use of the RAB offers the following benefits:

- **Reduced storage costs**
  - Smaller base image with reduced root-volume storage capacity
- **A Production-ready environment**
  - Install only what's needed to run a production accelerator design and host application
- **Flexibility and Extensibility**
  - Create components to install or use any software not included with the FPGA Developer Kit
- **Customizable deployment**
  - Automatically share runtime AMIs with AWS accounts in any region F2 instances are available

The RAB makes creating a runtime AMI for individual applications convenient by simplifying the use of the AWS CDK to create EC2 Image Builder pipelines. This guide demonstrates using the RAB on the FPGA Developer AMI to build a runtime AMI with the following tools installed:

- Python 3.12 (Rocky Linux only)
- The AWS CLI
- The AWS FPGA SDK (SDK)
- Runtime utilities for performance optimization
- Vivado Lab Edition (VLE)
- The Xilinx Virtual Cable driver (XVC)
- The XDMA driver, for designs built with the XDMA Shell

## Table of Contents

- [What is the AWS CDK?](#what-is-the-aws-cdk)
- [What Does Using the Runtime AMI Builder Cost?](#what-does-using-the-runtime-ami-builder-cost)
- [Running Individual Installation Scripts Locally](#running-individual-installation-scripts-locally)
- [AWS Account IAM Role Setup](#aws-account-iam-role-setup)
- [Installing Node.js](#installing-nodejs)
- [Installing AWS CDK Dependencies](#installing-aws-cdk-dependencies)
- [Customizing the Runtime AMI Build](#customizing-the-runtime-ami-build)
  - [Configuration and Resource Deployment](#configuration-and-resource-deployment)
  - [Choosing a Base AMI](#choosing-a-base-ami)
  - [Versioning the Image Recipe](#versioning-the-image-recipe)
  - [Choosing a Vivado Lab Edition Tool Version](#choosing-a-vivado-lab-edition-tool-version)
  - [Sizing AMI Storage](#sizing-ami-storage)
  - [Auto-Sharing with Other AWS Accounts](#auto-sharing-with-other-aws-accounts)
  - [Auto-Sharing in Specific Regions](#auto-sharing-in-specific-regions)
  - [Selecting a Build Instance Type](#selecting-a-build-instance-type)
  - [Customizing AMI Info](#customizing-ami-info)
  - [Selecting Components to Use in the Runtime AMI](#selecting-components-to-use-in-the-runtime-ami)
  - [XDMA Driver Installation](#xdma-driver-installation)
- [Bootstrapping, Deploying, and Running the Image Builder Pipeline](#bootstrapping-deploying-and-running-the-image-builder-pipeline)
  - [Bootstrap the CDK (First Deployment Only)](#bootstrap-the-cdk-first-deployment-only)
  - [Verify the Settings](#verify-the-settings)
  - [Deploy the Image Builder Pipeline](#deploy-the-image-builder-pipeline)
  - [Running the Image Builder Pipeline](#running-the-image-builder-pipeline)
  - [Cleaning Up Resources](#cleaning-up-resources)
- [Creating Custom Components](#creating-custom-components)
- [Issues and Support](#issues-and-support)
- [FAQ](#faq)

## What is the AWS CDK?

The Runtime AMI Builder uses the [**AWS Cloud Development Kit (CDK)**](https://docs.aws.amazon.com/cdk/v2/guide/home.html), which is a framework for defining cloud infrastructure as code through familiar programming languages. No prior knowledge about the CDK is needed to use this tool, but a basic understanding of these concepts will help:

- **CDK** converts the RAB's TypeScript code into AWS CloudFormation templates
- **CloudFormation** is AWS's service for creating and managing cloud resources
- **Bootstrapping** sets up the necessary CDK infrastructure in the deploying AWS account (one-time setup)
- **Synthesizing** shows what resources will be created without actually creating them
- **Deploying** creates the actual Image Builder pipeline and related resources

To create a runtime AMI build configuration, edit the settings in [lib/cdk.jsonc](./lib/cdk.jsonc) and, if needed, the component list in [lib/runtimeAmiBuilder.ts](./lib/runtimeAmiBuilder.ts). After that, only two commands are needed to deploy the EC2 Image Builder pipeline.

## What Does Using the Runtime AMI Builder Cost?

[The EC2 Image Builder is offered at no cost, other than the cost of the underlying AWS resources used to create, store, and share the images](https://aws.amazon.com/image-builder/faqs/). This means that the Image Builder pipeline and CloudFormation stack cost nothing to use or deploy.

- [Instance pricing](https://aws.amazon.com/ec2/pricing/)
- [EBS (instance-attached storage) pricing](https://aws.amazon.com/ebs/pricing/)
- [S3 storage pricing](https://aws.amazon.com/s3/pricing/?nc2=h_pr_s3)

## Running Individual Installation Scripts Locally

Before cloning the FPGA Developer Kit onto either base AMI, install `git`.
After the FPGA Developer Kit is cloned onto the base AMI, the installation scripts used by the RAB may be executed individually on the base AMI.
This greatly reduces iteration time before setting up an EC2 Image Builder pipeline.
Run the scripts from inside the cloned FPGA Developer Kit, because they use the repository to locate shared helper scripts.
If all components are being installed via local execution of the installer scripts, they must be run in this order to satisfy tool and package dependencies:

1. [install_script_execution_essentials.sh](./scripts/install_script_execution_essentials.sh)
2. [update_rocky_python.sh](./scripts/update_rocky_python.sh)
3. [install_aws_cli.sh](./scripts/install_aws_cli.sh)
4. [install_f2_runtime_utils.sh](./scripts/install_f2_runtime_utils.sh)
5. [install_vivado_lab_edition.sh](./scripts/install_vivado_lab_edition.sh)
6. [install_xilinx_virtual_cable.sh](./scripts/install_xilinx_virtual_cable.sh)
7. [install_xdma_driver.sh](./scripts/install_xdma_driver.sh) (optional, see [XDMA Driver Installation](#xdma-driver-installation))
8. [sdk_setup.sh](./../../sdk_setup.sh) \(must be sourced\)

Refer to each script to see any necessary flags and arguments.

> install_xilinx_virtual_cable.sh tests the driver on every FPGA in the instance. On an instance without FPGAs, such as the build instance the Runtime AMI Builder uses, it installs the driver and skips the test.

## AWS Account IAM Role Setup

The RAB requires access to an AWS account's resources via an IAM role.
See [Setting Up IAM Roles for Use with the AWS EC2 FPGA Development Kit](../Setting_up_IAM_roles_for_devkit_use.md#runtime-ami-builder-permissions) for detailed instructions on creating and attaching the required IAM role.

## Installing NodeJS

The AWS CDK depends on `Node.js` to function. More information about [supported versions is available here](https://docs.aws.amazon.com/cdk/v2/guide/node-versions.html).

Install Node.js 20.19+, 22.13+, or 24+ from the [Node.js download page](https://nodejs.org/en/download). This guide uses `Linux` as the platform, `nvm` as the Node.js version manager, and `npm` as the package manager.

## Installing AWS CDK Dependencies

After installing Node.js, source the setup script to install the pinned CDK and project dependencies:

```bash
cd $path_to_fpga_developer_kit/developer_resources/runtime_ami_builder
. runtime_ami_builder_setup.sh
```

This will also set the `RAB_DIR` environment variable which is used later on in this guide.

## Customizing the Runtime AMI Build

### Configuration and Resource Deployment

The RAB can be configured via the `context` section of [lib/cdk.jsonc](./lib/cdk.jsonc). In this section are all of the values that can be adjusted to create a runtime AMI, along with descriptions of what they do. These context values also set the AWS account and region the CDK deploys the CloudFormation stack and EC2 Image Builder pipeline to:

- `ami-builder:deployment-account` - the AWS account that will own the deployed resources
- `ami-builder:deployment-region` - the region the resources are deployed in

> ⚠️ The account IDs shipped in [lib/cdk.jsonc](./lib/cdk.jsonc) (`109876543210` for `ami-builder:deployment-account` and `012345678901` for `ami-builder:sharing-accounts`) are placeholders. Replace them with real account IDs, or set `ami-builder:sharing-accounts` to `[]`, before deploying. Otherwise the runtime AMI will be shared with the placeholder account.

> Unless mentioned otherwise, all configuration discussed will take place in [lib/cdk.jsonc](./lib/cdk.jsonc).

### Choosing a Base AMI

Two default base AMIs are available: `ROCKY_8_10` (Rocky Linux 8.10) and `UBUNTU_24_04` (Ubuntu 24.04). Select one with `ami-builder:base-image`. The AMI configurations are defined in [lib/source_amis.json](./lib/source_amis.json) using their AMI IDs for `us-east-1`. To add and use a different base AMI, add an entry to [lib/source_amis.json](./lib/source_amis.json) with the new AMI's ID, its default login user, and a description, then set `ami-builder:base-image` to the new entry's name. The new AMI must be based on Rocky Linux or Ubuntu. We recommend choosing an AMI without a product code attached to it. To find an AMI without a product code, use the following command:

```bash
aws ec2 describe-images --filters "Name=name, Values=*OS_NAME_GOES_HERE*" --query 'Images[].[ImageId,Name,CreationDate,ProductCodes[0].ProductCodeId || `null`]' --output table | grep None
```

The `*`s to each side of the OS name are standard wild-card characters and will help yield the most results for the OS of interest.

> The AMI used as the base for the runtime AMI must exist in the region the CDK resources are deployed in.

### Versioning the Image Recipe

Image recipe versioning, as the name suggests, provides version control over image builder pipelines and components. The image recipe version, `ami-builder:image-recipe-version`, must be incremented between changes to any of the files used by the RAB.

### Choosing a Vivado Lab Edition Tool Version

Set the Vivado Lab Edition version with `ami-builder:vivado-version`. The RAB supports the 2025.1 and later versions listed in [supported_vivado_versions.txt](./../../supported_vivado_versions.txt) at the root of the FPGA Developer Kit, currently 2025.1 and 2025.2. The two default base AMIs are supported by [Vivado Lab Edition 2025.2](https://docs.amd.com/r/en-US/ug973-vivado-release-notes-install-license/Supported-Operating-Systems).

If Vivado Lab Edition is not required, remove both the `installVivadoLabEdition` and `installXilinxVirtualCable` components from `componentConfigs` in [lib/runtimeAmiBuilder.ts](./lib/runtimeAmiBuilder.ts). The Xilinx Virtual Cable driver is installed from Vivado Lab Edition, so its component fails without it. Leave `ami-builder:vivado-version` set to a supported version.

### Sizing AMI Storage

Set the runtime AMI's root volume size in GiB with `ami-builder:root-volume-size`. The minimum is 32 GiB. The volume type and encryption are set with `ami-builder:root-volume-type` and `ami-builder:root-volume-encrypted`. Root volume sizing provides precise [storage cost control](https://aws.amazon.com/ebs/pricing/).

### Auto-Sharing with Other AWS Accounts

Add any AWS accounts to be granted launch permissions for the runtime AMI to `ami-builder:sharing-accounts`. This does **not** grant the target accounts ownership of it. If no other accounts need to be granted launch permissions, set this value to `[]`.

### Auto-Sharing in Specific Regions

Distribution of the runtime AMI to the regions in `ami-builder:distribution-regions` is handled automatically as part of the EC2 Image Builder pipeline. Only regions where F2 instances are available are accepted. This makes the runtime AMI available in the specified regions for only the deploying account and the accounts granted launch permissions above. If the runtime AMI is not needed in regions other than the deployment one, set the value to `[]`.

### Selecting a Build Instance Type

Set the build instance types with `ami-builder:build-instance-types`. The instance type and size chosen will affect the speed of the runtime AMI build. [Instance type pricing can be seen here](#what-does-using-the-runtime-ami-builder-cost).

### Customizing AMI Info

The AMI's name prefix, unique identifier, description, and tags are set with `ami-builder:name-prefix`, `ami-builder:unique-identifier`, `ami-builder:description`, and `ami-builder:tags`.

> Spaces aren't allowed in the unique identifier field.

### Selecting Components to Use in the Runtime AMI

Edit the `componentConfigs` list in [lib/runtimeAmiBuilder.ts](./lib/runtimeAmiBuilder.ts) to choose which components will be installed on the runtime AMI. By default, every component in this guide is included. With the default `ami-builder:cl-device-number`, the XDMA component only prepares the driver source. See [XDMA Driver Installation](#xdma-driver-installation). If the runtime AMI is for a design built with the Small Shell, which has no DMA engine, remove the `installXdmaDriver` component.

### XDMA Driver Installation

Designs built with the XDMA Shell need the XDMA driver to use the shell's DMA engine. The `installXdmaDriver` component runs [install_xdma_driver.sh](./scripts/install_xdma_driver.sh) with the device ID set in `ami-builder:cl-device-number`. The value must be a 4-digit hex value with the `0x` prefix, such as `"0xf001"`. The `cdk synth` and `cdk deploy` commands stop with an error otherwise. When running the script directly, pass the device ID with the required `-d` option. See [XDMA Driver Installation Instructions](./../../hdk/docs/XDMA_Install.md) for how to find the device ID of a CL.

- **Device ID set** (for example `"0xf001"`): the driver is built, installed, and loaded during the AMI build, and binds to FPGAs running an AFI with that device ID.
- **Default device ID** (`"0x0000"`): the driver source is prepared in `~/dma_ip_drivers/XDMA/linux-kernel/xdma/` on the runtime AMI, but not built. `cdk synth` and `cdk deploy` print a notice about this. To finish the install on an instance launched from the runtime AMI, run these steps from that directory:
  1. In `xdma_mod.c`, change the entry `{ PCI_DEVICE(0x1d0f, 0x0000), },` to use the CL's device ID, for example `{ PCI_DEVICE(0x1d0f, 0xf001), },`
  2. Run `sudo make clean`
  3. Run `sudo make install`
  4. Run `sudo modprobe xdma`

The driver is built for the kernel of the build instance. If an instance launched from the runtime AMI runs a different kernel, for example after a kernel update, rebuild the driver as described in the [XDMA Driver Installation Instructions](./../../hdk/docs/XDMA_Install.md). On Rocky Linux, the build updates the installed packages before it builds the driver, which can install a newer kernel than the one the driver is built for. If `modinfo -n xdma` reports `Module xdma not found` on an instance launched from the AMI, rebuild the driver on that instance.

> The XDMA and XRT `xocl` drivers cannot be installed on the same instance. Don't add components that install XRT to a runtime AMI that uses the XDMA driver.

## Bootstrapping, Deploying, and Running the Image Builder Pipeline

> If the Runtime AMI Builder IAM role has not yet been attached to the EC2 instance, this must be done before proceeding.

The EC2 Image Builder Pipeline is now ready for deployment. The following commands should be run from within `aws-fpga/developer_resources/runtime_ami_builder/lib`:

### Bootstrap the CDK (First Deployment Only)

First, generate the CDK configuration from `cdk.jsonc`. This can be done from anywhere within `developer_resources/runtime_ami_builder`:

```bash
npx ts-node $RAB_DIR/scripts/buildConfig.ts
```

This converts the `cdk.jsonc` configuration into the standard `cdk.json` format that the CDK CLI expects. If `cdk.jsonc` or any of the files mentioned above have been edited, the image recipe version must be incremented. After the edit is made, re-run this command to ensure the changes will take effect.

Now the CDK can be bootstrapped:

```bash
cdk bootstrap
```

This sets up the necessary AWS infrastructure (S3 bucket, AMI distribution IAM roles, etc.) the CDK needs to deploy its resources. This is command only needs to be run once per AWS account/deployment-region combination.

On successful bootstrap, `✅  Environment aws://<deploying_aws_account_number_here>/<configured_deployment_region_here> bootstrapped` will be printed to the console.

### Verify the Settings

`cdk synth` emits a long-form display of all of the components, parameters, and distributions the runtime AMI will be built with and process.

```bash
cdk synth
```

It's especially useful for verifying that AMI launch permissions will be granted as expected:

```yaml
  F2RuntimeAMIDistributionConfig:
    Type: AWS::ImageBuilder::DistributionConfiguration
    Properties:
      Distributions:
        - AmiDistributionConfiguration:
            Name: f2-runtime-ami-{{imagebuilder:buildDate}}
            Description: F2 FPGA Runtime AMI - {{imagebuilder:buildDate}}
            AmiTags:
              Project: AWS-FPGA-F2
              Environment: Production
              ManagedBy: ImageBuilder
            LaunchPermissionConfiguration:
              UserIds:
                - "012345678901"
          Region: us-east-1
        - AmiDistributionConfiguration:
            Name: f2-runtime-ami-{{imagebuilder:buildDate}}
            Description: F2 FPGA Runtime AMI - {{imagebuilder:buildDate}}
            AmiTags:
              Project: AWS-FPGA-F2
              Environment: Production
              ManagedBy: ImageBuilder
            LaunchPermissionConfiguration:
              UserIds:
                - "012345678901"
          Region: us-west-2
      Name: F2RuntimeAMIDistributionConfig
```

Here, the AMI is being shared with the AWS account `012345678901` and is also being distributed to regions `us-east-1` and `us-west-2`.

### Deploy the Image Builder Pipeline

```bash
cdk deploy
```

Running this command creates:

- A CloudFormation stack
- EC2 Image Builder components and image recipe
- An EC2 Image Builder pipeline for repeatable and automated AMI builds

> A prompt will appear requesting permission to deploy these resources.

### Running the Image Builder Pipeline

Once the deployment completes, retrieve the EC2 Image Builder pipeline's ARN:

  1. Open the AWS EC2 Console in a browser
  2. In the search bar, type `EC2 Image Builder` and click on it
  3. Click on the link for the deployed pipeline's name

Next, use the `Pipeline ARN` on that page to run the pipeline from the CLI:

```bash
$ aws imagebuilder start-image-pipeline-execution --image-pipeline-arn <image_builder_arn_from_image_pipelines_page_in_ec2_console>
{
    "requestId": "01234567-0123-0123-0123-012345678901",
    "clientToken": "01234567-0123-0123-0123-012345678901",
    "imageBuildVersionArn": "arn:aws:imagebuilder:us-east-1:<deploying-aws-account-number>:image/<pipeline-identifier>/<Maj.Min.Pat/Iteration #>"
}
```

The combined command `cdk deploy && aws imagebuilder start-image-pipeline-execution` is very effective for making sure that the EC2 Image Builder pipeline runs the moment deployment completes, reducing iteration time.

To run the pipeline via the EC2 Console, refer back to the steps directly above, then do the following:

  1. On the `Actions` dropdown menu, select `Run pipeline`
  2. View the log stream provided for that build session

The CloudWatch log stream may be inspected from the EC2 Image Builder pipeline visited in the steps above. This provides a near-real-time view of the runtime AMI build's progress, as well as any errors it may encounter. A successful runtime AMI build using all of the components mentioned in this guide takes ~45 minutes. Once the runtime AMI has been built successfully, it is available for immediate use by the deploying account and all others it was shared with across all specified regions.

### Cleaning Up Resources

To delete the CloudFormation stack, EC2 Image Builder pipeline, and all of its components, run:

```bash
cdk destroy
```

This also allows starting over from version 1.0.0 when deploying a pipeline with the same name again.

## Creating Custom Components

If an application has a dependency that is not covered by the provided components, a custom component can be created to install that dependency or perform any other setup needed. The components are defined in the table called `COMPONENTS` in [lib/components.ts](./lib/components.ts). Each component has 3 parts: a `name`, a `header`, and `cmds`. These are the only values needed to define a new component. Components' commands are able to use TypeScript's template strings to substitute variables into them.

A component's commands are executed as bash commands during the AMI build. The EC2 Image Builder service may fail due to undefined variables when it's executing the Bash commands in a component. The EC2 Image Builder service requires all variables to be defined before being accessed to ensure reliable and reproducible builds. This is why variables are explicitly defined in the included component definitions and installer scripts.

Once the component has been created, add it to the `componentConfigs` list in [lib/runtimeAmiBuilder.ts](./lib/runtimeAmiBuilder.ts) for use in the runtime AMI build.

## Issues and Support

- [Open an issue on GitHub if](https://github.com/aws/aws-fpga/issues):
  - A code bug is found
  - A failure not due to the use of IAM roles or the AWS CDK itself is encountered
- [Open an issue on re:Post if](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development):
  - An issue with IAM roles, the AWS CDK, EC2 Image Builder, or CloudFormation has occurred

## FAQ

- It looks like the XVC PCIe driver isn't there after being installed in the pipeline. What should I do?
  - Run `sudo modprobe xilinx_xvc_pci_driver` to start the driver for the current session
