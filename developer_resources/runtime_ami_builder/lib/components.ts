import { CfnComponent } from 'aws-cdk-lib/aws-imagebuilder';
import { Construct } from 'constructs';
import { BlockDevice } from 'aws-cdk-lib/aws-ec2';
import { BASE_AMI_CONFIGS } from './types';
import * as YAML from 'yaml';

const getHomeDir = (user: string): string => {
  return `/home/${user}`;
};

const returnToScriptsDirCmd = (user: string): string => {
  return `cd ${locateAwsFpgaRepo(user)}/developer_resources/runtime_ami_builder/scripts`;
};

const locateAwsFpgaRepo = (user: string) => {
  return `"$(find ${getHomeDir(user)} -type d -not -path "*.git*" -name "aws-fpga*" -print -quit)"`;
};

const getPkgManager = (user: string): string => {
  return user === BASE_AMI_CONFIGS.ROCKY_8_10.user ? "dnf" : "apt";
};

export interface ComponentDefn {
  name: string;
  header: string;
  cmds: string[];
}

export const COMPONENTS = {
  prepareForAmiBuild: (user: string): ComponentDefn => ({
    name: "PrepareForAmiBuild",
    header: "Preparing for AMI build",
    cmds: [
      `echo "Installing dependencies!"`,
      `sudo ${getPkgManager(user)} install -y git`,
      `sudo ${getPkgManager(user)} install -y wget`,
      `sudo ${getPkgManager(user)} update -y`,
      user === BASE_AMI_CONFIGS.ROCKY_8_10.user
        ? `sudo dnf groupinstall -y "Development tools"`
        : "sudo apt install -y build-essential",
      `export HOME=${getHomeDir(user)}`,
      `cd $HOME`,
      `git config --system --add safe.directory $HOME`,
      `git clone https://github.com/aws/aws-fpga`,
      `git config --system --add safe.directory ${locateAwsFpgaRepo(user)}`,
      `echo "Basic utilities installed and FPGA Developer Kit cloned!"`,
      `echo "Proceeding to build the AMI!"`
    ]
  }),

  updateRockyPython: (user: string): ComponentDefn => ({
    name: "UpdateRockyPython",
    header: "Installing Python3",
    cmds: [
      returnToScriptsDirCmd(user),
      `. update_rocky_python.sh`,
    ]
  }),

  installAwsCli: (user: string): ComponentDefn => ({
    name: "InstallAwsCli",
    header: "Installing AWS CLI",
    cmds: [
      returnToScriptsDirCmd(user),
      `. install_aws_cli.sh`,
    ]
  }),

  displayStorage: (volumes: BlockDevice[]): ComponentDefn => {
    let commands: string[] = [];
    for (const [volNum, volume] of volumes.entries()) {
      const volumeLabel = volNum === 0 ? "Root volume" : `Volume ${volNum}`;
      commands.push(`echo "${volumeLabel} defined by ImageBuilder recipe:"`);
      commands.push(`echo "  Device Name: ${volume.deviceName!}"`);
      commands.push(`echo "  Size: ${volume.volume.ebsDevice!.volumeSize!} GiB"`);
      commands.push(`echo "  Type: ${volume.volume.ebsDevice!.volumeType!}"`);
    }
    commands.push(`df -h /`, `lsblk`);
    return {
      name: "DisplayStorage",
      header: "Displaying Storage Volumes",
      cmds: commands
    };
  },

  installAwsFpgaSdk: (user: string): ComponentDefn => ({
    name: "InstallAwsFpgaSdk",
    header: "Installing AWS FPGA SDK",
    cmds: [
      `cd ${locateAwsFpgaRepo(user)}`,
      `. sdk_setup.sh`
    ]
  }),

  installF2RuntimeUtils: (user: string): ComponentDefn => ({
    name: "InstallF2RuntimeUtils",
    header: "Installing F2 Runtime Utilities",
    cmds: [
      returnToScriptsDirCmd(user),
      `. install_f2_runtime_utils.sh`
    ]
  }),

  installVivadoLabEdition: (user: string, toolVersion: string): ComponentDefn => ({
    name: "InstallVivadoLabEdition",
    header: "Installing Vivado Lab Edition",
    cmds: [
      returnToScriptsDirCmd(user),
      `. install_vivado_lab_edition.sh -v ${toolVersion}`
    ]
  }),

  installXilinxVirtualCable: (user: string, toolVersion: string): ComponentDefn => ({
    name: "InstallXilinxVirtualCable",
    header: "Installing Xilinx Virtual Cable",
    cmds: [
      returnToScriptsDirCmd(user),
      `export HOME=${getHomeDir(user)}`,
      `. install_xilinx_virtual_cable.sh -v ${toolVersion}`
    ]
  }),

  installXdmaDriver: (user: string, deviceNumber: string): ComponentDefn => ({
    name: "InstallXdmaDriver",
    header: "Installing XDMA Driver",
    cmds: [
      `export HOME=${getHomeDir(user)}`,
      returnToScriptsDirCmd(user),
      `. install_xdma_driver.sh -d ${deviceNumber}`
    ]
  }),

  cleanupStage: (user: string): ComponentDefn => ({
    name: "CleanupStage",
    header: "Cleanup Stage",
    cmds: [
      `cd ${getHomeDir(user)}`,
      `sudo chown -R ${user}:${user} ./*`
    ]
  })
};

export const createComponentHeader = (message: string): string[] => {
  return [
    `echo "================================================================================="`,
    `echo "${message}"`,
    `echo "================================================================================="`,
  ];
};

export const createComponent = (
  scope: Construct,
  componentDefn: ComponentDefn,
): CfnComponent => {
  const uniqueIdentifier = scope.node.tryGetContext('ami-builder:unique-identifier');
  const version = scope.node.tryGetContext('ami-builder:image-recipe-version');
  return new CfnComponent(scope, `${uniqueIdentifier}${componentDefn.name}`, {
    name: componentDefn.name,
    platform: 'Linux',
    version,
    data: YAML.stringify({
      name: componentDefn.name,
      description: `${componentDefn.name} component for FPGA runtime AMI`,
      schemaVersion: '1.0',
      phases: [{
        name: 'build',
        steps: [{
          name: componentDefn.name,
          action: 'ExecuteBash',
          inputs: {
            commands: ['set -Eexuo pipefail', ...createComponentHeader(componentDefn.header).concat(componentDefn.cmds)]
          }
        }]
      }]
    })
  });
};
