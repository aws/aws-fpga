import { App, Stack, StackProps } from 'aws-cdk-lib';
import { BlockDevice, BlockDeviceVolume, EbsDeviceVolumeType, MachineImage } from 'aws-cdk-lib/aws-ec2';
import { InstanceProfile, ManagedPolicy, Role, ServicePrincipal } from 'aws-cdk-lib/aws-iam';
import {
  CfnDistributionConfiguration,
  CfnImagePipeline,
  CfnImageRecipe,
  CfnInfrastructureConfiguration,
} from 'aws-cdk-lib/aws-imagebuilder';
import { Construct } from 'constructs';
import { BASE_AMI_CONFIGS, BaseImageConfig, VivadoLabEditionVersion } from './types';
import { COMPONENTS, createComponentHeader, createComponent } from './components';

export class RuntimeAmiBuilderStack extends Stack {
  private imageBuilderRole: Role;
  private instanceProfile: InstanceProfile;
  private imageRecipe: CfnImageRecipe;
  private infrastructureConfig: CfnInfrastructureConfiguration;
  private distributionConfig: CfnDistributionConfiguration;
  private imagePipeline: CfnImagePipeline;
  private uniqueIdentifier = Stack.of(this).node.tryGetContext('ami-builder:unique-identifier');

  constructor(scope: Construct, id: string, props?: StackProps) {
    super(scope, id);

    const baseAmi = BASE_AMI_CONFIGS[Stack.of(this).node.tryGetContext('ami-builder:base-image') as keyof typeof BASE_AMI_CONFIGS];
    const user = baseAmi.user;
    const components: { componentArn: string }[] = [];
    const rootVolume = {
      deviceName: '/dev/sda1',
      volume: BlockDeviceVolume.ebs(
        Stack.of(this).node.tryGetContext('ami-builder:root-volume-size'),
        {
          volumeType: Stack.of(this).node.tryGetContext('ami-builder:root-volume-type'),
          deleteOnTermination: true,
          encrypted: Stack.of(this).node.tryGetContext('ami-builder:root-volume-encrypted') as boolean,
        }
      )
    };
    const vivadoToolVersion = Stack.of(this).node.tryGetContext('ami-builder:vivado-version')
    const componentConfigs = [
      COMPONENTS.prepareForAmiBuild(user),
      ...(user === BASE_AMI_CONFIGS.ROCKY_8_10.user ? [COMPONENTS.updateRockyPython(user)] : []),
      COMPONENTS.installAwsCli(user),
      COMPONENTS.displayStorage([rootVolume]),
      COMPONENTS.installF2RuntimeUtils(user),
      COMPONENTS.installAwsFpgaSdk(user),
      COMPONENTS.installVivadoLabEdition(user, vivadoToolVersion),
      COMPONENTS.installXilinxVirtualCable(user, vivadoToolVersion),
      COMPONENTS.cleanupStage(user)
    ];
    componentConfigs.forEach((componentDefn) => {
      const component = createComponent(this, componentDefn);
      components.push({
        componentArn: component.attrArn
      });
    });

    const ebsDevice = rootVolume.volume.ebsDevice!;
    const volumeType = ebsDevice.volumeType!;

    this.imageRecipe = new CfnImageRecipe(
      this,
      `${this.uniqueIdentifier}ImageRecipe`,
      {
        name: `${this.uniqueIdentifier}Recipe`,
        version: Stack.of(this).node.tryGetContext('ami-builder:image-recipe-version'),
        components: components,
        parentImage: baseAmi.amiId,
        blockDeviceMappings: [
          {
            deviceName: rootVolume.deviceName,
            ebs: {
              deleteOnTermination: ebsDevice.deleteOnTermination,
              encrypted: ebsDevice.encrypted as boolean,
              volumeSize: ebsDevice.volumeSize,
              volumeType: volumeType.toString(),
            },
          },
        ],
        workingDirectory: `/home/${baseAmi.user}`,
      }
    );

    const buildInstanceTypes = Stack.of(this).node.tryGetContext('ami-builder:build-instance-types');

    this.imageBuilderRole = new Role(this, `${this.uniqueIdentifier}ImageBuilderRole`, {
      roleName: `${this.uniqueIdentifier}ImageBuilderRole`,
      assumedBy: new ServicePrincipal('ec2.amazonaws.com'),
      managedPolicies: [
        ManagedPolicy.fromAwsManagedPolicyName('AmazonSSMManagedInstanceCore'),
        ManagedPolicy.fromAwsManagedPolicyName('EC2InstanceProfileForImageBuilder'),
        ManagedPolicy.fromAwsManagedPolicyName('AmazonS3FullAccess'),
      ],
    });

    this.instanceProfile = new InstanceProfile(this, `${this.uniqueIdentifier}InstanceProfile`, {
      instanceProfileName: `${this.uniqueIdentifier}InstanceProfile`,
      role: this.imageBuilderRole,
    });

    this.infrastructureConfig = new CfnInfrastructureConfiguration(
      this,
      `${this.uniqueIdentifier}InfrastructureConfig`,
      {
        name: `${this.uniqueIdentifier}InfrastructureConfig`,
        instanceTypes: buildInstanceTypes,
        instanceProfileName: this.instanceProfile.instanceProfileName,
      }
    );

    const sharingAccountIds = Stack.of(this).node.tryGetContext('ami-builder:sharing-accounts');
    const distributions = Stack.of(this).node.tryGetContext('ami-builder:distribution-regions').map((region: string) => ({
      region,
      amiDistributionConfiguration: {
        name: `${Stack.of(this).node.tryGetContext('ami-builder:name-prefix')}-{{imagebuilder:buildDate}}`,
        description: Stack.of(this).node.tryGetContext('ami-builder:description'),
        amiTags: Stack.of(this).node.tryGetContext('ami-builder:tags'),
        ...(sharingAccountIds?.length > 0 && {
          launchPermissionConfiguration: {
            userIds: sharingAccountIds,
          }
        }),
      }
    }));
    this.distributionConfig = new CfnDistributionConfiguration(
      this,
      `${this.uniqueIdentifier}DistributionConfig`,
      {
        name: `${this.uniqueIdentifier}DistributionConfig`,
        distributions: distributions,
      }
    );

    this.imagePipeline = new CfnImagePipeline(
      this,
      `${this.imageRecipe.name}Pipeline`,
      {
        name: `${this.imageRecipe.name}Pipeline`,
        imageRecipeArn: this.imageRecipe.attrArn,
        infrastructureConfigurationArn: this.infrastructureConfig.attrArn,
        imageTestsConfiguration: { imageTestsEnabled: true },
        imageScanningConfiguration: { imageScanningEnabled: false },
        distributionConfigurationArn: this.distributionConfig.attrArn,
      }
    );
  }
}


const app = new App();

const baseImage = app.node.tryGetContext('ami-builder:base-image');
const vivadoLabEditionVersion = app.node.tryGetContext('ami-builder:vivado-version');
const rootVolumeSize = app.node.tryGetContext('ami-builder:root-volume-size');
const rootVolumeType = app.node.tryGetContext('ami-builder:root-volume-type');
const encrypted = app.node.tryGetContext('ami-builder:root-volume-encrypted');
const distributionRegions = app.node.tryGetContext('ami-builder:distribution-regions');
const sharingAccountIds = app.node.tryGetContext('ami-builder:sharing-accounts');
const uniqueIdentifier = app.node.tryGetContext('ami-builder:unique-identifier');

if (!/^\d+\.\d+\.\d+$/.test(app.node.tryGetContext('ami-builder:image-recipe-version'))) {
  throw new Error('No image recipe version specified!');
}

if (!baseImage) {
  throw new Error('Missing required context: ami-builder:base-image');
}
if (!(baseImage in BASE_AMI_CONFIGS)) {
  throw new Error(`Invalid base AMI: '${baseImage}'`);
}

if (!vivadoLabEditionVersion) {
  throw new Error('Missing required context: ami-builder:vivado-version');
}
if (!Object.values(VivadoLabEditionVersion).includes(vivadoLabEditionVersion)) {
  throw new Error(`Invalid Vivado Lab Edition Version: '${vivadoLabEditionVersion}'`);
}

if (rootVolumeSize < 32) {
  throw new Error(`Runtime AMI requires >= 32GiB of root volume capacity! Capacity specified: ${rootVolumeSize}`);
}
if (!(Object.values(EbsDeviceVolumeType).includes(rootVolumeType))) {
  throw new Error(`Invalid root volume type: '${rootVolumeType}'`);
}
if (encrypted === undefined || !(encrypted === false || encrypted === true)) {
  throw new Error(`Root volume encryption selection must be a boolean: '${encrypted}'`);
}

if (sharingAccountIds) {
  sharingAccountIds.forEach((id: string) => {
    if (!/^\d{12}$/.test(id)) {
      throw new Error(`AWS IDs must be 12 digit values: '${id}'`);
    }
  });
}
const f2Regions = [
  'ap-south-1',
  'eu-central-1',
  'us-east-1',
  'eu-west-2',
  'ap-northeast-1',
  'us-west-2',
  'ap-southeast-1',
  'ap-southeast-2',
  'ca-central-1'
];
if (!Array.isArray(distributionRegions)) {
  throw new Error('Distribution regions must be specified as an array!');
}
distributionRegions.forEach((region: string) => {
  if (!f2Regions.includes(region)) {
    throw new Error(`Invalid distribution region: '${region}'. Must be one of: ${f2Regions.join(', ')}`);
  }
});

if (!app.node.tryGetContext('ami-builder:build-instance-types')) {
  throw new Error('No build instance types specified!');
}

if (!app.node.tryGetContext('ami-builder:name-prefix')) {
  throw new Error('No AMI name prefix specified!');
}

if (!uniqueIdentifier) {
  throw new Error('No unique identifier specified!');
}

if (!app.node.tryGetContext('ami-builder:description')) {
  throw new Error('No AMI description specified!');
}

const runtimeAmiBuilderStack = new RuntimeAmiBuilderStack(
  app,
  `${uniqueIdentifier}Stack`,
  {
    env: {
      account: app.node.tryGetContext('ami-builder:deployment-account'),
      region: app.node.tryGetContext('ami-builder:deployment-region')
    }
  }
);

export { runtimeAmiBuilderStack };
