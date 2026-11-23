import {
  MachineImage,
  IMachineImage,
} from 'aws-cdk-lib/aws-ec2';
import * as fs from 'fs';
import * as path from 'path';

export interface BaseImageConfig {
  machineImage: IMachineImage;
  user: string;
  description: string;
}

export interface AmiMetadata {
  namePrefix: string;
  description: string;
  tags: Record<string, string>;
}

interface SourceAmiConfig {
  amiId: string;
  user: string;
  description: string;
}

// Load source AMI configurations from JSON file
const sourceAmisPath = path.join(__dirname, 'source_amis.json');
const sourceAmisData = JSON.parse(fs.readFileSync(sourceAmisPath, 'utf-8')) as Record<string, SourceAmiConfig>;

export const BASE_AMI_CONFIGS = sourceAmisData as {
  readonly ROCKY_8_10: SourceAmiConfig;
  readonly UBUNTU_24_04: SourceAmiConfig;
};

export enum VivadoLabEditionVersion {
  V2025_1 = '2025.1',
  V2025_2 = '2025.2',
}
