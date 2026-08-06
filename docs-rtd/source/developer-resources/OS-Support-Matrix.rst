Operating System Support Matrix
===============================

This page lists AMD Vivado / Vitis support for Rocky Linux (8, 9, 10)
and Ubuntu (20.04, 22.04, 24.04), and identifies the exact FPGA
Developer AMI combinations built and tested by AWS. Rocky Linux 8.10 and
specific Ubuntu versions are currently or historically supported by the
AWS F2 Developer Kit; the remaining rows are AMD-supported combinations
for which AWS does not publish a built-and-tested AMI (untested / not
supported by AWS).

The matrix covers AMD tool versions **2024.1, 2024.2, 2025.1, 2025.2,
and 2026.1**. AMD support and AWS testing are independent: listing a
tool version in the AMD column does not indicate AWS testing, and an
AWS-built/tested tool version does not imply that AMD listed that
OS/tool combination in UG973. Tool versions supported by the AWS F2
Developer Kit are listed in
`supported_vivado_versions.txt <https://github.com/aws/aws-fpga/tree/f2/supported_vivado_versions.txt>`__;
listing AMD’s 2026.1 OS support here does not declare F2 Developer Kit
support for Vivado / Vitis 2026.1.

The OS and tool-version mappings are taken from AMD’s official `UG973 —
Vivado Design Suite User Guide: Release Notes, Installation, and
Licensing <https://docs.amd.com/r/en-US/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__.

For EC2 development, AMD tools require **x86-64** instances. Graviton
(AArch64) instances are not compatible with the AMD tools.

Operating System Support
------------------------

Legend:

- **AMD-Supported Vivado / Vitis Versions** lists the tool versions for
  which AMD lists the OS in UG973.
- ``✅`` — AWS built and tested the listed FPGA Developer AMI on that OS
  and tool version. The AMI may be current or historical.
- ``—`` — no AWS-built and tested FPGA Developer AMI is documented for
  that OS.

.. list-table::
   :header-rows: 1
   :widths: auto

   * - OS Family
     - Version
     - AMD-Supported Vivado / Vitis Versions
     - AWS-Built and Tested FPGA Developer AMIs
   * - Rocky Linux 8
     - 8.10
     - 2025.1, 2025.2, 2026.1
     - ✅ `2025.1; 2025.2 <http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu>`__
   * - Rocky Linux 9
     - 9.6
     - 2025.2, 2026.1
     - —
   * - Rocky Linux 9
     - 9.7
     - 2026.1
     - —
   * - Rocky Linux 10
     - 10.0
     - 2025.2, 2026.1
     - —
   * - Rocky Linux 10
     - 10.1
     - 2026.1
     - —
   * - Ubuntu 20.04
     - 20.04.4 LTS
     - 2024.1
     - —
   * - Ubuntu 20.04
     - 20.04.5 LTS
     - 2024.1, 2024.2
     - —
   * - Ubuntu 20.04
     - 20.04.6 LTS
     - 2024.1, 2024.2
     - ✅ 2024.1 (legacy/EoL)
   * - Ubuntu 22.04
     - 22.04 LTS
     - 2024.1
     - —
   * - Ubuntu 22.04
     - 22.04.1 LTS
     - 2024.1, 2024.2
     - —
   * - Ubuntu 22.04
     - 22.04.2 LTS
     - 2024.1, 2024.2, 2025.1
     - —
   * - Ubuntu 22.04
     - 22.04.3 LTS
     - 2024.1, 2024.2, 2025.1, 2025.2, 2026.1
     - —
   * - Ubuntu 22.04
     - 22.04.4 LTS
     - 2024.2, 2025.1, 2025.2, 2026.1
     - —
   * - Ubuntu 22.04
     - 22.04.5 LTS
     - 2025.1, 2025.2, 2026.1
     - ✅ `2024.1 <https://aws.amazon.com/marketplace/pp/prodview-f5kjsenkfkz5u>`__ \*
   * - Ubuntu 24.04
     - 24.04 LTS
     - 2024.2, 2025.1, 2025.2, 2026.1
     - ✅ `2024.2; 2025.1; 2025.2 <http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
   * - Ubuntu 24.04
     - 24.04.1 LTS
     - 2025.1, 2025.2, 2026.1
     - —
   * - Ubuntu 24.04
     - 24.04.2 LTS
     - 2025.2, 2026.1
     - —
   * - Ubuntu 24.04
     - 24.04.3 LTS
     - 2026.1
     - —

\* Vivado 2024.1 predates Ubuntu 22.04.5: AMD’s UG973 lists 2024.1
support for Ubuntu 22.04 through 22.04.4. AWS built and tested FPGA
Developer AMI 1.16.2 (Vivado 2024.1) on Ubuntu 22.04.5.

**Ubuntu 20.04 lifecycle:** Ubuntu 20.04 is legacy/EoL and no longer
supported by AWS. `Canonical marks Ubuntu 20.04 LTS as out of standard
support and states that standard support ended on May 31,
2025 <https://ubuntu.com/20-04>`__. Continued Canonical security
maintenance requires Ubuntu Pro.

For current AMI IDs, kernels, and AWS Marketplace listings, see the
`User Guide — FPGA Developer AMI
section <../User-Guide-AWS-EC2-FPGA-Development-Kit.html#fpga-developer-ami>`__.

Building Your Own AMI (BYO)
---------------------------

For OS / tool combinations that AMD supports but AWS does not publish a
turnkey AMI for, you can:

- Use the `Runtime AMI Builder
  (RAB) <./runtime-ami-builder/README.html>`__ to build a customized
  runtime AMI on top of a base OS that AMD supports. The RAB is a
  CDK-based tool that automates installing the F2 SDK, Vivado Lab
  Edition, the AWS CLI, and other components.
- Set up an on-premise development environment using AMD’s `on-premise
  licensing guide <../hdk/docs/on-premise-licensing-help.html>`__ and the
  `HDK setup script <https://github.com/aws/aws-fpga/tree/f2/hdk_setup.sh>`__ on an AMD-supported OS and tool
  version supported by the F2 Developer Kit.
- For graphical Vivado / Vitis sessions on EC2, see the `Amazon DCV
  Setup Guide <./Amazon-DCV-Setup-Guide.html>`__.

Notes
-----

- The AMD matrix is a snapshot of UG973. The authoritative source for
  each tool version is AMD’s release notes:

  - `UG973 —
    2026.1 <https://docs.amd.com/r/2026.1-English/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__
  - `UG973 —
    2025.2 <https://docs.amd.com/r/2025.2-English/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__
  - `UG973 —
    2025.1 <https://docs.amd.com/r/2025.1-English/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__
  - `UG973 —
    2024.2 <https://docs.amd.com/r/2024.2-English/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__
  - `UG973 —
    2024.1 <https://docs.amd.com/r/2024.1-English/ug973-vivado-release-notes-install-license/Supported-Operating-Systems>`__

`Back to Home <../index.html>`__
