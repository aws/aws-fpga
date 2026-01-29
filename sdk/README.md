# AWS EC2 FPGA Software Development Kit

The AWS FPGA SDK directory provides drivers and runtime tools for managing Amazon FPGA Images (AFIs) on EC2 FPGA instances. Use this SDK to load, clear, and interact with pre-built AFIs on F2 instances in Linux environments.

**Note:** This SDK is for **deploying** AFIs, not building or registering them. For AFI development, see the [HDK](../hdk/README.md).

## Quick Start

The AWS FPGA SDK requires `gcc` to be installed on a Linux distribution AMI: `sudo {yum|apt-get} install gcc`

```bash
# Clone and setup and install the SDK with env variables (if not already done)
git clone https://github.com/aws/aws-fpga.git
cd aws-fpga
source sdk_setup.sh

# Check FPGA management tools
fpga-describe-local-image --help
fpga-load-local-image --help

# Verify SDK environment
echo $SDK_DIR

# Load an AFI (replace with your AFI ID and slot)
sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0

# Verify AFI loaded
sudo fpga-describe-local-image -S 0

# Test management tools
cd $SDK_DIR/userspace/fpga_mgmt_examples
make
sudo ./fpga_mgmt_example
```

## Core Tools

Fully documented in [FPGA Management Tools](./userspace/fpga_mgmt_tools/README.md)

| Tool | Purpose |
|------|---------|
| `fpga-describe-local-image-slots` | List available FPGA slots |
| `fpga-load-local-image` | Load AFI to FPGA slot |
| `fpga-describe-local-image` | Check AFI status |
| `fpga-clear-local-image` | Clear AFI from slot |

**All tools require `sudo` privileges.** Use `-help` flag for detailed options.

## SDK Components

### Management Tools

- **[FPGA Management Tools](./userspace/fpga_mgmt_tools/README.md)** - Command-line AFI management
- **[C API Examples](./userspace/fpga_mgmt_examples/README.md)** - Programmatic AFI control
- **[Python Bindings](./userspace/cython_bindings/README.md)** - Python interface to FPGA APIs

### Applications

- **[Virtual Ethernet](./apps/virtual-ethernet/README.md)** - High-performance networking
- **[MSI-X Interrupts](./apps/msix-interrupts/README.md)** - Interrupt handling implementation

### Performance & Optimization

- **[Performance Optimization Guide](./docs/F2_Software_Performance_Optimization_Guide.md)**
- **[Load Times Analysis](./docs/Load_Times.md)**

## Troubleshooting

Refer to the [FAQ section for FPGA Mgmt Tools](./userspace/fpga_mgmt_tools/README.md#faq) or respective applications and tools.

**Need help?**

- [GitHub Issues](https://github.com/aws/aws-fpga/issues) - Code/documentation problems
- [AWS re:Post](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development) - F2 instance questions
