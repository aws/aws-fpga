#!/bin/bash

# Check if the script is being sourced
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    echo "Error: This script must be sourced. Please run:"
    echo "    source ${0}"
    exit 1
fi

# Get the directory of the script
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

# Create a requirements.txt file in the script directory
cat > "$SCRIPT_DIR/requirements.txt" << EOF
boto3>=1.33.13
boto3-stubs>=1.34.4
botocore>=1.33.13
botocore-stubs>=1.34.4
mypy-boto3-ec2>=1.34.4
mypy-boto3-s3>=1.34.0
pydantic==2.5.3
pydantic-core==2.14.6
EOF

echo "Creating and activating virtual environment in the script directory"
python3 -m venv "$SCRIPT_DIR/venv"
source "$SCRIPT_DIR/venv/bin/activate"

# Upgrade pip
python3 -m pip install --upgrade pip

# Install requirements
python3 -m pip install -r "$SCRIPT_DIR/requirements.txt"

echo "Virtual environment created in $SCRIPT_DIR/venv and packages installed successfully!"
