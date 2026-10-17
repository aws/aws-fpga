# Amazon FPGA Runtime AMI Builder
#
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

. $(git rev-parse --show-toplevel)/shared/bin/set_common_functions.sh
. $(git rev-parse --show-toplevel)/shared/bin/set_common_env_vars.sh
export RAB_DIR="${AWS_FPGA_REPO_DIR}/developer_resources/runtime_ami_builder"

install_cdk_deps() {
    if [[ -z $(which npm) ]]; then
        err_msg "No npm install detected! Please install Node.js and npm before running!"
        return 1
    fi

    npm_cmds=(
        "install -g aws-cdk@2.1138.0"
        "ci"
    )

    info_msg "Installing pinned CDK dependencies!"
    for cmd in "${npm_cmds[@]}"; do
        if ! npm $cmd; then
            err_msg "Failed to run: npm $cmd"
            return 1
        fi
    done

    info_msg "All required NPM packages installed and updated!"
    return 0
}

create_supported_ver_enum() {
    SUPPORTED_VERSIONS_FILE="${AWS_FPGA_REPO_DIR}/supported_vivado_versions.txt"
    TYPES_FILE="${RAB_DIR}/lib/types.ts"

    if [[ ! -f "$SUPPORTED_VERSIONS_FILE" ]]; then
        err_msg "Could not find $SUPPORTED_VERSIONS_FILE"
        return 1
    fi

    versions=()
    while IFS= read -r line; do
        if [[ $line =~ vivado[[:space:]]+v([0-9]+)\.([0-9]+) ]]; then
            major="${BASH_REMATCH[1]}"
            minor="${BASH_REMATCH[2]}"
            if [[ $major -gt 2025 ]] || [[ $major -eq 2025 && $minor -ge 1 ]]; then
                versions+=("V${major}_${minor} = '${major}.${minor}'")
            fi
        fi
    done < "$SUPPORTED_VERSIONS_FILE"

    if [[ ${#versions[@]} -eq 0 ]]; then
        enum_content="export enum VivadoLabEditionVersion {\n}"
    else
        enum_entries=$(printf "  %s,\n" "${versions[@]}")
        enum_content="export enum VivadoLabEditionVersion {\n${enum_entries}\n}"
    fi

    if [[ -f "$TYPES_FILE" ]]; then
        awk -v new_enum="$enum_content" '
            /export enum VivadoLabEditionVersion/ {
                print new_enum
                in_enum=1
                next
            }
            in_enum && /^}/ {
                in_enum=0
                next
            }
            !in_enum { print }
        ' "$TYPES_FILE" > "${TYPES_FILE}.tmp" && mv "${TYPES_FILE}.tmp" "$TYPES_FILE"
    else
        err_msg "Could not find $TYPES_FILE"
        return 1
    fi
    return 0
}

if ! install_cdk_deps; then
    return 1
fi

if ! create_supported_ver_enum; then
    return 1
fi

info_msg "###############################################################"
info_msg "#            Runtime AMI Builder setup complete!              #"
info_msg "###############################################################"
