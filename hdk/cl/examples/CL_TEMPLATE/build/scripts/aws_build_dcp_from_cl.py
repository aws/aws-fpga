#!/usr/bin/env python3

import os
import sys


def main() -> int:
    hdk_shell_dir = os.environ.get("HDK_SHELL_DIR")
    if not hdk_shell_dir:
        sys.stderr.write("HDK_SHELL_DIR is not set. Please source hdk_setup.sh.\n")
        return 127

    candidate = os.path.join(hdk_shell_dir, "build", "scripts", "aws_build_dcp_from_cl.py")
    if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
        os.execv(candidate, [candidate, *sys.argv[1:]])

    sys.stderr.write("Unable to locate aws_build_dcp_from_cl.py from the AWS HDK environment.\n")
    sys.stderr.write("Please source hdk_setup.sh so HDK_SHELL_DIR points to the active shell.\n")
    return 127


if __name__ == "__main__":
    raise SystemExit(main())
