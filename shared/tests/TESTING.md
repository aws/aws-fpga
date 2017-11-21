# AWS-FPGA Testing

## Table of Contents

* [Overview](#overview)
  * [Prerequisities](#prerequisities)
  * [Running Tests](#running-tests)
  * [References](#references)
* [Shared Testing](#shared-testing)
* [HDK Testing](#hdk-testing)
* [SDK Testing](#sdk-testing)
* [SDAccel Testing](#sdaccel-testing)
* [Jenkins Steps](#jenkins-steps)

## Overview

This repository is tested using [pytest](https://docs.pytest.org/en/latest/).
The pytest framework enables and encourages
[Test Driven Development](https://wiki.python.org/moin/TestDrivenDevelopment) so
that development of new features includes unit tests that verify that the feature is
implemented correctly.

The release process will automatically run all unit tests on all pull requests and all
the unit tests must pass before the pull request can be merged.

All of the tests are contained in the following directories:
* shared/tests
* hdk/tests
* SDAccel/tests
* sdk/tests

### Prerequisities

The testing framework uses the following packages which must be installed prior to running tests:
* [pytest](#pytest)
* [GitPython](#gitpython)
* [boto3](#boto3)

#### Pytest

This package contains the pytest program and package that is used to run the tests.
If it is not installed on your system you can install it using the following command:

```sudo pip install pytest --upgrade```

#### GitPython

This package allows programmatic access to the git repository.
It is used to find the root directory of the repository as well as information about which files have
been changed by a pull request.

Use the following command to install the package:

```sudo pip install GitPython --upgrade```

#### Boto3

The boto3 package is the AWS Python API.
It can be used to start and terminate instances and any other API operation that you have
permissions for.

Configuration of account credentials is explained in the [Quickstart](http://boto3.readthedocs.io/en/latest/guide/quickstart.html#configuration).

The following command will install the latest release.

```sudo pip install boto3 --upgrade```

### Running Tests

Run tests in a module:

`pytest -v `*`test_module.py`*

Run tests in a directory:

`pytest -v `*`test-dir`*

To get a list of tests that will run without running them just add the `--collect-only` option:

`pytest -v `*`test-dir`*` --collect-only`

More details can be found on the [pytest web site](https://docs.pytest.org/en/latest/usage.html#specifying-tests-selecting-tests).

### References

* [pytest web site](https://docs.pytest.org/en/latest/index.html)
* [python.org PyTest Wiki](https://wiki.python.org/moin/PyTest)

## Shared Testing

```
pytest shared/tests
```

### Markdown Broken Links Checking

The following command will check all markdown files (*.md) in the repository for broken hyperlinks.
It first renders the markdown into HTML and the finds all of the links in the HTML and verifies
that the links point to valid URLs.

```
shared/test/bin/check_md_files.py
```

This script can also be run as part of pytest using:
```
pytest shared/tests/test_md_links.py
```

## HDK Testing

## SDK Testing

## SDAccel Testing

## Jenkins Steps

The commands for each Jenkins pipeline step are:

* ``pytest -v shared/tests/test_md_links.py``
* ``pytest -v hdk/tests/simulation_tests``
* ``pytest -v hdk/tests/dcp_generation_tests -k test_cl_hello_world --input_key input_key --output_key output_key``
