# AWS-FPGA Testing

## Table of Contents

* [Overview](#overview)
* [Shared Testing](#shared-testing)
* [HDK Testing](#hdk-testing)
* [SDK Testing](#sdk-testing)
* [SDAccel Testing](#sdaccel-testing)

## Overview

This repository is tested using [pytest](https://docs.pytest.org/en/latest/).
The pytest framework enables and encourages
[Test Driven Development](https://wiki.python.org/moin/TestDrivenDevelopment) so
that development of new features includes unit tests that verify that the feature is
implemented correctly.

The release process will automatically run all unit tests on all pull requests and all
the unit tests must pass before the pull request can be merged.

### Running Tests

Run tests in a module:
```
pytest *test_module.py*
```

Run tests in a directory:
```
pytest *test-dir*
```

[Specifying tests / selecting tests](https://docs.pytest.org/en/latest/usage.html#specifying-tests-selecting-tests)

### References

* [python.org PyTest Wiki](https://wiki.python.org/moin/PyTest)

## Shared Testing

```
pytest shared/test/bin/test_all.py
```

### Markdown Broken Links Checking

The following command will check all markdown files (*.md) in the repository for broken hyperlinks.
It first renders the markdown into HTML and the finds all of the links in the HTML and verifies
that the links point to valid URLs.

```
shared/test/bin/check_md_files.py
```

## HDK Testing

## SDK Testing

## SDAccel Testing
