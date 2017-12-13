# SDK Testing

## Overview
All of these tests must be run on an F1 instance because they require loading AFIs
and installing DMA drivers.

To get a list of all tests:

```
pytest sdk/tests --collect-only
```

To run a test:

```
pytest -s -v <test-name>
```

For example:

```
pytest -s -v sdk/tests/test_edma.py::TestEdma::test_unittest
```

## Test Summaries

| Class | Test | Description |
|-------|------|-------------|
| sdk/tests/test_edma.py::TestEdma | test_unittest | |
|                                  | test_perftest | |
| sdk/tests/test_sdk_scripts.py::TestSdkScripts | test_sdk_setup | |
