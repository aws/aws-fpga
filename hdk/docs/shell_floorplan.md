# Shell Floorplan Reference

This document provides the floorplans of the Small and XDMA Shells.

## Small Shell

![Small_shell_floorplan](../../docs-rtd/source/_static/small_shell_fp.png)

## XDMA Shell

![XDMA_shell_floorplan](../../docs-rtd/source/_static/xdma_shell_fp.png)

## Recommendations

* The PCIS bus is physically located in SLR1 in SMALL_SHELL. Any customer logic interfacing with this bus should reside in SLR1.
* The PCIS bus is physically located in SLR2 in the XDMA_SHELL. Any customer logic interfacing with this bus should reside in SLR2.
