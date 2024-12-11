# =============================================================================
# Copyright 2021 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
# =============================================================================


# Bitstream generation constraints


###############################################################################
# TODO
###############################################################################
set_property CONFIG_MODE                       SPIx4    [current_design]
set_property CONFIG_VOLTAGE                    1.8      [current_design]
set_property BITSTREAM.GENERAL.COMPRESS        TRUE     [current_design]
##set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN ENABLE   [current_design]
set_property BITSTREAM.CONFIG.USR_ACCESS       00000000 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE       85.0     [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR   YES      [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE    YES      [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH     4        [current_design]
