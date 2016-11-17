####################################################################################################
# HEADER_BEGIN
# COPYRIGHT NOTICE
# Copyright 2001-2016 Xilinx Inc. All Rights Reserved.
# http://www.xilinx.com/support
# HEADER_END
####################################################################################################

########################################################################################
##
## Company:        Xilinx, Inc.
## Created by:     David Pefourque
##
## Version:        2016.11.01
## Description:    Generate a fast fail/pass report
##
########################################################################################

########################################################################################
## 2016.11.01 - Added few more utilization metrics inside CSV
## 2016.10.31 - Fix minor formating issue with some percent metrics
##            - Added missing metrics inside CSV
##            - Added new columns to CSV with design and run directory
## 2016.10.28 - Added better support for post-place utilization report
##            - Added support for extracting small percent such as "<0.1"
## 2016.10.24 - Renamed proc and namespace to report_failfast
## 2016.10.11 - Improved runtime for average fanout calculation
## 2016.10.10 - Initial release
########################################################################################

# Example of report:

#      +-----------------------------------------------------------------------------------+
#      | Design Summary                                                                    |
#      | checkpoint_ECO                                                                    |
#      | xcku040-ffva1156-2-e                                                              |
#      +---------------------------------------------------+-------------+--------+--------+
#      | Criteria                                          | Requirement | Actual | Status |
#      +---------------------------------------------------+-------------+--------+--------+
#      | LUT                                               | 70%         | 89.72% | FAIL   |
#      | FD                                                | 50%         | 34.85% | OK     |
#      | LUTRAM+SRL                                        | 25%         | 10.32% | OK     |
#      | CARRY8                                            | 25%         | 6.44%  | OK     |
#      | MUXF7                                             | 15%         | 3.73%  | OK     |
#      | MUXF8                                             | 7%          | 0.32%  | OK     |
#      | HLUTNM                                            | 20%         | 8.41%  | OK     |
#      | DSP48                                             | 80%         | 0.00%  | OK     |
#      | RAMB36/FIFO36                                     | 80%         | 85.75% | FAIL   |
#      | DSP48+RAMB38                                      | 140%        | 85.75% | OK     |
#      | BUFGCE* + BUFGCTRL                                | 24          | 43     | FAIL   |
#      | Control Sets                                      | 10000       | 7739   | OK     |
#      | Average Fanout for modules > 100k cells           | 4           | 3.53   | OK     |
#      | Non-FD high fanout nets > 10k loads               | 0           | 0      | OK     |
#      +---------------------------------------------------+-------------+--------+--------+
#      | TIMING-6                                          | 0           | 1      | FAIL   |
#      | TIMING-7                                          | 0           | 1      | FAIL   |
#      | TIMING-8                                          | 0           | 1      | FAIL   |
#      | TIMING-14                                         | 0           | 0      | OK     |
#      | TIMING-35                                         | 0           | 0      | OK     |
#      +---------------------------------------------------+-------------+--------+--------+
#      | Number of paths above max LUT budgeting (0.425ns) | 0           | 0      | OK     |
#      +---------------------------------------------------+-------------+--------+--------+

namespace eval ::tb {
  namespace export -force report_failfast
}

namespace eval ::tb::utils {
  namespace export -force report_failfast
}

namespace eval ::tb::utils::report_failfast {
  namespace export -force report_failfast
  variable version {2016.11.01}
  variable params
  variable output {}
  variable metrics
  variable data
  array set params [list failed 0 format {table} verbose 0 debug 0]
  array set reports [list]
  array set metrics [list]
  catch {unset data}
}

proc ::tb::utils::report_failfast::lshift {inputlist} {
  upvar $inputlist argv
  set arg  [lindex $argv 0]
  set argv [lrange $argv 1 end]
  return $arg
}

proc ::tb::utils::report_failfast::report_failfast {args} {
  variable metrics
  variable params
  variable output
  variable data
  set params(failed) 0
  set params(verbose) 0
  set params(debug) 0
  set params(format) {table}
  set filename {}
  set filemode {w}
  set time [clock seconds]
  set date [clock format $time]
  set error 0
  set help 0
#   if {[llength $args] == 0} {
#     set help 1
#   }
  while {[llength $args]} {
    set name [lshift args]
    switch -regexp -- $name {
      {^-f(i(le?)?)?$} {
        set filename [lshift args]
      }
      {^-ap(p(e(nd?)?)?)?$} {
        set filemode {a}
      }
      {^-v(e(r(b(o(se?)?)?)?)?)?$} {
        set params(verbose) 1
      }
      {^-d(e(b(ug?)?)?)?$} {
        set params(debug) 1
      }
      {^-h(e(lp?)?)?$} {
        set help 1
      }
      default {
        if {[string match "-*" $name]} {
          puts " -E- option '$name' is not a valid option."
          incr error
        } else {
          puts " -E- option '$name' is not a valid option."
          incr error
        }
      }
    }
  }

  if {$help} {
    puts [format {
  Usage: report_failfast
              [-file <filename>]
              [-append]
              [-verbose|-v]
              [-help|-h]

  Description: Generate a fast fail/pass report

  Example:
     report_failfast
     report_failfast -file failfast.rpt
} ]
    # HELP -->
    return -code ok
  }

  if {$error} {
    error " -E- some error(s) happened. Cannot continue"
  }

  reset

  set startTime [clock seconds]
  set output [list]

  if {[catch {

    ########################################################################################
    ##
    ## General design metrics
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      addMetric {design.part}                   {Part}
      addMetric {design.part.architecture}      {Architecture}
      addMetric {design.part.architecture.name} {Architecture Name}
      addMetric {design.part.speed.class}       {Speed class}
      addMetric {design.part.speed.label}       {Speed label}
      addMetric {design.part.speed.id}          {Speed ID}
      addMetric {design.part.speed.date}        {Speed date}
#       addMetric {design.nets}                   {Number of nets}
      addMetric {design.cells.hlutnm}           {Number of HLUTNM cells}
      addMetric {design.cells.hlutnm.pct}       {Number of HLUTNM cells (%)}
      addMetric {design.ports}                  {Number of ports}
      addMetric {design.slrs}                   {Number of SLRs}

      set part [get_property -quiet PART [current_design]]
      setMetric {design.part}                   $part
      setMetric {design.part.architecture}      [get_property -quiet ARCHITECTURE $part]
      setMetric {design.part.architecture.name} [get_property -quiet ARCHITECTURE_FULL_NAME $part]
      setMetric {design.part.speed.class}       [get_property -quiet SPEED $part]
      setMetric {design.part.speed.label}       [get_property -quiet SPEED_LABEL $part]
      setMetric {design.part.speed.id}          [get_property -quiet SPEED_LEVEL_ID $part]
      setMetric {design.part.speed.date}        [get_property -quiet SPEED_LEVEL_ID_DATE $part]
      setMetric {design.ports}                  [llength [get_ports -quiet]]
      setMetric {design.slrs}                   [llength [get_slrs -quiet]]
#       setMetric {design.nets}                   [llength [get_nets -quiet -hier -top_net_of_hierarchical_group -filter {TYPE == SIGNAL}]]

      set luts [get_cells -quiet -hier -filter {IS_PRIMITIVE && REF_NAME =~ LUT*}]
      set hlutnm [filter -quiet $luts {SOFT_HLUTNM != "" || HLUTNM != ""}]
      setMetric {design.cells.hlutnm} [llength $hlutnm]
      # Calculate the percent of HLUTNM over the total number of LUT
      setMetric {design.cells.hlutnm.pct} [format {%.2f} [expr {100.0 * double([llength $hlutnm]) / double([llength $luts])}] ]
      set stepStopTime [clock seconds]
      puts " -I- design metrics completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Utilization metrics
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      # Get report
      set report [report_utilization -quiet -return_string]

      # +----------------------------+--------+-------+-----------+-------+
      # |          Site Type         |  Used  | Fixed | Available | Util% |
      # +----------------------------+--------+-------+-----------+-------+
      # | Slice LUTs                 | 396856 |     0 |   1221600 | 32.49 |
      # |   LUT as Logic             | 394919 |     0 |   1221600 | 32.33 |
      # |   LUT as Memory            |   1937 |     0 |    344800 |  0.56 |
      # |     LUT as Distributed RAM |     64 |     0 |           |       |
      # |     LUT as Shift Register  |   1873 |     0 |           |       |
      # | Slice Registers            | 224301 |     2 |   2443200 |  9.18 |
      # |   Register as Flip Flop    | 200897 |     0 |   2443200 |  8.22 |
      # |   Register as Latch        |  23404 |     2 |   2443200 |  0.96 |
      # | F7 Muxes                   |   6787 |     0 |    610800 |  1.11 |
      # | F8 Muxes                   |   2619 |     0 |    305400 |  0.86 |
      # +----------------------------+--------+-------+-----------+-------+
      # +----------------------------+------+-------+-----------+-------+
      # |          Site Type         | Used | Fixed | Available | Util% |
      # +----------------------------+------+-------+-----------+-------+
      # | CLB LUTs                   | 2088 |     0 |    230400 |  0.91 |
      # |   LUT as Logic             | 1916 |     0 |    230400 |  0.83 |
      # |   LUT as Memory            |  172 |     0 |    101760 |  0.17 |
      # |     LUT as Distributed RAM |   56 |     0 |           |       |
      # |     LUT as Shift Register  |  116 |     0 |           |       |
      # | CLB Registers              | 2612 |     0 |    460800 |  0.57 |
      # |   Register as Flip Flop    | 2612 |     0 |    460800 |  0.57 |
      # |   Register as Latch        |    0 |     0 |    460800 |  0.00 |
      # | CARRY8                     |    8 |     0 |     28800 |  0.03 |
      # | F7 Muxes                   |    7 |     0 |    115200 | <0.01 |
      # | F8 Muxes                   |    0 |     0 |     57600 |  0.00 |
      # | F9 Muxes                   |    0 |     0 |     28800 |  0.00 |
      # +----------------------------+------+-------+-----------+-------+

      # +-------------------------------------------------------------+----------+-------+-----------+-------+
      # |                          Site Type                          |   Used   | Fixed | Available | Util% |
      # +-------------------------------------------------------------+----------+-------+-----------+-------+
      # | CLB                                                         |       33 |     0 |     34260 |  0.10 |
      # |   CLBL                                                      |       21 |     0 |           |       |
      # |   CLBM                                                      |       12 |     0 |           |       |
      # | LUT as Logic                                                |       96 |     0 |    274080 |  0.04 |
      # |   using O5 output only                                      |        0 |       |           |       |
      # |   using O6 output only                                      |       68 |       |           |       |
      # |   using O5 and O6                                           |       28 |       |           |       |
      # | LUT as Memory                                               |        0 |     0 |    144000 |  0.00 |
      # |   LUT as Distributed RAM                                    |        0 |     0 |           |       |
      # |   LUT as Shift Register                                     |        0 |     0 |           |       |
      # | LUT Flip Flop Pairs                                         |      153 |     0 |    274080 |  0.06 |
      # |   fully used LUT-FF pairs                                   |       63 |       |           |       |
      # |   LUT-FF pairs with unused LUT                              |       57 |       |           |       |
      # |   LUT-FF pairs with unused Flip Flop                        |       33 |       |           |       |
      # | Unique Control Sets                                         |       13 |       |           |       |
      # | Maximum number of registers lost to control set restriction | 21(Lost) |       |           |       |
      # +-------------------------------------------------------------+----------+-------+-----------+-------+

      addMetric {utilization.clb.lut}        {CLB LUTs}
      addMetric {utilization.clb.lut.pct}    {CLB LUTs (%)}
      addMetric {utilization.clb.ff}         {CLB Registers}
      addMetric {utilization.clb.ff.pct}     {CLB Registers (%)}
      addMetric {utilization.clb.carry8}     {CARRY8}
      addMetric {utilization.clb.carry8.pct} {CARRY8 (%)}
      addMetric {utilization.clb.f7mux}      {F7 Muxes}
      addMetric {utilization.clb.f7mux.pct}  {F7 Muxes (%)}
      addMetric {utilization.clb.f8mux}      {F8 Muxes}
      addMetric {utilization.clb.f8mux.pct}  {F8 Muxes (%)}
      addMetric {utilization.clb.f9mux}      {F9 Muxes}
      addMetric {utilization.clb.f9mux.pct}  {F9 Muxes (%)}
      addMetric {utilization.clb.lutmem}     {LUT as Memory}
      addMetric {utilization.clb.lutmem.pct} {LUT as Memory (%)}
#       addMetric {utilization.ctrlsets.uniq}  {Unique Control Sets}
#       addMetric {utilization.ctrlsets.lost}  {Registers Lost due to Control Sets}

#       extractMetric report {utilization.clb.lut}         {\|\s+CLB LUTs[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                      {n/a}
#       extractMetric report {utilization.clb.lut.pct}     {\|\s+CLB LUTs[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|}      {n/a}
#       extractMetric report {utilization.clb.ff}          {\|\s+CLB Registers[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                 {n/a}
#       extractMetric report {utilization.clb.ff.pct}      {\|\s+CLB Registers[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} {n/a}

      extractMetric2 report {utilization.clb.lut}        -p [list {\|\s+CLB LUTs[^\|]*\s*\|\s+([0-9\.]+)\s+\|} \
                                                                  {\|\s+SLICE LUTs[^\|]*\s*\|\s+([0-9\.]+)\s+\|} \
                                                            ] \
                                                         -default {n/a}
      extractMetric2 report {utilization.clb.lut.pct}    -p [list {\|\s+CLB LUTs[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+([0-9\.]+)\s+\|} \
                                                                  {\|\s+SLICE LUTs[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+([0-9\.]+)\s+\|} \
                                                            ] \
                                                         -default {n/a}
      extractMetric2 report {utilization.clb.ff}         -p [list {\|\s+CLB Registers[^\|]*\s*\|\s+([0-9\.]+)\s+\|} \
                                                                  {\|\s+SLICE Registers[^\|]*\s*\|\s+([0-9\.]+)\s+\|} \
                                                            ] \
                                                         -default {n/a}
      extractMetric2 report {utilization.clb.ff.pct}     -p [list {\|\s+CLB Registers[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} \
                                                                  {\|\s+SLICE Registers[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} \
                                                            ] \
                                                         -default {n/a}

      extractMetric report {utilization.clb.carry8}      {\|\s+CARRY8[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                          {0}
      extractMetric report {utilization.clb.carry8.pct}  {\|\s+CARRY8[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|}        {0.0}
      extractMetric report {utilization.clb.f7mux}       {\|\s+F7 Muxes[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                        {0}
      extractMetric report {utilization.clb.f7mux.pct}   {\|\s+F7 Muxes[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|}      {0.0}
      extractMetric report {utilization.clb.f8mux}       {\|\s+F8 Muxes[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                        {0}
      extractMetric report {utilization.clb.f8mux.pct}   {\|\s+F8 Muxes[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|}      {0.0}
      extractMetric report {utilization.clb.f9mux}       {\|\s+F9 Muxes[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                        {0}
      extractMetric report {utilization.clb.f9mux.pct}   {\|\s+F9 Muxes[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|}      {0.0}
      extractMetric report {utilization.clb.lutmem}      {\|\s+LUT as Memory[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                   {0}
      extractMetric report {utilization.clb.lutmem.pct}  {\|\s+LUT as Memory[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} {0.0}
#       extractMetric report {utilization.ctrlsets.uniq}   {\|\s+Unique Control Sets[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                           {n/a}
#       extractMetric report {utilization.ctrlsets.lost}   {\|\s+.+registers lost to control set restriction[^\|]*\s*\|\s+([0-9\.]+).+\s+\|}                 {n/a}

#       # Calculate the percent of HLUTNM over the total number of LUT
#       set numluts [getMetric {utilization.clb.lut}]
#       set numhlutnm [getMetric {design.cells.hlutnm}]
#       setMetric {design.cells.hlutnm.pct} [format {%.2f} [expr {100.0 * double($numhlutnm) / double($numluts)}] ]


      # +-------------------+------+-------+-----------+-------+
      # |     Site Type     | Used | Fixed | Available | Util% |
      # +-------------------+------+-------+-----------+-------+
      # | Block RAM Tile    |    8 |     0 |       912 |  0.88 |
      # |   RAMB36/FIFO*    |    8 |     0 |       912 |  0.88 |
      # |     FIFO36E2 only |    8 |       |           |       |
      # |   RAMB18          |    0 |     0 |      1824 |  0.00 |
      # +-------------------+------+-------+-----------+-------+

      addMetric {utilization.ram.tile}     {Block RAM Tile}
      addMetric {utilization.ram.tile.pct} {Block RAM Tile (%)}

      extractMetric report {utilization.ram.tile}     {\|\s+Block RAM Tile[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                   {n/a}
      extractMetric report {utilization.ram.tile.pct} {\|\s+Block RAM Tile[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} {n/a}

      # +-----------+------+-------+-----------+-------+
      # | Site Type | Used | Fixed | Available | Util% |
      # +-----------+------+-------+-----------+-------+
      # | DSPs      |    0 |     0 |      2520 |  0.00 |
      # +-----------+------+-------+-----------+-------+

      addMetric {utilization.dsp}     {DSPs}
      addMetric {utilization.dsp.pct} {DSPs (%)}

      extractMetric report {utilization.dsp}     {\|\s+DSPs[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                   {n/a}
      extractMetric report {utilization.dsp.pct} {\|\s+DSPs[^\|]*\s*\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+[0-9\.]+\s+\|\s+<?([0-9\.]+)\s+\|} {n/a}

      addMetric {utilization.bigblocks.pct} {Block RAM + DSP (%)}
      if {[catch {
        # Cumulative metric
        setMetric {utilization.bigblocks.pct} [format {%.2f} [expr [getMetric {utilization.dsp.pct}] \
                                                  + [getMetric {utilization.ram.tile.pct}] ] ]
      }]} {
        setMetric {utilization.bigblocks.pct} {n/a}
      }

      # +----------------------+------+-------+-----------+-------+
      # |       Site Type      | Used | Fixed | Available | Util% |
      # +----------------------+------+-------+-----------+-------+
      # | GLOBAL CLOCK BUFFERs |    5 |     0 |       544 |  0.92 |
      # |   BUFGCE             |    5 |     0 |       208 |  2.40 |
      # |   BUFGCE_DIV         |    0 |     0 |        32 |  0.00 |
      # |   BUFG_GT            |    0 |     0 |       144 |  0.00 |
      # |   BUFG_PS            |    0 |     0 |        96 |  0.00 |
      # |   BUFGCTRL*          |    0 |     0 |        64 |  0.00 |
      # +----------------------+------+-------+-----------+-------+

      addMetric {utilization.clk.bufgce}           {BUFGCE Buffers}
      addMetric {utilization.clk.bufgce.pct}       {BUFGCE Buffers (%)}
      addMetric {utilization.clk.bufgcediv}        {BUFGCE_DIV Buffers}
      addMetric {utilization.clk.bufgcediv.pct}    {BUFGCE_DIV Buffers (%)}
      addMetric {utilization.clk.bufggt}           {BUFG_GT Buffers}
      addMetric {utilization.clk.bufggt.pct}       {BUFG_GT Buffers (%)}
      addMetric {utilization.clk.bufgps}           {BUFG_PS Buffers}
      addMetric {utilization.clk.bufgps.pct}       {BUFG_PS Buffers (%)}
      addMetric {utilization.clk.bufgctrl}         {BUFGCTRL Buffers}
      addMetric {utilization.clk.bufgctrl.pct}     {BUFGCTRL Buffers (%)}
      addMetric {utilization.clk.all}              {BUFG* Buffers}

      extractMetric report {utilization.clk.bufgce}        {\|\s+BUFGCE[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                  {0}
      extractMetric report {utilization.clk.bufgce.pct}    {\|\s+BUFGCE[^\|]*\s*\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+<?([0-9\.]+)\s+\|}      {0.0}
      extractMetric report {utilization.clk.bufgcediv}     {\|\s+BUFGCE_DIV[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                              {0}
      extractMetric report {utilization.clk.bufgcediv.pct} {\|\s+BUFGCE_DIV[^\|]*\s*\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+<?([0-9\.]+)\s+\|}  {0.0}
      extractMetric report {utilization.clk.bufggt}        {\|\s+BUFG_GT[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                 {0}
      extractMetric report {utilization.clk.bufggt.pct}    {\|\s+BUFG_GT[^\|]*\s*\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+<?([0-9\.]+)\s+\|}     {0.0}
      extractMetric report {utilization.clk.bufgps}        {\|\s+BUFG_PS[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                                 {0}
      extractMetric report {utilization.clk.bufgps.pct}    {\|\s+BUFG_PS[^\|]*\s*\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+<?([0-9\.]+)\s+\|}     {0.0}
      extractMetric report {utilization.clk.bufgctrl}      {\|\s+BUFGCTRL\*?[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                             {0}
      extractMetric report {utilization.clk.bufgctrl.pct}  {\|\s+BUFGCTRL\*?[^\|]*\s*\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+[^\|]+\s+\|\s+<?([0-9\.]+)\s+\|} {0.0}

      if {[catch {
        # Cumulative metric (w/o BUFG_GT/BUFG_PS)
#                                             + [getMetric {utilization.clk.bufggt}]
#                                             + [getMetric {utilization.clk.bufgps}]
        setMetric {utilization.clk.all} [expr [getMetric {utilization.clk.bufgce}] \
                                            + [getMetric {utilization.clk.bufgcediv}] \
                                            + [getMetric {utilization.clk.bufgctrl}] ]
      }]} {
        setMetric {utilization.clk.all} {n/a}
      }

      set stepStopTime [clock seconds]
      puts " -I- utilization metrics completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Control sets metric
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      # Get report
      set report [report_control_sets -quiet -return_string]

      addMetric {utilization.ctrlsets.uniq}  {Unique Control Sets}

      extractMetric report {utilization.ctrlsets.uniq}   {\|\s+Number of unique control sets[^\|]*\s*\|\s+([0-9\.]+)\s+\|}                                           {n/a}

      set stepStopTime [clock seconds]
      puts " -I- control set metrics completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Methodology checks metrics
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      addMetric {methodology.timing-6}   {TIMING-6}
      addMetric {methodology.timing-7}   {TIMING-7}
      addMetric {methodology.timing-8}   {TIMING-8}
      addMetric {methodology.timing-14}  {TIMING-14}
      addMetric {methodology.timing-35}  {TIMING-35}
      catch {unset vios}
      foreach idx {6 7 8 14 35} { set vios($idx) 0 }
      # Only run TIMING-* checks
      report_methodology -quiet -checks [get_methodology_checks -quiet TIMING-*] -return_string
      set violations [get_methodology_violations]
      foreach vio $violations {
        if {[regexp {TIMING-([0-9]+)#[0-9]+} $vio - num]} {
          if {![info exists vios($num)]} { set vios($num) 0 }
          incr vios($num)
        }
      }
      setMetric {methodology.timing-6}   $vios(6)
      setMetric {methodology.timing-7}   $vios(7)
      setMetric {methodology.timing-8}   $vios(8)
      setMetric {methodology.timing-14}  $vios(14)
      setMetric {methodology.timing-35}  $vios(35)
      set stepStopTime [clock seconds]
      puts " -I- methodology check metrics completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Average fanout metric
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      addMetric {design.cells.maxavgfo}   {Average Fanout for modules > 100k cells}

      catch {unset data}
      # Key '-' holds the list of average fanout for modules > 100K
      set data(-) [list 0]
      calculateAvgFanout . 100000
      set maxfo [lindex [lsort -decreasing -real $data(-)] 0]

#       set cells [getModules . 0 100000]
#       set L [list 0.0]
#       foreach cell $cells {
#         lappend L [getAvgFanout $cell]
# # puts "  => avgfo: [lindex $L end]"
#       }
#       set maxfo [lindex [lsort -decreasing -real $L] 0]

# puts "<maxfo:$maxfo>"
      setMetric {design.cells.maxavgfo}  $maxfo
      set stepStopTime [clock seconds]
#       puts " -I- average fanout metrics completed for [llength $cells] modules in [expr $stepStopTime - $stepStartTime] seconds"
      puts " -I- average fanout metrics completed in [expr $stepStopTime - $stepStartTime] seconds ([expr [llength $data(-)] -1] modules)"
    }

    ########################################################################################
    ##
    ## Non-FD high fanout nets (fanout) metric
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]
      addMetric {design.nets.nonfdhfn}   {Non-FD high fanout nets > 10k loads}

      set nets [get_nets -quiet -hierarchical -top_net_of_hierarchical_group -filter {(FLAT_PIN_COUNT >= 10000) && (TYPE == SIGNAL)}]
      set drivers [get_pins -quiet -of $nets -filter {IS_LEAF && (REF_NAME !~ FD*) && (DIRECTION == OUT)}]
      setMetric {design.nets.nonfdhfn}  [llength $drivers]
      set stepStopTime [clock seconds]
      puts " -I- non-FD high fanout nets completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Number of LUTs in path in critical timing paths
    ##
    ########################################################################################

    if {1} {
      set stepStartTime [clock seconds]

      # Timing budget per LUT: 300ps (UltraScale Plus / Speedgrade -2)
      set timBudgetPerLUT 0.300

      set speedgrade [get_property -quiet SPEED [get_property -quiet PART [current_design]]]
      set architecture [get_property -quiet ARCHITECTURE [get_property -quiet PART [current_design]]]
      switch $architecture {
        artix7 -
        kintex7 -
        virtex7 -
        zynq {
          switch -regexp -- $speedgrade {
            "-1.*" {
              set timBudgetPerLUT 0.575
            }
            "-2.*" {
              set timBudgetPerLUT 0.500
            }
            "-3.*" {
              set timBudgetPerLUT 0.425
            }
            default {
              set timBudgetPerLUT 0.575
            }
          }
        }
        kintexu -
        kintexum -
        virtexu -
        virtexum {
          switch -regexp -- $speedgrade {
            "-1.*" {
              set timBudgetPerLUT 0.490
            }
            "-2.*" {
              set timBudgetPerLUT 0.425
            }
            "-3.*" {
              set timBudgetPerLUT 0.360
            }
            default {
              set timBudgetPerLUT 0.490
            }
          }
        }
        zynquplus -
        kintexuplus -
        virtexuplus {
          switch -regexp -- $speedgrade {
            "-1.*" {
              set timBudgetPerLUT 0.350
            }
            "-2.*" {
              set timBudgetPerLUT 0.300
            }
            "-3.*" {
              set timBudgetPerLUT 0.250
            }
            default {
              set timBudgetPerLUT 0.350
            }
          }
        }
        default {
          puts " -E- architecture $architecture is not supported."
          incr error
        }
      }

      addMetric {design.device.maxlvls}   "Number of paths above max LUT budgeting (${timBudgetPerLUT}ns)"

      set spaths [get_timing_paths -quiet -setup -sort_by group -nworst 1 -max 20 -slack_less_than 2.0]
      set eps [get_property -quiet ENDPOINT_PIN $spaths]
      set sps [get_property -quiet STARTPOINT_PIN $spaths]
      set num 0
      foreach path $spaths \
              sp $sps \
              spref [get_property -quiet REF_NAME $sps] \
              ep $eps \
              epref [get_property -quiet REF_NAME $eps] {
        set requirement [get_property -quiet REQUIREMENT $path]
        set skew [get_property -quiet SKEW $path]
        set uncertainty [get_property -quiet UNCERTAINTY $path]
        set datapath_delay [get_property -quiet DATAPATH_DELAY $path]
        if {$skew == {}} { set skew 0.0 }
        if {$uncertainty == {}} { set uncertainty 0.0 }
        # Number of LUT* in the datapath
        set levels [llength [filter [get_cells -quiet -of $path] {REF_NAME =~ LUT*}]]
        if {![regexp {^FD} $spref] && ![regexp {^LD} $spref]} {
          # If the startpoint is not an FD* or a LD*, then account for it by increasing the number of levels
          incr levels
        }
        if {!([regexp {^FD} $epref] && ([get_property -quiet REF_PIN_NAME $ep] == {D}))} {
          # If the endpoint is not an FD*/D, then account for it by increasing the number of levels
          incr levels
        }
        # Calculate the maximum number of LUTs based on path requirement, skew and uncertainty
        set lut_budget [expr int(($requirement - $skew - $uncertainty) / double($timBudgetPerLUT)) ]
        # Calculate the maximum datapath based on path requirement, skew and uncertainty
        set datapath_budget [format {%.3f} [expr double($lut_budget) * double($timBudgetPerLUT)] ]
#         if {$datapath_budget > [expr $requirement - $skew - $uncertainty]} {}
        if {$levels > $lut_budget} {
          if {$params(debug)} {
            puts " -D- $path"
            puts " -D- levels=$levels / requirement=$requirement / skew=$skew / uncertainty=$uncertainty / lut_budget=$lut_budget / dp_budget=$datapath_budget / datapath_delay=$datapath_delay"
          }
          incr num
        } else {
#           puts " -I- $path"
#           puts " -I- levels=$levels / requirement=$requirement / skew=$skew / uncertainty=$uncertainty / lut_budget=$lut_budget / dp_budget=$datapath_budget / datapath_delay=$datapath_delay"
        }
      }
      setMetric {design.device.maxlvls}  $num
      set stepStopTime [clock seconds]
      puts " -I- max level metrics completed in [expr $stepStopTime - $stepStartTime] seconds"
    }

    ########################################################################################
    ##
    ## Dump all metrics (debug)
    ##
    ########################################################################################

    if {$params(debug)} {
      # Dump the list of metrics categories
      # E.g: metric = 'design.ram.blockram' -> category = 'design'
      set categories [list]
      foreach key [lsort [array names metrics *:def]] {
        lappend categories [lindex [split $key .] 0]
      }
      set categories [lsort -unique $categories]

      set tbl [::Table::Create {Design Summary}]
      $tbl indent 1
      $tbl header [list {Id} {Description} {Value}]
      foreach category $categories {
        $tbl separator
        foreach key [regsub -all {:def} [lsort [array names metrics $category.*:def]] {}] {
          # E.g: key = 'design.ram.blockram' -> metric = 'ram.blockram'
          regsub "$category." $key {} metric
          $tbl addrow [list $key $metrics(${key}:description) $metrics(${key}:val)]
        }
      }
      set output [concat $output [split [$tbl print] \n] ]
      catch {$tbl destroy}
      puts [join $output \n]
      set output [list]
    }

    ########################################################################################
    ##
    ##
    ##
    ########################################################################################

  } errorstring]} {
    puts " -E- $errorstring"
  }

  set stopTime [clock seconds]
#   puts " -I- report_failfast completed in [expr $stopTime - $startTime] seconds"

  ########################################################################################
  ##
  ## Table generation
  ##
  ########################################################################################

  set tbl [::Table::Create "Design Summary\n[get_property -quiet NAME [current_design]]\n[get_property -quiet PART [current_design]]"]
  $tbl indent 1
  $tbl header [list {Criteria} {Requirement} {Actual} {Status}]
  $tbl addrow [generateRow {utilization.clb.lut.pct}    {<=70%}   {LUT}]
  $tbl addrow [generateRow {utilization.clb.ff.pct}     {<=50%}   {FD}]
  $tbl addrow [generateRow {utilization.clb.lutmem.pct} {<=25%}   {LUTRAM+SRL}]
  $tbl addrow [generateRow {utilization.clb.carry8.pct} {<=25%}   {CARRY8}]
  $tbl addrow [generateRow {utilization.clb.f7mux.pct}  {<=15%}   {MUXF7}]
  $tbl addrow [generateRow {utilization.clb.f8mux.pct}  {<=7%}    {MUXF8}]
  $tbl addrow [generateRow {design.cells.hlutnm.pct}    {<=20%}   {HLUTNM}]
  $tbl addrow [generateRow {utilization.dsp.pct}        {<=80%}   {DSP48}]
  $tbl addrow [generateRow {utilization.ram.tile.pct}   {<=80%}   {RAMB36/FIFO36}]
  $tbl addrow [generateRow {utilization.bigblocks.pct}  {<=140%}  {DSP48+RAMB38}]
  $tbl addrow [generateRow {utilization.clk.all}        {<=24}    {BUFGCE* + BUFGCTRL}]
  $tbl addrow [generateRow {utilization.ctrlsets.uniq}  {<=10000} {Control Sets}]
  $tbl addrow [generateRow {design.cells.maxavgfo}      {<=4}     {Average Fanout for modules > 100k cells}]
  $tbl addrow [generateRow {design.nets.nonfdhfn}       {=0}      {Non-FD high fanout nets > 10k loads}]
  $tbl separator
  $tbl addrow [generateRow {methodology.timing-6}  {=0}  {TIMING-6}]
  $tbl addrow [generateRow {methodology.timing-7}  {=0}  {TIMING-7}]
  $tbl addrow [generateRow {methodology.timing-8}  {=0}  {TIMING-8}]
  $tbl addrow [generateRow {methodology.timing-14} {=0}  {TIMING-14}]
  $tbl addrow [generateRow {methodology.timing-35} {=0}  {TIMING-35}]
  $tbl separator
  $tbl addrow [generateRow {design.device.maxlvls} "=0"]

#   puts [$tbl print]
#   set output [concat $output [split [$tbl print] \n] ]
  foreach line [split [$tbl print] \n] {
    lappend output [format {# %s} $line]
  }
  catch {$tbl destroy}

  ########################################################################################
  ##
  ## CSV generation
  ##
  ########################################################################################
  set dir [file split [pwd]]
  set suite [lindex $dir end-2]
  set design [lindex $dir end-1]
  set csvrow [list]
  lappend csvrow [get_property -quiet PART [current_design -quiet]]
  lappend csvrow [get_property -quiet TOP [current_design -quiet]]
  lappend csvrow [getMetric {utilization.clb.lut}]
  lappend csvrow [getMetric {utilization.clb.ff}]
  lappend csvrow [getMetric {utilization.ram.tile}]
  lappend csvrow [getMetric {utilization.dsp}]
  lappend csvrow $params(failed)
  lappend csvrow [getMetric {utilization.clb.lut.pct}]
  lappend csvrow [getMetric {utilization.clb.ff.pct}]
  lappend csvrow [getMetric {utilization.clb.lutmem.pct}]
  lappend csvrow [getMetric {utilization.clb.carry8.pct}]
  lappend csvrow [getMetric {utilization.clb.f7mux.pct}]
  lappend csvrow [getMetric {utilization.clb.f8mux.pct}]
  lappend csvrow [getMetric {design.cells.hlutnm.pct}]
  lappend csvrow [getMetric {utilization.dsp.pct}]
  lappend csvrow [getMetric {utilization.ram.tile.pct}]
  lappend csvrow [getMetric {utilization.bigblocks.pct}]
  lappend csvrow [getMetric {utilization.clk.all}]
  lappend csvrow [getMetric {utilization.ctrlsets.uniq}]
  lappend csvrow [getMetric {design.cells.maxavgfo}]
  lappend csvrow [getMetric {design.nets.nonfdhfn}]
  lappend csvrow [getMetric {methodology.timing-6}]
  lappend csvrow [getMetric {methodology.timing-7}]
  lappend csvrow [getMetric {methodology.timing-8}]
  lappend csvrow [getMetric {methodology.timing-14}]
  lappend csvrow [getMetric {methodology.timing-35}]
  lappend csvrow [getMetric {design.device.maxlvls}]

  ########################################################################################
  ##
  ##
  ##
  ########################################################################################

  puts [join $output \n]

  if {$filename != {}} {
    set FH [open $filename $filemode]
    puts $FH "# ---------------------------------------------------------------------------------"
    puts $FH [format {# Created on %s with report_failfast (%s)} [clock format [clock seconds]] $::tb::utils::report_failfast::version ]
    puts $FH "# ---------------------------------------------------------------------------------\n"
    puts $FH "# Part,Top,LUT(#),FD(#),RAMB36/FIFO36(#),DSP48(#),Total Failures,LUT,FD,LUTRAM+SRL,CARRY8,MUXF7,MUXF8,HLUTNM,DSP48,RAMB36/FIFO36,DSP48+RAMB38,BUFGCE* + BUFGCTRL,Control Sets,Average Fanout for modules > 100k cells,Non-FD high fanout nets > 10k loads,TIMING-6,TIMING-7,TIMING-8,TIMING-14,TIMING-35,Number of paths above max LUT budgeting (${timBudgetPerLUT}ns)"
    puts $FH [join $csvrow ,]
    puts $FH ""
    puts $FH [join $output \n]
    close $FH
    puts " -I- Generated file [file normalize $filename]"
  } else {
#     puts [join $output \n]
  }

  puts " -I- Number of failures: $params(failed)"
  puts " -I- report_failfast completed in [expr $stopTime - $startTime] seconds"

  return $params(failed)
}

########################################################################################
##
## Helper Procs
##
########################################################################################

proc ::tb::utils::report_failfast::calculateAvgFanout {cell minCellCount} {
  variable data
  set current [current_instance -quiet .]
  current_instance -quiet
  current_instance -quiet $cell
  set hierCells [lsort [get_cells -quiet -filter {!IS_PRIMITIVE}]]
  foreach c $hierCells {
    calculateAvgFanout $c $minCellCount
  }

  set primitives [get_cells -quiet -filter {IS_PRIMITIVE && REF_NAME !~ BUFG* && REF_NAME !~ VCC && REF_NAME !~ GND}]
  set opins [get_pins -quiet -of $primitives -filter {!IS_CLOCK && DIRECTION == OUT && IS_CONNECTED}]
  set nets [get_nets -quiet -of $opins -filter {(FLAT_PIN_COUNT > 1) && (TYPE == SIGNAL)}]
  set avgFanout 0.0
  set totalFlatPinCount 0
  set numPins [llength $opins]
  set numPrimitives [llength $primitives]
  if {[llength $nets] != 0} {
    # Calculate total fanout of the cell
    set totalFlatPinCount [expr [join [get_property -quiet FLAT_PIN_COUNT $nets] +] ]
  }

  # Calculate the average pin fanout of the cell
  if {$numPins != 0} {
    set avgFanout [format {%.2f} [expr ((1.0 * $totalFlatPinCount) - $numPins) / $numPins ] ]
  } else {
    set avgFanout 0.0
  }

  set data(${cell}:PIN_COUNT) $totalFlatPinCount
  set data(${cell}:OPINS) $numPins
  set data(${cell}:PRIMITIVES) $numPrimitives
  set data(${cell}:AVG_FANOUT) $avgFanout

# puts "#primitives: [llength $primitives]"
# puts "#hierCells: [llength $hierCells]"
# puts "#opins: [llength $opins]"
# puts "#totalFlatPinCount: $totalFlatPinCount"

  foreach c $hierCells {
    set totalFlatPinCount [expr $totalFlatPinCount + $data(${c}:FLAT_PIN_COUNT)]
    set numPins [expr $numPins + $data(${c}:FLAT_OPINS)]
    set numPrimitives [expr $numPrimitives + $data(${c}:FLAT_PRIMITIVES)]
  }

  # Calculate the average pin fanout of the cell
  if {$numPins != 0} {
    set avgFanout [format {%.2f} [expr ((1.0 * $totalFlatPinCount) - $numPins) / $numPins ] ]
  } else {
    set avgFanout 0.0
  }

  set data(${cell}:FLAT_PIN_COUNT) $totalFlatPinCount
  set data(${cell}:FLAT_OPINS) $numPins
  set data(${cell}:FLAT_PRIMITIVES) $numPrimitives
  set data(${cell}:FLAT_AVG_FANOUT) $avgFanout

  if {$numPrimitives > $minCellCount} {
    lappend data(-) $avgFanout
#     puts "$cell / numPrimitives=$numPrimitives / avgFanout=$avgFanout"
  }

  current_instance -quiet $current
  # Make sure the memory is released
  set primitives {}
  set opins {}
  set nets {}
  set hierCells {}
  return $avgFanout
}

# Return the average fanout for a module
proc ::tb::utils::report_failfast::getAvgFanout {cell} {
  set current [current_instance -quiet .]
  current_instance -quiet
  current_instance -quiet $cell
  set primitives [get_cells -quiet -hierarchical -filter {IS_PRIMITIVE && PRIMITIVE_LEVEL != MACRO && REF_NAME !~ BUFG* && REF_NAME !~ VCC && REF_NAME !~ GND}]
  set opins [get_pins -quiet -of $primitives -filter {!IS_CLOCK && DIRECTION == OUT && IS_CONNECTED && IS_LEAF}]
  set nets [get_nets -quiet -of $opins -filter {(FLAT_PIN_COUNT > 1) && (TYPE == SIGNAL)}]
#   set avgFanout {N/A}
  set avgFanout 0.0
  if {[llength $nets] != 0} {
    # Calculate total fanout of the cell
    set totalFlatPinCount [expr [join [get_property -quiet FLAT_PIN_COUNT $nets] +] ]
    # Calculate the average pin fanout of the cell
    set avgFanout [format {%.2f} [expr ((1.0 * $totalFlatPinCount) - [llength $opins]) / [llength $opins] ] ]
  }
# puts "#primitives: [llength $primitives]"
# puts "#opins: [llength $opins]"
# puts "#totalFlatPinCount: $totalFlatPinCount"
  # Make sure the memory is released
  set primitives {}
  set opins {}
  set nets {}
  current_instance -quiet $current
  return $avgFanout
}

# Return the list modules that have a number of primitives more than <min>
# and a number of hierarchical orimitives more than <hmin>
proc ::tb::utils::report_failfast::getModules {level min hmin} {
  set current [current_instance -quiet .]
  set L [list]
  current_instance -quiet
  current_instance -quiet $level
  set primitives [get_cells -quiet -filter {IS_PRIMITIVE}]
  if {[llength $primitives] < $min} {
    set L {}
  } else {
    set L $level
  }
  set hierPrimitives [get_cells -quiet -hier -filter {IS_PRIMITIVE}]
  if {[llength $hierPrimitives] < $hmin} {
    current_instance -quiet $current
    # Make sure the memory is released
    set primitives {}
    set hierPrimitives {}
    return {}
  }
# puts -nonewline "Entering $level"
# puts " (hier=[llength $hierPrimitives]) (local=[llength $primitives])"
#   set L $level
  set hierCells [lsort [get_cells -quiet -filter {!IS_PRIMITIVE}]]
  foreach cell $hierCells {
    set L [concat $L [getModules $cell $min $hmin]]
  }
  current_instance -quiet $current
  # Make sure the memory is released
  set primitives {}
  set hierPrimitives {}
  set hierCells {}
  return $L
}

proc ::tb::utils::report_failfast::generateRow {name requirement {description {}}} {
  variable metrics
  variable params
  if {![info exists metrics(${name}:def)]} {
    puts " -E- metric '$name' does not exist"
    return {}
  }
#   set status {PASS}
  set status {OK}
  set suffix {}
  # Is the requirement expressed in %?
  if {[regexp {%$} $requirement]} {
    set suffix {%}
    regsub {%$} $requirement {} requirement
  }
  if {[regexp {^([^0-9]+)([0-9].*)$} $requirement - mode m]} {
    set requirement $m
  } else {
    set mode {<=}
  }
  if {$description == {}} {
    set description $metrics(${name}:description)
  }
  set value [getMetric $name]
  set row [list]
  lappend row $description
  lappend row ${requirement}${suffix}
  lappend row ${value}${suffix}
  switch $mode {
    "<=" {
      if {$value > $requirement} {
        set status {FAIL}
      }
    }
    "<" {
      if {$value >= $requirement} {
        set status {FAIL}
      }
    }
    ">=" {
      if {$value < $requirement} {
        set status {FAIL}
      }
    }
    ">" {
      if {$value <= $requirement} {
        set status {FAIL}
      }
    }
    "=" -
    "==" {
      if {$value != $requirement} {
        set status {FAIL}
      }
    }
    "!=" {
      if {$value == $requirement} {
        set status {FAIL}
      }
    }
  }
  if {$value == {n/a}} { set status {ERROR} }
  lappend row $status
  switch $status {
    FAIL -
    ERROR {
      incr params(failed)
    }
  }
  return $row
}

proc ::tb::utils::report_failfast::reset { {force 0} } {
  variable metrics
  variable params
  if {$params(debug) && !$force} {
    # Do not remove arrays in debug mode
    return -code ok
  }
  catch { unset metrics }
  array set reports [list]
  array set metrics [list]
  return -code ok
}

proc ::tb::utils::report_failfast::addMetric {name {description {}}} {
  variable metrics
  variable params
  if {[info exists metrics(${name}:def)]} {
    if {$params(verbose)} { puts " -W- metric '$name' already exist. Skipping new definition" }
    return -code ok
  }
  if {$description == {}} { set description $name }
  set metrics(${name}:def) 1
  set metrics(${name}:description) $description
  set metrics(${name}:val) {}
  return -code ok
}

proc ::tb::utils::report_failfast::getMetric {name} {
  variable metrics
  if {![info exists metrics(${name}:def)]} {
    puts " -E- metric '$name' does not exist"
    return {}
  }
  return $metrics(${name}:val)
}

proc ::tb::utils::report_failfast::setMetric {name value} {
  variable metrics
  if {![info exists metrics(${name}:def)]} {
    puts " -E- metric '$name' does not exist"
    return -code ok
  }
  dputs " -D- setting: $name = $value"
  set metrics(${name}:def) 2
  set metrics(${name}:val) $value
  return -code ok
}

proc ::tb::utils::report_failfast::extractMetric {&report name exp {notfound {n/a}} {save 1}} {
  variable metrics
  upvar ${&report} report
  if {![info exists metrics(${name}:def)]} {
    puts " -E- metric '$name' does not exist"
    return -code ok
  }
  if {![regexp -nocase -- $exp $report -- value]} {
    set value $notfound
    dputs " -D- failed to extract metric '$name' from report"
  }
  if {!$save} {
    return $value
  }
  setMetric $name $value
#   dputs " -D- setting: $name = $value"
#   set metrics(${name}:def) 2
#   set metrics(${name}:val) $value
  return -code ok
}

# Supports a list of patterns
proc ::tb::utils::report_failfast::extractMetric2 {&report name args} {
  variable metrics
  upvar ${&report} report
  array set defaults [list \
      -default {n/a} \
      -save 1 \
      -p [list] \
    ]
  array set options [array get defaults]
  array set options $args
  if {![info exists metrics(${name}:def)]} {
    puts " -E- metric '$name' does not exist"
    return -code ok
  }
  # Default value if not found in any pattern
  set value $options(-default)
  set found 0
  foreach exp $options(-p) {
    if {![regexp -nocase -- $exp $report -- value]} {
    } else {
      set found 1
      break
    }
  }
  if {!$found} {
    dputs " -D- failed to extract metric '$name' from report"
  }
  if {!$options(-save)} {
    return $value
  }
  setMetric $name $value
#   dputs " -D- setting: $name = $value"
#   set metrics(${name}:def) 2
#   set metrics(${name}:val) $value
  return -code ok
}

# Generate a list of integers
proc ::tb::utils::report_failfast::iota {from to} {
  set out [list]
  if {$from <= $to} {
    for {set i $from} {$i <= $to} {incr i}    {lappend out $i}
  } else {
    for {set i $from} {$i >= $to} {incr i -1} {lappend out $i}
  }
  return $out
}

proc ::tb::utils::report_failfast::dputs {args} {
  variable params
  if {$params(debug)} {
    catch { eval [concat puts $args] }
  }
  return -code ok
}

###########################################################################
##
## Simple package to handle printing of tables
##
## %> set tbl [Table::Create {this is my title}]
## %> $tbl header [list "name" "#Pins" "case_value" "user_case_value"]
## %> $tbl addrow [list A/B/C/D/E/F 12 - -]
## %> $tbl addrow [list A/B/C/D/E/F 24 1 -]
## %> $tbl separator
## %> $tbl addrow [list A/B/C/D/E/F 48 0 1]
## %> $tbl indent 0
## %> $tbl print
## +-------------+-------+------------+-----------------+
## | name        | #Pins | case_value | user_case_value |
## +-------------+-------+------------+-----------------+
## | A/B/C/D/E/F | 12    | -          | -               |
## | A/B/C/D/E/F | 24    | 1          | -               |
## +-------------+-------+------------+-----------------+
## | A/B/C/D/E/F | 48    | 0          | 1               |
## +-------------+-------+------------+-----------------+
## %> $tbl indent 2
## %> $tbl print
##   +-------------+-------+------------+-----------------+
##   | name        | #Pins | case_value | user_case_value |
##   +-------------+-------+------------+-----------------+
##   | A/B/C/D/E/F | 12    | -          | -               |
##   | A/B/C/D/E/F | 24    | 1          | -               |
##   +-------------+-------+------------+-----------------+
##   | A/B/C/D/E/F | 48    | 0          | 1               |
##   +-------------+-------+------------+-----------------+
## %> $tbl sort {-index 1 -increasing} {-index 2 -dictionary}
## %> $tbl print
## %> $tbl destroy
##
###########################################################################

# namespace eval Table { set n 0 }

# Trick to silence the linter
eval [list namespace eval ::Table {
  set n 0
} ]

proc ::Table::Create { {title {}} } { #-- constructor
  # Summary :
  # Argument Usage:
  # Return Value:

  variable n
  set instance [namespace current]::[incr n]
  namespace eval $instance { variable tbl [list]; variable header [list]; variable indent 0; variable title {}; variable numrows 0 }
  interp alias {} $instance {} ::Table::do $instance
  # Set the title
  $instance title $title
  set instance
}

proc ::Table::do {self method args} { #-- Dispatcher with methods
  # Summary :
  # Argument Usage:
  # Return Value:

  upvar #0 ${self}::tbl tbl
  upvar #0 ${self}::header header
  upvar #0 ${self}::numrows numrows
  switch -- $method {
      header {
        set header [lindex $args 0]
        return 0
      }
      addrow {
        eval lappend tbl $args
        incr numrows
        return 0
      }
      separator {
        eval lappend tbl {%%SEPARATOR%%}
        return 0
      }
      title {
        set ${self}::title [lindex $args 0]
        return 0
      }
      indent {
        set ${self}::indent $args
        return 0
      }
      print {
        eval ::Table::print $self
      }
      csv {
        eval ::Table::printcsv $self
      }
      length {
        return $numrows
      }
      sort {
        # Each argument is a list of: <lsort arguments>
        set command {}
        while {[llength $args]} {
          if {$command == {}} {
            set command "lsort [[namespace parent]::lshift args] \$tbl"
          } else {
            set command "lsort [[namespace parent]::lshift args] \[$command\]"
          }
        }
        if {[catch { set tbl [eval $command] } errorstring]} {
          puts " -E- $errorstring"
        } else {
        }
      }
      reset {
        set ${self}::tbl [list]
        set ${self}::header [list]
        set ${self}::indent 0
        set ${self}::title {}
        return 0
      }
      destroy {
        set ${self}::tbl [list]
        set ${self}::header [list]
        set ${self}::indent 0
        set ${self}::title {}
        namespace delete $self
        return 0
      }
      default {error "unknown method $method"}
  }
}

proc ::Table::print {self} {
   upvar #0 ${self}::tbl table
   upvar #0 ${self}::header header
   upvar #0 ${self}::indent indent
   upvar #0 ${self}::title title
   set maxs {}
   foreach item $header {
       lappend maxs [string length $item]
   }
   set numCols [llength $header]
   foreach row $table {
       if {$row eq {%%SEPARATOR%%}} { continue }
       for {set j 0} {$j<$numCols} {incr j} {
            set item [lindex $row $j]
            set max [lindex $maxs $j]
            if {[string length $item]>$max} {
               lset maxs $j [string length $item]
           }
       }
   }
  set head " [string repeat " " [expr $indent * 4]]+"
  foreach max $maxs {append head -[string repeat - $max]-+}

  # Generate the title
  if {$title ne {}} {
    # The upper separator should something like +----...----+
    append res " [string repeat " " [expr $indent * 4]]+[string repeat - [expr [string length [string trim $head]] -2]]+\n"
    # Suports multi-lines title
    foreach line [split $title \n] {
      append res " [string repeat " " [expr $indent * 4]]| "
      append res [format "%-[expr [string length [string trim $head]] -4]s" $line]
      append res " |\n"
    }
  }

  # Generate the table header
  append res $head\n
  # Generate the table rows
  set first 1
  set numsep 0
  foreach row [concat [list $header] $table] {
      if {$row eq {%%SEPARATOR%%}} {
        incr numsep
        if {$numsep == 1} { append res $head\n }
        continue
      } else {
        set numsep 0
      }
      append res " [string repeat " " [expr $indent * 4]]|"
      foreach item $row max $maxs {append res [format " %-${max}s |" $item]}
      append res \n
      if {$first} {
        append res $head\n
        set first 0
        incr numsep
      }
  }
  append res $head
  set res
}

proc ::Table::printcsv {self args} {
  upvar #0 ${self}::tbl table
  upvar #0 ${self}::header header
  upvar #0 ${self}::title title

  array set defaults [list \
      -delimiter {,} \
    ]
  array set options [array get defaults]
  array set options $args
  set sepChar $options(-delimiter)

  set res {}
  # Support for multi-lines title
  set first 1
  foreach line [split $title \n] {
    if {$first} {
      set first 0
      append res "# title${sepChar}[::Table::list2csv [list $line] $sepChar]\n"
    } else {
      append res "#      ${sepChar}[::Table::list2csv [list $line] $sepChar]\n"
    }
  }
  append res "[::Table::list2csv $header $sepChar]\n"
  set count 0
  set numsep 0
  foreach row $table {
    incr count
    if {$row eq {%%SEPARATOR%%}} {
      incr numsep
      if {$numsep == 1} {
        append res "# [::Table::list2csv {++++++++++++++++++++++++++++++++++++++++++++++++++} $sepChar]\n"
      }
      continue
    } else {
      set numsep 0
    }
    append res "[::Table::list2csv $row $sepChar]\n"
  }
  return $res
}

proc ::Table::list2csv { list {sepChar ,} } {
  set out ""
  set sep {}
  foreach val $list {
    if {[string match "*\[\"$sepChar\]*" $val]} {
      append out $sep\"[string map [list \" \"\"] $val]\"
    } else {
      append out $sep\"$val\"
    }
    set sep $sepChar
  }
  return $out
}

namespace eval ::tb::utils {
  namespace import -force ::tb::utils::report_failfast::report_failfast
}

namespace eval ::tb {
  namespace import -force ::tb::utils::report_failfast
}

namespace import -force ::tb::report_failfast

# Call ilself ...
set CWD [uplevel #0 pwd]
::tb::utils::report_failfast -file [file join $CWD failfast.csv]

