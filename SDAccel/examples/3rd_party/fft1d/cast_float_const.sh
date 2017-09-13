#!/bin/sh

sed 's/\([0-9]\)\( \{0,\}[,}]\)/\1f\2/g' twid_radix4_8.cl > tmp
mv tmp twid_radix4_8.cl
