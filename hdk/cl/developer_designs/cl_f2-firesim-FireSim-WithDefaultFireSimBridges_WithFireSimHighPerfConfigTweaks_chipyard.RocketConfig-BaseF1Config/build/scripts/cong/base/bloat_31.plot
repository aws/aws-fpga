set title "bloat_31"
set palette negative rgbformula 21,22,23
set cbrange [0:2]
set yrange [720:0]
set size ratio 2.36066
set view map
splot "bloat_31.dat" using 1:2:3 with image
pause -1
