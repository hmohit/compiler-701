#!/bin/sh
clear
rm -rf debug.cfg 
make clean
make 

echo "Type the input name"
read inp

make $inp.reg &> debug.cfg
#gcc $inp.s -o $inp

