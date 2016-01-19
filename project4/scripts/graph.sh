#! /bin/bash

cp ../TESTS/*.h . 

rm -rf Results

##Build Normal tests (WITHOUT PRINTANALYSIS)
##echo "Enter the test name - for, if, loop, math, mbr1, replace, schedule, space, switch_return, switch_return_call, tcas, tst_array, tst-param, while"
##read test

make clean
make
mkdir Results

#replace, space tst-params -- give out error 

for test in "for" "if" "loop" "math" "mbr1" "schedule" "switch_return" "switch_return_call" "tcas" "try" "tst-array" "while" "replace" "space" "tst-params"
do

	echo "Testing" $test
	cp ../TESTS/$test.c . 
	
	cp ../TESTS/EXPECTED/$test.printGraph.expected Results
	
	##PRINTRANGES TEST
	make $test.reg &> Results/$test.printgraph.res 
	make $test.exe &>> Results/$test.printgraph.res 

	

	echo "TESTS done -- Comparing results"
	
	if diff -B -b "Results/$test.printGraph.expected" "Results/$test.printgraph.res" > /dev/null; then
		echo "PrintGraph files same -- $test PASSED"; rm -rf Results/$test.printGraph.expected Results/$test.printgraph.res
	else
		echo "PrintGraph files different -- $test FAILED. Check Results Dir"
	fi

	echo $'\n'
done

rm -rf *.c *.bc *.opt *.o *.h *.exe
make clean
