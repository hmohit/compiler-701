#! /bin/bash

cp ./TESTS/*.h . 

rm -rf Results

##Build Normal tests (WITHOUT PRINTANALYSIS)
##echo "Enter the test name - for, if, loop, math, mbr1, replace, schedule, space, switch_return, switch_return_call, tcas, tst_array, tst-param, while"
##read test

make clean
make
mkdir Results

#replace, space tst-params -- give out error ##DONT FORGET TO DELETE THE CODE which has been added to just support this 

for test in "for" "if" "loop" "math" "mbr1" "schedule" "switch_return" "switch_return_call" "tcas" "try" "tst-array" "while" "replace" "tst-params"
do

	echo "Testing" $test
	cp ./TESTS/$test.c . 
	
	cp ./TESTS/EXPECTED/$test.printRanges.expected Results
	
	##PRINTRANGES TEST
	make $test.reg &> Results/$test.printranges.res 
	make $test.exe &>> Results/$test.printranges.res 

	

	echo "TESTS done -- Comparing results"
	
	if diff -B -b "Results/$test.printRanges.expected" "Results/$test.printranges.res" > /dev/null; then
		echo "PrintRanges files same -- $test PASSED"; rm -rf Results/$test.printRanges.expected Results/$test.printranges.res
	else
		echo "PrintRanges files different -- $test FAILED. Check Results Dir"
	fi

	echo $'\n'
done

rm -rf *.c *.bc *.opt *.o *.h *.exe
make clean
