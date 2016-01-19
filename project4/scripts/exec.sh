#! /bin/bash

cp ../TESTS/*.h . 
cp ../TESTS/*.input . 

rm -rf Results

make clean
make
mkdir Results

#replace, space, tst-params -- give out error 

for test in "for" "if" "loop" "math" "mbr1" "schedule" "switch_return" "switch_return_call" "tcas" "try" "tst-array" "while"
do

	echo "Testing" $test
	cp ../TESTS/$test.c . 
	
	cp ../TESTS/EXPECTED/$test.expected Results
	
	##PRINTRANGES TEST
	make $test.reg
	make $test.exe  
	
	if [ "$test" == "tcas" ]; then
		cp ../TESTS/EXPECTED/$test.withinput.expected Results
		./$test.exe 600 1 1 10 500 0 0 0 0 0 1 0    1> Results/$test.withinput.expected.res
	elif [ "$test" == "schedule" ]; then
		cp ../TESTS/EXPECTED/$test.withinput.expected Results
		./$test.exe 1 2 3 4 < $test.input						1> Results/$test.withinput.expected.res
	fi
	
	./$test.exe 1> Results/$test.expected.res

	echo "TESTS done -- Comparing results"
	
	if diff -B -b "Results/$test.expected" "Results/$test.expected.res" > /dev/null; then
		echo "Ouput files same -- $test PASSED"; rm -rf Results/$test.expected Results/$test.expected.res
	else
		echo "Ouput files different -- $test FAILED. Check Results Dir"
	fi

	if [ "$test" == "tcas" ]; then
		if diff -B -b "Results/$test.withinput.expected" "Results/$test.withinput.expected.res" > /dev/null; then
			echo "Ouput files with i/p same -- $test PASSED"; rm -rf Results/$test.withinput.expected Results/$test.withinput.expected.res
		else
			echo "Ouput files with i/p different -- $test FAILED. Check Results Dir"
		fi
	fi

	if [ "$test" == "schedule" ]; then
		if diff -B -b "Results/$test.withinput.expected" "Results/$test.withinput.expected.res" > /dev/null; then
			echo "Ouput files with i/p same -- $test PASSED"; rm -rf Results/$test.withinput.expected Results/$test.withinput.expected.res
		else
			echo "Ouput files with i/p different -- $test FAILED. Check Results Dir"
		fi
	fi

	echo $'\n'
done

rm -rf *.c *.bc *.opt *.o *.h *.exe *.input
make clean
