# Retain intermediate bitcode files
.PRECIOUS: %.bc

# The default target builds the plugin
plugin:
	make -C lib/p3

# run loopInv on a .c file
%.loopInv:
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc
	(opt -load Debug/lib/P3.so -loopInv -stats $*.bc > $*.opt) >& $*.loopInv

#
# create sample output for a .c file with PROFITABLE defined
%.profitable:
	make clean
	cp lib/p3/flags.profitable lib/p3/flags.h
	make
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc
	(opt -load Debug/lib/P3.so -loopInv -stats $*.bc > $*.opt) >& $*.out
	sort $*.out >& $*.profitable

# run printCode on a .c file and save output in a .printCode file
%.saveprintCode: %.c
	rm -f  $*.printCode
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc
	opt -load Debug/lib/P3.so -printCode $*.bc > /dev/null >& $*.printCode

#
# run printCode on a .c file
%.printCode: %.c
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc
	opt -load Debug/lib/P3.so -printCode $*.bc > /dev/null

# run printCode on an optimized .opt file
%.printOpt: %.opt
	opt -load Debug/lib/P3.so -printCode $*.opt > /dev/null


# create mem2reg optimized .bc from source
%.mem2reg:	%.c
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc


# create executable from .bc
%.exe: %.bc
	llc $^
	gcc $*.s -o $*.exe

# create human-readable assemly (.ll) from .c
%.ll: %.c
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc
	llvm-dis $*.bc

# clean up generated files
clean:
	make -C lib/p3 clean
	rm -f *.bc *.exe *.ll *.s
