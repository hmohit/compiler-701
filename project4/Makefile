# The default target builds the plugin
plugin:
	make -C lib/p4

.PRECIOUS: %.bc

# do register allocation
%.reg: %.bc
	llc -mcpu=generic -optimize-regalloc=0 -load Debug/lib/P4.so -regalloc=gc $*.bc

%.exe: %.s
	gcc -lm $*.s -o $*.exe

%.bc:	%.c
	clang -emit-llvm -O0 -c $*.c -o $*.bc
	opt -mem2reg $*.bc > $*.mem2reg
	mv $*.mem2reg $*.bc

clean:
	make -C lib/p4 clean
	rm -f *.bc *.ll *.s *.exe *~
