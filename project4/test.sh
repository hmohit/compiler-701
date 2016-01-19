clang -emit-llvm -O0 -c $1.c -o $1.bc
opt -mem2reg $1.bc > $1.ssa
mv -f $1.ssa $1.bc
llc -optimize-regalloc=0 -load Debug/lib/P4.so -regalloc=gc $1.bc
