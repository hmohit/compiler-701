clang -emit-llvm -O0 -c mbr1.c -o mbr1.bc
opt -mem2reg mbr1.bc > mbr1.mem2reg
mv mbr1.mem2reg mbr1.bc
llc -mcpu=generic -optimize-regalloc=0 -load Debug/lib/P4.so -regalloc=gc mbr1.bc

INITIAL LIVE RANGES FOR FUNCTION foo

Physical Registers
R2: { %40 %41 }
R43: { %41 }
R46: { %1 }
R47: { %1 %2 %3 %4 }
R49: { %7 %8 }
R49: { %14 }
R49: { %18 }
R49: { %22 }
R49: { %27 }
R49: { %32 }
R49: { %36 }
R49: { %38 }
R49: { %42 }
R53: { %1 %2 %3 }
R110: { %39 %40 %41 }
R111: { %1 %2 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %36 }
R115: { %36 %37 %38 %39 %40 %41 }
R115: { %41 %42 }
R115: { %42 }

Virtual Registers
%0: { %10 %11 }
%1: { %13 %14 }
%1: { %14 %15 }
%2: { %17 %18 }
%2: { %18 %19 }
%3: { %23 %24 }
%4: { %28 %29 }
%5: { %33 %34 }
%6: { %44 %45 }
%7: { %4 %5 %6 %7 %8 %9 %10 %13 %17 %21 %26 %31 }
%8: { %3 %4 %5 %6 %7 %8 %9 %10 %13 %14 %17 %18 %21 %22 %26 %27 %31 %32 }
%9: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %44 %45 }
%10: { %1 %2 %3 %4 %5 }
%11: { %6 %7 %8 %9 }
%12: { %5 %6 %7 }
%14: { %31 %32 }
%14: { %32 %33 }
%15: { %26 %27 }
%15: { %27 %28 }
%16: { %21 %22 }
%16: { %22 %23 }
%17: { %37 %38 %39 }
%18: { %38 %39 %40 }
%20: { %11 %12 %44 }
%20: { %15 %16 %44 }
%20: { %19 %20 %44 }
%20: { %24 %25 %44 }
%20: { %29 %30 %44 }
%20: { %34 %35 %44 }


FINAL LIVE RANGES FOR FUNCTION foo

Physical Registers
R2: { %40 %41 }
R43: { %41 }
R46: { %1 }
R47: { %1 %2 %3 %4 }
R49: { %7 %8 }
R49: { %14 }
R49: { %18 }
R49: { %22 }
R49: { %27 }
R49: { %32 }
R49: { %36 }
R49: { %38 }
R49: { %42 }
R53: { %1 %2 %3 }
R110: { %39 %40 %41 }
R111: { %1 %2 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %36 %37 %38 %39 %40 %41 %42 }

Virtual Registers
%0: { %10 %11 }
%1: { %13 %14 %15 }
%2: { %17 %18 %19 }
%3: { %23 %24 }
%4: { %28 %29 }
%5: { %33 %34 }
%6: { %44 %45 }
%7: { %4 %5 %6 %7 %8 %9 %10 %13 %17 %21 %26 %31 }
%8: { %3 %4 %5 %6 %7 %8 %9 %10 %13 %14 %17 %18 %21 %22 %26 %27 %31 %32 }
%9: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %44 %45 }
%10: { %1 %2 %3 %4 %5 }
%11: { %6 %7 %8 %9 }
%12: { %5 %6 %7 }
%14: { %31 %32 %33 }
%15: { %26 %27 %28 }
%16: { %21 %22 %23 }
%17: { %37 %38 %39 }
%18: { %38 %39 %40 }
%20: { %11 %12 %15 %16 %19 %20 %24 %25 %29 %30 %34 %35 %44 }


INITIAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %39 %40 }
R43: { %40 }
R43: { %43 %44 }
R46: { %9 %10 }
R46: { %20 %21 }
R46: { %29 %30 }
R47: { %6 %7 %8 %9 %10 }
R47: { %17 %18 %19 %20 %21 }
R47: { %26 %27 %28 %29 %30 }
R49: { %1 }
R49: { %11 }
R49: { %13 }
R49: { %22 }
R49: { %24 }
R49: { %31 }
R49: { %34 }
R49: { %36 }
R49: { %41 }
R53: { %7 %8 %9 %10 }
R53: { %18 %19 %20 %21 }
R53: { %27 %28 %29 %30 }
R53: { %38 %39 %40 }
R110: { %37 %38 %39 %40 }
R111: { %8 %9 %10 }
R111: { %19 %20 %21 }
R111: { %28 %29 %30 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 }
R115: { %10 %11 }
R115: { %11 %12 %13 }
R115: { %13 %14 %15 %16 %17 %18 %19 %20 %21 }
R115: { %21 %22 }
R115: { %22 %23 %24 }
R115: { %24 %25 %26 %27 %28 %29 %30 }
R115: { %30 %31 }
R115: { %31 %32 %33 %34 %35 %36 }
R115: { %36 %37 %38 %39 %40 }
R115: { %40 %41 }
R115: { %41 }

Virtual Registers
%0: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 }
%1: { %3 %4 %5 %6 %7 }
%2: { %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 }
%3: { %5 %6 %7 %8 %9 }
%4: { %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 }
%5: { %15 %16 %17 %18 }
%6: { %16 %17 %18 %19 %20 }
%7: { %25 %26 }
%8: { %32 %33 %34 %35 %36 %37 }
%9: { %33 %34 %35 %36 %37 %38 }
%10: { %34 %35 %36 %37 %38 %39 }
%12: { %42 %43 }


FINAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %39 %40 }
R43: { %40 }
R43: { %43 %44 }
R46: { %9 %10 }
R46: { %20 %21 }
R46: { %29 %30 }
R47: { %6 %7 %8 %9 %10 }
R47: { %17 %18 %19 %20 %21 }
R47: { %26 %27 %28 %29 %30 }
R49: { %1 }
R49: { %11 }
R49: { %13 }
R49: { %22 }
R49: { %24 }
R49: { %31 }
R49: { %34 }
R49: { %36 }
R49: { %41 }
R53: { %7 %8 %9 %10 }
R53: { %18 %19 %20 %21 }
R53: { %27 %28 %29 %30 }
R53: { %38 %39 %40 }
R110: { %37 %38 %39 %40 }
R111: { %8 %9 %10 }
R111: { %19 %20 %21 }
R111: { %28 %29 %30 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 }

Virtual Registers
%0: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 }
%1: { %3 %4 %5 %6 %7 }
%2: { %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 }
%3: { %5 %6 %7 %8 %9 }
%4: { %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 }
%5: { %15 %16 %17 %18 }
%6: { %16 %17 %18 %19 %20 }
%7: { %25 %26 }
%8: { %32 %33 %34 %35 %36 %37 }
%9: { %33 %34 %35 %36 %37 %38 }
%10: { %34 %35 %36 %37 %38 %39 }
%12: { %42 %43 }

gcc -lm mbr1.s -o mbr1.exe
