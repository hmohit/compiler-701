clang -emit-llvm -O0 -c switch_return.c -o switch_return.bc
opt -mem2reg switch_return.bc > switch_return.mem2reg
mv switch_return.mem2reg switch_return.bc
llc -mcpu=generic -optimize-regalloc=0 -load Debug/lib/P4.so -regalloc=gc switch_return.bc

INITIAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %70 %71 }
R43: { %71 }
R43: { %80 %81 }
R46: { %68 %69 %70 %71 }
R48: { %67 %68 %69 %70 %71 }
R49: { %1 }
R49: { %3 }
R49: { %12 %13 }
R49: { %15 %16 }
R49: { %18 %19 %20 %21 }
R49: { %22 %23 %24 %25 }
R49: { %37 %38 %39 %40 %41 }
R49: { %43 }
R49: { %44 %45 %46 %47 %48 }
R49: { %51 %52 %53 %54 %55 }
R49: { %64 }
R49: { %72 }
R49: { %79 }
R53: { %66 %67 %68 %69 %70 %71 }
R76: { %69 %70 %71 }
R110: { %65 %66 %67 %68 %69 %70 %71 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %71 %72 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %72 %73 %74 %75 %76 %77 %78 }

Virtual Registers
%0: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 }
%1: { %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %31 %32 }
%2: { %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 }
%3: { %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 }
%4: { %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 }
%5: { %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 }
%6: { %57 %58 %59 }
%7: { %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 }
%8: { %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 }
%9: { %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 }
%10: { %73 %74 }
%13: { %1 %2 %3 %4 %5 %6 %7 }
%15: { %79 %80 }
%18: { %31 %32 %33 }
%19: { %27 %28 %29 }
%20: { %36 %37 %38 %39 %40 }
%21: { %43 %44 %45 %46 %47 }
%22: { %50 %51 %52 %53 }
%23: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 }
%24: { %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 }
%26: { %4 %5 %6 %7 %8 }
%26: { %8 %74 %75 %76 %77 %78 }
%27: { %5 %6 %7 %8 %9 }
%27: { %8 %9 %75 %76 %77 %78 }
%28: { %6 %7 %8 %9 %10 }
%28: { %8 %9 %10 %76 %77 %78 }
%29: { %7 %8 %9 %10 %11 }
%29: { %8 %9 %10 %11 %77 %78 }
%30: { %19 %20 %21 %34 }
%30: { %23 %24 %25 %26 %34 }
%30: { %28 %29 %30 %34 }
%30: { %32 %33 %34 }
%31: { %20 %21 %34 %35 }
%31: { %24 %25 %26 %34 %35 }
%31: { %29 %30 %34 %35 }
%31: { %33 %34 %35 }
%32: { %38 %39 %40 %41 %42 %61 }
%32: { %45 %46 %47 %48 %49 %61 }
%32: { %52 %53 %54 %55 %56 %61 }
%32: { %58 %59 %60 %61 }
%33: { %39 %40 %41 %42 %61 %62 }
%33: { %46 %47 %48 %49 %61 %62 }
%33: { %53 %54 %55 %56 %61 %62 }
%33: { %59 %60 %61 %62 }
%34: { %40 %41 %42 %61 %62 %63 }
%34: { %47 %48 %49 %61 %62 %63 }
%34: { %54 %55 %56 %61 %62 %63 }
%34: { %60 %61 %62 %63 }


FINAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %70 %71 }
R43: { %71 }
R43: { %80 %81 }
R46: { %68 %69 %70 %71 }
R48: { %67 %68 %69 %70 %71 }
R49: { %1 }
R49: { %3 }
R49: { %12 %13 }
R49: { %15 %16 }
R49: { %18 %19 %20 %21 }
R49: { %22 %23 %24 %25 }
R49: { %37 %38 %39 %40 %41 }
R49: { %43 }
R49: { %44 %45 %46 %47 %48 }
R49: { %51 %52 %53 %54 %55 }
R49: { %64 }
R49: { %72 }
R49: { %79 }
R53: { %66 %67 %68 %69 %70 %71 }
R76: { %69 %70 %71 }
R110: { %65 %66 %67 %68 %69 %70 %71 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 }

Virtual Registers
%0: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 }
%1: { %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %31 %32 }
%2: { %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 }
%3: { %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 }
%4: { %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 }
%5: { %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 }
%6: { %57 %58 %59 }
%7: { %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 }
%8: { %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 }
%9: { %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 }
%10: { %73 %74 }
%13: { %1 %2 %3 %4 %5 %6 %7 }
%15: { %79 %80 }
%18: { %31 %32 %33 }
%19: { %27 %28 %29 }
%20: { %36 %37 %38 %39 %40 }
%21: { %43 %44 %45 %46 %47 }
%22: { %50 %51 %52 %53 }
%23: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 }
%24: { %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 }
%26: { %4 %5 %6 %7 %8 %74 %75 %76 %77 %78 }
%27: { %5 %6 %7 %8 %9 %75 %76 %77 %78 }
%28: { %6 %7 %8 %9 %10 %76 %77 %78 }
%29: { %7 %8 %9 %10 %11 %77 %78 }
%30: { %19 %20 %21 %23 %24 %25 %26 %28 %29 %30 %32 %33 %34 }
%31: { %20 %21 %24 %25 %26 %29 %30 %33 %34 %35 }
%32: { %38 %39 %40 %41 %42 %45 %46 %47 %48 %49 %52 %53 %54 %55 %56 %58 %59 %60 %61 }
%33: { %39 %40 %41 %42 %46 %47 %48 %49 %53 %54 %55 %56 %59 %60 %61 %62 }
%34: { %40 %41 %42 %47 %48 %49 %54 %55 %56 %60 %61 %62 %63 }






gcc -lm switch_return.s -o switch_return.exe