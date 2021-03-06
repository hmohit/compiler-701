clang -emit-llvm -O0 -c switch_return_call.c -o switch_return_call.bc
opt -mem2reg switch_return_call.bc > switch_return_call.mem2reg
mv switch_return_call.mem2reg switch_return_call.bc
llc -mcpu=generic -optimize-regalloc=0 -load Debug/lib/P4.so -regalloc=gc switch_return_call.bc

INITIAL LIVE RANGES FOR FUNCTION foo

Physical Registers
R43: { %2 %3 }
R47: { %1 }

Virtual Registers
%0: { %1 %2 }


FINAL LIVE RANGES FOR FUNCTION foo

Physical Registers
R43: { %2 %3 }
R47: { %1 }

Virtual Registers
%0: { %1 %2 }


INITIAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %90 %91 }
R43: { %31 }
R43: { %40 %41 %42 }
R43: { %81 %82 %83 }
R43: { %91 }
R43: { %101 %102 }
R46: { %88 %89 %90 %91 }
R47: { %30 %31 }
R47: { %39 %40 }
R47: { %80 %81 }
R48: { %87 %88 %89 %90 %91 }
R49: { %1 }
R49: { %3 }
R49: { %12 %13 }
R49: { %15 %16 }
R49: { %18 %19 %20 %21 %22 }
R49: { %23 %24 %25 %26 %27 }
R49: { %29 }
R49: { %32 }
R49: { %38 }
R49: { %41 }
R49: { %52 %53 %54 %55 %56 }
R49: { %58 }
R49: { %59 %60 %61 %62 %63 }
R49: { %66 %67 %68 %69 %70 }
R49: { %79 }
R49: { %82 }
R49: { %84 }
R49: { %92 }
R49: { %100 }
R53: { %86 %87 %88 %89 %90 %91 }
R76: { %89 %90 %91 }
R110: { %85 %86 %87 %88 %89 %90 %91 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %29 %30 %31 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %31 %32 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %32 %33 %34 %35 %36 %37 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %38 %39 %40 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %40 %41 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %81 %82 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %82 %83 %84 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %84 %85 %86 %87 %88 %89 %90 %91 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %91 %92 }
R115: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %38 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %92 %93 %94 %95 %96 %97 %98 %99 }

Virtual Registers
%0: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %38 %39 }
%1: { %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %38 %39 %40 %41 %42 %43 %44 %45 %46 }
%2: { %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 }
%3: { %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 }
%4: { %44 %45 }
%5: { %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 }
%6: { %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 }
%7: { %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 }
%8: { %72 %73 %74 }
%9: { %76 %77 %78 %79 %80 }
%10: { %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 }
%11: { %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 }
%12: { %94 %95 %96 }
%13: { %93 %94 %95 }
%16: { %1 %2 %3 %4 %5 %6 %7 }
%18: { %100 %101 }
%21: { %43 %44 %45 %46 %47 }
%22: { %42 %43 %44 }
%23: { %33 %34 %35 %36 }
%25: { %51 %52 %53 %54 %55 }
%26: { %58 %59 %60 %61 %62 }
%27: { %65 %66 %67 %68 }
%28: { %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 }
%29: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 %99 }
%30: { %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 %99 }
%32: { %4 %5 %6 %7 %8 }
%32: { %8 %95 %96 %97 %98 %99 }
%33: { %5 %6 %7 %8 %9 }
%33: { %8 %9 %96 %97 %98 %99 }
%34: { %6 %7 %8 %9 %10 }
%34: { %8 %9 %10 %97 %98 %99 }
%35: { %7 %8 %9 %10 %11 }
%35: { %8 %9 %10 %11 %98 %99 }
%36: { %19 %20 %21 %22 %48 }
%36: { %24 %25 %26 %27 %28 %48 }
%36: { %34 %35 %36 %37 %48 }
%36: { %45 %46 %47 %48 }
%37: { %20 %21 %22 %48 %49 }
%37: { %25 %26 %27 %28 %48 %49 }
%37: { %35 %36 %37 %48 %49 }
%37: { %46 %47 %48 %49 }
%38: { %21 %22 %48 %49 %50 }
%38: { %26 %27 %28 %48 %49 %50 }
%38: { %36 %37 %48 %49 %50 }
%38: { %47 %48 %49 %50 }
%39: { %53 %54 %55 %56 %57 %76 }
%39: { %60 %61 %62 %63 %64 %76 }
%39: { %67 %68 %69 %70 %71 %76 }
%39: { %73 %74 %75 %76 }
%40: { %54 %55 %56 %57 %76 %77 }
%40: { %61 %62 %63 %64 %76 %77 }
%40: { %68 %69 %70 %71 %76 %77 }
%40: { %74 %75 %76 %77 }
%41: { %55 %56 %57 %76 %77 %78 }
%41: { %62 %63 %64 %76 %77 %78 }
%41: { %69 %70 %71 %76 %77 %78 }
%41: { %75 %76 %77 %78 }


FINAL LIVE RANGES FOR FUNCTION main

Physical Registers
R2: { %90 %91 }
R43: { %31 }
R43: { %40 %41 %42 }
R43: { %81 %82 %83 }
R43: { %91 }
R43: { %101 %102 }
R46: { %88 %89 %90 %91 }
R47: { %30 %31 }
R47: { %39 %40 }
R47: { %80 %81 }
R48: { %87 %88 %89 %90 %91 }
R49: { %1 }
R49: { %3 }
R49: { %12 %13 }
R49: { %15 %16 }
R49: { %18 %19 %20 %21 %22 }
R49: { %23 %24 %25 %26 %27 }
R49: { %29 }
R49: { %32 }
R49: { %38 }
R49: { %41 }
R49: { %52 %53 %54 %55 %56 }
R49: { %58 }
R49: { %59 %60 %61 %62 %63 }
R49: { %66 %67 %68 %69 %70 }
R49: { %79 }
R49: { %82 }
R49: { %84 }
R49: { %92 }
R49: { %100 }
R53: { %86 %87 %88 %89 %90 %91 }
R76: { %89 %90 %91 }
R110: { %85 %86 %87 %88 %89 %90 %91 }
R115: { %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 %99 }

Virtual Registers
%0: { %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %38 %39 }
%1: { %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %38 %39 %40 %41 %42 %43 %44 %45 %46 }
%2: { %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 }
%3: { %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 }
%4: { %44 %45 }
%5: { %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 }
%6: { %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 }
%7: { %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 }
%8: { %72 %73 %74 }
%9: { %76 %77 %78 %79 %80 }
%10: { %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 }
%11: { %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 }
%12: { %94 %95 %96 }
%13: { %93 %94 %95 }
%16: { %1 %2 %3 %4 %5 %6 %7 }
%18: { %100 %101 }
%21: { %43 %44 %45 %46 %47 }
%22: { %42 %43 %44 }
%23: { %33 %34 %35 %36 }
%25: { %51 %52 %53 %54 %55 }
%26: { %58 %59 %60 %61 %62 }
%27: { %65 %66 %67 %68 }
%28: { %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 }
%29: { %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 %99 }
%30: { %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30 %31 %32 %33 %34 %35 %36 %37 %38 %39 %40 %41 %42 %43 %44 %45 %46 %47 %48 %49 %50 %51 %52 %53 %54 %55 %56 %57 %58 %59 %60 %61 %62 %63 %64 %65 %66 %67 %68 %69 %70 %71 %72 %73 %74 %75 %76 %77 %78 %79 %80 %81 %82 %83 %84 %85 %86 %87 %88 %89 %90 %91 %92 %93 %94 %95 %96 %97 %98 %99 }
%32: { %4 %5 %6 %7 %8 %95 %96 %97 %98 %99 }
%33: { %5 %6 %7 %8 %9 %96 %97 %98 %99 }
%34: { %6 %7 %8 %9 %10 %97 %98 %99 }
%35: { %7 %8 %9 %10 %11 %98 %99 }
%36: { %19 %20 %21 %22 %24 %25 %26 %27 %28 %34 %35 %36 %37 %45 %46 %47 %48 }
%37: { %20 %21 %22 %25 %26 %27 %28 %35 %36 %37 %46 %47 %48 %49 }
%38: { %21 %22 %26 %27 %28 %36 %37 %47 %48 %49 %50 }
%39: { %53 %54 %55 %56 %57 %60 %61 %62 %63 %64 %67 %68 %69 %70 %71 %73 %74 %75 %76 }
%40: { %54 %55 %56 %57 %61 %62 %63 %64 %68 %69 %70 %71 %74 %75 %76 %77 }
%41: { %55 %56 %57 %62 %63 %64 %69 %70 %71 %75 %76 %77 %78 }






gcc -lm switch_return_call.s -o switch_return_call.exe
