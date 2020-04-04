; ModuleID = 'main.c'
source_filename = "main.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.arg = type { i8, i8 }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.arg*, align 8
  %3 = alloca i8, align 1
  store i32 0, i32* %1, align 4
  %4 = call noalias i8* @malloc(i64 2) #3
  %5 = bitcast i8* %4 to %struct.arg*
  store %struct.arg* %5, %struct.arg** %2, align 8
  %6 = load %struct.arg*, %struct.arg** %2, align 8
  %7 = getelementptr inbounds %struct.arg, %struct.arg* %6, i32 0, i32 0
  store i8 1, i8* %7, align 1
  %8 = load %struct.arg*, %struct.arg** %2, align 8
  %9 = getelementptr inbounds %struct.arg, %struct.arg* %8, i32 0, i32 1
  store i8 2, i8* %9, align 1
  %10 = load %struct.arg*, %struct.arg** %2, align 8
  %11 = call signext i8 @foo(%struct.arg* %10)
  store i8 %11, i8* %3, align 1
  %12 = load %struct.arg*, %struct.arg** %2, align 8
  %13 = bitcast %struct.arg* %12 to i8*
  call void @free(i8* %13) #3
  %14 = load i8, i8* %3, align 1
  %15 = sext i8 %14 to i32
  ret i32 %15
}

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i64) #1

declare dso_local signext i8 @foo(%struct.arg*) #2

; Function Attrs: nounwind
declare dso_local void @free(i8*) #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 11.0.0-++20200330082552+4e0d9925d6a-1~exp1~20200330063148.154 "}
