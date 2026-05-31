; ModuleID = 'loop_unswitching.c'
source_filename = "loop_unswitching.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-redhat-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @func(i1 noundef zeroext %0, i1 noundef zeroext %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i8, align 1
  %5 = zext i1 %0 to i8
  store i8 %5, ptr %3, align 1
  %6 = zext i1 %1 to i8
  store i8 %6, ptr %4, align 1
  br label %7

7:                                                ; preds = %15, %2
  %8 = load i8, ptr %3, align 1
  %9 = trunc i8 %8 to i1
  br i1 %9, label %10, label %16

10:                                               ; preds = %7
  %11 = load i8, ptr %4, align 1
  %12 = trunc i8 %11 to i1
  br i1 %12, label %13, label %14

13:                                               ; preds = %10
  call void (...) @foo()
  br label %15

14:                                               ; preds = %10
  call void (...) @bar()
  br label %15

15:                                               ; preds = %14, %13
  br label %7, !llvm.loop !4

16:                                               ; preds = %7
  ret i32 1
}

declare dso_local void @foo(...) #1

declare dso_local void @bar(...) #1

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"uwtable", i32 2}
!2 = !{i32 7, !"frame-pointer", i32 2}
!3 = !{!"clang version 21.1.8 (Fedora 21.1.8-4.fc43)"}
!4 = distinct !{!4, !5}
!5 = !{!"llvm.loop.mustprogress"}
