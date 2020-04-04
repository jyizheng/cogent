; ModuleID = 'adder.cogent'
source_filename = "adder.cogent"
target datalayout = "e"

define i8 @foo({ i8, i8 }*) {
entry:
  %1 = getelementptr inbounds { i8, i8 }, { i8, i8 }* %0, i32 0, i32 0
  %2 = load atomic i8, i8* %1 monotonic, align 1
  %3 = getelementptr inbounds { i8, i8 }, { i8, i8 }* %0, i32 0, i32 1
  %4 = load atomic i8, i8* %3 monotonic, align 1
  %5 = add nuw i8 %2, %4
  ret i8 %5
}
