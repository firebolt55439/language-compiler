target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.8.0"

%struct.FILE = type opaque
%struct.va_list = type opaque
%struct.fpos_t = type opaque
%class_struct.Testing = type { i32, i32, i32 }

@stdin = global %struct.FILE* null
@stdout = global %struct.FILE* null
@stderr = global %struct.FILE* null
@SEEK_SET = global i32 0
@SEEK_CUR = global i32 1
@SEEK_END = global i32 2
@.str = private constant [4 x i8] c"%d\0A\00"

; Function Attrs: noinline nounwind uwtable
declare i32 @remove(i8*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @rename(i8*, i8*) #0

; Function Attrs: noinline nounwind uwtable
declare %struct.FILE* @tmpfile() #0

; Function Attrs: noinline nounwind uwtable
declare i8* @tmpname(i8*) #0

; Function Attrs: noinline nounwind uwtable
declare %struct.FILE* @fdopen(i32, i8*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fclose(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fflush(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare %struct.FILE* @fopen(i8*, i8*) #0

; Function Attrs: noinline nounwind uwtable
declare %struct.FILE* @freopen(i8*, i8*, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare void @setbuf(%struct.FILE*, i8*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @setvbuf(%struct.FILE*, i8*, i32, i64) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fprintf(%struct.FILE*, i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fscanf(%struct.FILE*, i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @printf(i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @scanf(i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @sprintf(i8*, i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @sscanf(i8*, i8*, ...) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @vfprintf(%struct.FILE*, i8*, %struct.va_list) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @vprintf(i8*, %struct.va_list) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @vsprintf(i8*, i8*, %struct.va_list) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fgetc(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i8* @fgetc1(i8*, i32, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fputc(i32, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fputs(i8*, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @getc(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @getchar() #0

; Function Attrs: noinline nounwind uwtable
declare i8* @gets(i8*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @putc(i32, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @putchar(i32) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @puts(i8*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @ungetc(i32, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i64 @fread(i8*, i64, i64, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i64 @fwrite(i8*, i64, i64, %struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fgetpos(%struct.FILE*, %struct.fpos_t*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fseek(%struct.FILE*, i64, i32) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @fsetpos(%struct.FILE*, %struct.fpos_t*) #0

; Function Attrs: noinline nounwind uwtable
declare i64 @ftell(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare void @rewind(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare void @clearerr(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @feof(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @ferror(%struct.FILE*) #0

; Function Attrs: noinline nounwind uwtable
declare void @perror(i8*) #0

; Function Attrs: noinline nounwind uwtable
declare void @srand(i32) #0

; Function Attrs: noinline nounwind uwtable
declare i32 @rand() #0

; Function Attrs: noinline nounwind uwtable
declare double @pow(double, double) #0

; Function Attrs: noinline nounwind uwtable
define %class_struct.Testing* @Testing(i32 %x) #0 {
entry:
  %__class_ptr_ctor = alloca %class_struct.Testing
  %__classmembergeptmp1 = getelementptr inbounds %class_struct.Testing* %__class_ptr_ctor, i32 0, i32 1
  store i32 %x, i32* %__classmembergeptmp1
  ret %class_struct.Testing* %__class_ptr_ctor
}

; Function Attrs: noinline nounwind uwtable
define %class_struct.Testing* @Testing2() #0 {
entry:
  %__class_ptr_ctor = alloca %class_struct.Testing
  %__classmembergeptmp = getelementptr inbounds %class_struct.Testing* %__class_ptr_ctor, i32 0, i32 0
  %__classmembergeptmp1 = getelementptr inbounds %class_struct.Testing* %__class_ptr_ctor, i32 0, i32 1
  %__classmembergeptmp2 = getelementptr inbounds %class_struct.Testing* %__class_ptr_ctor, i32 0, i32 2
  store i32 0, i32* %__classmembergeptmp
  store i32 0, i32* %__classmembergeptmp2
  store i32 0, i32* %__classmembergeptmp1
  ret %class_struct.Testing* %__class_ptr_ctor
}

; Function Attrs: noinline nounwind uwtable
define void @test1(%class_struct.Testing* %__class_ptr, i32 %test, ...) #0 {
entry:
  ret void
}

; Function Attrs: noinline nounwind uwtable
define void @tester(%class_struct.Testing* %__class_ptr, i32 %t) #0 {
entry:
  %__classmembergeptmp = getelementptr inbounds %class_struct.Testing* %__class_ptr, i32 0, i32 0
  %__classmembergeptmp1 = getelementptr inbounds %class_struct.Testing* %__class_ptr, i32 0, i32 1
  store i32 %t, i32* %__classmembergeptmp
  store i32 %t, i32* %__classmembergeptmp1
  ret void
}

; Function Attrs: noinline nounwind uwtable
define void @tester3(%class_struct.Testing* %__class_ptr, i64 %t) #0 {
entry:
  %__classmembergeptmp = getelementptr inbounds %class_struct.Testing* %__class_ptr, i32 0, i32 0
  %castinst = trunc i64 %t to i32
  store i32 %castinst, i32* %__classmembergeptmp
  call void @tester(%class_struct.Testing* %__class_ptr, i32 1)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define i32 @main(i32 %argc, i8** %argv) #0 {
entry:
  %class_test = alloca %class_struct.Testing
  %structmembertmp3 = getelementptr inbounds %class_struct.Testing* %class_test, i32 0, i32 1
  %structmemberloadtmp4 = load i32* %structmembertmp3
  %calltmp = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %structmemberloadtmp4)
  ret i32 0
}

attributes #0 = { noinline nounwind uwtable }
