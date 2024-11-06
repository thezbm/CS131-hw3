open Util.Assert
open Gradedtests
    
let parse_ll_string str =
  let program =
    str
    |> Lexing.from_string
    |> Llparser.prog Lllexer.token
  in
  program

let exec_ll_string str =
  let ast = parse_ll_string str in
  exec_e2e_ast ast "" []

let executed tests =
  List.map
    (fun (llstring, ans) ->
      llstring, assert_eqf (fun () -> exec_ll_string llstring) ans)
    tests

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let my_tests =
  (* This program checks if a number is odd. *)
  [ 100, 0L
  ; 201, 1L
  ; 0, 0L
  ; 1, 1L
  ; 902, 0L
  ]
  |> List.map (fun (n, res) ->
{|
%struct1 = type { i64 }
%struct2 = type { %struct1 }
%array1 = type [1 x %struct2]
%array2 = type [1 x %array1]
%struct = type { %array2 }

@ans = global %struct { %array2 [ %array1 [ %struct2 { %struct1 { i64 0 } } ] ] }

define i64 @not(i64 %nx) {
  %ncmp = icmp eq i64 0, %nx
  br i1 %ncmp, label %then, label %else
then:
  ret i64 1
else:
  ret i64 0
}

define i64 @foo(i64 %fx) {
  %fcmp = icmp eq i64 0, %fx
  br i1 %fcmp, label %then, label %else
then:
  ret i64 0
else:
  %fansptr = getelementptr %struct, %struct* @ans, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0
  %fans1 = load i64, i64* %fansptr
  %fans2 = call i64 @not(i64 %fans1)
  store i64 %fans2, i64* %fansptr
  %f1 = sub i64 %fx, 1
  %f2 = call i64 @bar(i64 %f1)
  ret i64 %f2
}

define i64 @bar(i64 %bx) {
  %bcmp = icmp eq i64 0, %bx
  br i1 %bcmp, label %then, label %else
then:
  ret i64 1
else:
  %bansptr = getelementptr %struct, %struct* @ans, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0
  %bans1 = load i64, i64* %bansptr
  %bans2 = call i64 @not(i64 %bans1)
  store i64 %bans2, i64* %bansptr
  %b1 = sub i64 %bx, 1
  %b2 = call i64 @foo(i64 %b1)
  ret i64 %b2
}

define i64 @is_odd(i64 %n) {
  %res = call i64 @foo(i64 %n)
  ret i64 %res
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @is_odd(i64 |} ^ Format.sprintf "%d" n ^ {|)
  %ansptr = getelementptr %struct, %struct* @ans, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0
  %ans1 = load i64, i64* %ansptr
  %cmp = icmp eq i64 %ans1, %1
  br i1 %cmp, label %then, label %else
then:
  ret i64 %ans1
else:
  ret i64 -1
}
|}, res)

let provided_tests : suite = [
  Test("my tests", executed my_tests)
] 
