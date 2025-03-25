(** Copyright 2024, Vlasenco Daniel and Kudrya Alexandr *)

(** SPDX-License-Identifier: MIT *)

open Typecheck.Inference
open Typecheck.Types
open Ast

(* Определяем встроенное окружение для операторов,
   чтобы тестовые выражения (например, для факториала или Фибоначчи)
   могли использовать арифметические и логические операции *)
let builtins =
  [ "=", Scheme ([ 0 ], TFun (TVar 0, TFun (TVar 0, TBool)))
  ; "-", Scheme ([], TFun (TInt, TFun (TInt, TInt)))
  ; "*", Scheme ([], TFun (TInt, TFun (TInt, TInt)))
  ; "+", Scheme ([], TFun (TInt, TFun (TInt, TInt)))
  ; "<", Scheme ([], TFun (TInt, TFun (TInt, TBool)))
  ]
;;

(* Начальное окружение состоит из встроенных операторов.
   initial_env из модуля Inference изначально пустое. *)
let env = builtins @ initial_env

(* Простой тест: функция-идентичность: fun x -> x *)
let id_expr = Expr_lam (Pattern_ident_or_op "x", Expr_ident_or_op "x")
let _sId, tId = infer env id_expr

let%expect_test "Identity function" =
  Printf.printf "Inferred type for identity: %s\n" (string_of_ty tId);
  [%expect {|
    Inferred type for identity: ('a0 -> 'a0)
  |}]
;;

(* Простой тест: функция, возвращающая константу: fun x -> 1 *)
let const_expr = Expr_lam (Pattern_ident_or_op "x", Expr_const (Const_int 1))
let _sConst, tConst = infer env const_expr

let%expect_test "Constant function" =
  Printf.printf "Inferred type for constant function: %s\n" (string_of_ty tConst);
  [%expect {|
    Inferred type for constant function: ('a0 -> int)
  |}]
;;

(* Тест: функция факториала (let rec fact = fun n -> if n < 1 then 1 else n * fact (n - 1) in fact) *)
let fact_expr =
  Expr_let
    ( Recursive
    , Bind
        ( Pattern_ident_or_op "fact"
        , Expr_lam
            ( Pattern_ident_or_op "n"
            , Expr_ifthenelse
                ( (* if n < 1 then 1 *)
                  Expr_apply
                    ( Expr_apply (Expr_ident_or_op "<", Expr_ident_or_op "n")
                    , Expr_const (Const_int 1) )
                , Expr_const (Const_int 1)
                , Some
                    ((* else n * fact (n - 1) *)
                       Expr_apply
                       ( Expr_apply (Expr_ident_or_op "*", Expr_ident_or_op "n")
                       , Expr_apply
                           ( Expr_ident_or_op "fact"
                           , Expr_apply
                               ( Expr_apply (Expr_ident_or_op "-", Expr_ident_or_op "n")
                               , Expr_const (Const_int 1) ) ) )) ) ) )
    , []
    , Expr_ident_or_op "fact" )
;;

let _sFact, tFact = infer env fact_expr

let%expect_test "Factorial function" =
  Printf.printf "Inferred type for factorial: %s\n" (string_of_ty tFact);
  [%expect {|
    Inferred type for factorial: (int -> int)
  |}]
;;

(* Тест: функция Фибоначчи (let rec fib = fun n -> if n < 2 then n else fib (n - 1) + fib (n - 2) in fib) *)
let fib_expr =
  Expr_let
    ( Recursive
    , Ast.Bind
        ( Pattern_ident_or_op "fib"
        , Expr_lam
            ( Pattern_ident_or_op "n"
            , Expr_ifthenelse
                ( (* if n < 2 then n *)
                  Expr_apply
                    ( Expr_apply (Expr_ident_or_op "<", Expr_ident_or_op "n")
                    , Expr_const (Const_int 2) )
                , Expr_ident_or_op "n"
                , Some
                    ((* else fib (n - 1) + fib (n - 2) *)
                       Expr_apply
                       ( Expr_apply
                           ( Expr_ident_or_op "+"
                           , Expr_apply
                               ( Expr_ident_or_op "fib"
                               , Expr_apply
                                   ( Expr_apply
                                       (Expr_ident_or_op "-", Expr_ident_or_op "n")
                                   , Expr_const (Const_int 1) ) ) )
                       , Expr_apply
                           ( Expr_ident_or_op "fib"
                           , Expr_apply
                               ( Expr_apply (Expr_ident_or_op "-", Expr_ident_or_op "n")
                               , Expr_const (Const_int 2) ) ) )) ) ) )
    , []
    , Expr_ident_or_op "fib" )
;;

let _sFib, tFib = infer env fib_expr

let%expect_test "Fibonacci function" =
  Printf.printf "Inferred type for fibonacci: %s\n" (string_of_ty tFib);
  [%expect {| Inferred type for fibonacci: (int -> int)
    |}]
;;

(* Тест: константа с единицей измерения: 5.0<cm> *)
let unit_expr =
  Expr_const
    (Const_unit_of_measure (Unit_of_measure (Mnum_float 5.0, Measure_ident "cm")))
;;

let _sUnit, tUnit = infer env unit_expr

let%expect_test "Unit of measure constant" =
  Printf.printf "Inferred type for unit constant: %s\n" (string_of_ty tUnit);
  [%expect {|
    Inferred type for unit constant: float<cm>
  |}]
;;

(* Тест: списковое выражение: [1; 2; 3] *)
let list_expr =
  Expr_list
    [ Expr_const (Const_int 1); Expr_const (Const_int 2); Expr_const (Const_int 3) ]
;;

let _sList, tList = infer env list_expr

let%expect_test "List literal" =
  Printf.printf "Inferred type for list: %s\n" (string_of_ty tList);
  [%expect {|
    Inferred type for list: list<int>
  |}]
;;

(* Тест: let–связывание (не рекурсивное): let x = 1 and y = 2 in x *)
let let_expr =
  Expr_let
    ( Nonrecursive
    , Ast.Bind (Pattern_ident_or_op "x", Expr_const (Const_int 1))
    , [ Ast.Bind (Pattern_ident_or_op "y", Expr_const (Const_int 2)) ]
    , Expr_ident_or_op "x" )
;;

let _sLet, tLet = infer env let_expr

let%expect_test "Non-recursive let binding" =
  Printf.printf "Inferred type for non-recursive let: %s\n" (string_of_ty tLet);
  [%expect {|
    Inferred type for non-recursive let: int
  |}]
;;

let%expect_test "Typed pattern in lambda" =
  let expr =
    Expr_lam
      ( Pattern_typed (Pattern_ident_or_op "x", Type_ident "int")
      , Expr_apply
          ( Expr_apply (Expr_ident_or_op "+", Expr_ident_or_op "x")
          , Expr_const (Const_int 1) ) )
  in
  let _s, t = infer env expr in
  let t' = apply_subst _s t in
  Printf.printf "Type for typed-lambda: %s\n" (string_of_ty t');
  [%expect {|
  Type for typed-lambda: (int -> int)
|}]
;;

let%expect_test "Pattern match on list with different lengths" =
  (* fun xs ->
     match xs with
     | [] -> 0
     | [x] -> x
     | [x; y] -> x + y
  *)
  let expr =
    Expr_lam
      ( Pattern_ident_or_op "xs"
      , Expr_match
          ( Expr_ident_or_op "xs"
          , Rule (Pattern_list [], Expr_const (Const_int 0))
          , [ Rule (Pattern_list [ Pattern_ident_or_op "x" ], Expr_ident_or_op "x")
            ; Rule
                ( Pattern_list [ Pattern_ident_or_op "x"; Pattern_ident_or_op "y" ]
                , Expr_apply
                    ( Expr_apply (Expr_ident_or_op "+", Expr_ident_or_op "x")
                    , Expr_ident_or_op "y" ) )
            ] ) )
  in
  let _s, t = infer env expr in
  let t' = apply_subst _s t in
  Printf.printf "Match on list yields type: %s\n" (string_of_ty t');
  [%expect {|
      Match on list yields type: (list<int> -> int)
    |}]
;;

let%expect_test "Add measure mismatch" =
  let expr =
    Expr_let
      ( Nonrecursive
      , Bind
          ( Pattern_ident_or_op "x"
          , Expr_const
              (Const_unit_of_measure (Unit_of_measure (Mnum_int 5, Measure_ident "cm")))
          )
      , []
      , Expr_apply
          ( Expr_apply (Expr_ident_or_op "+", Expr_ident_or_op "x")
          , Expr_const (Const_int 3) ) )
  in
  (try
     let _s, t = infer env expr in
     let t' = apply_subst _s t in
     Printf.printf "Inferred type: %s\n" (string_of_ty t')
   with
   | TypeError msg -> Printf.printf "Type error: %s\n" msg
   | Typecheck.Unification.UnificationError msg ->
     Printf.printf "Unification error: %s\n" msg);
  [%expect {|
      Unification error: Cannot unify types: int and int<cm>
    |}]
;;

let%expect_test "Sum of list with pattern-list" =
  let sumList_expr =
    Expr_let
      ( Recursive
      , Bind
          ( Pattern_ident_or_op "sumList"
          , Expr_lam
              ( Pattern_ident_or_op "xs"
              , Expr_match
                  ( Expr_ident_or_op "xs"
                  , Rule (Pattern_list [], Expr_const (Const_int 0))
                  , [ Rule (Pattern_list [ Pattern_ident_or_op "x" ], Expr_ident_or_op "x")
                    ; Rule
                        ( Pattern_list [ Pattern_ident_or_op "x"; Pattern_ident_or_op "y" ]
                        , Expr_apply
                            ( Expr_apply (Expr_ident_or_op "+", Expr_ident_or_op "x")
                            , Expr_ident_or_op "y" ) )
                    ] ) ) )
      , []
      , Expr_ident_or_op "sumList" )
  in
  let _sSum, tSum = infer env sumList_expr in
  Printf.printf "Inferred type for sumList: %s\n" (string_of_ty tSum);
  [%expect {| Inferred type for sumList: (list<int> -> int)    |}]
;;

let simple_option_test =
  Expr_let
    ( Nonrecursive
    , Ast.Bind (Pattern_ident_or_op "x", Expr_option (Some (Expr_const (Const_int 42))))
    , []
    , Expr_match
        ( Expr_ident_or_op "x"
        , Rule (Pattern_option (Some (Pattern_ident_or_op "y")), Expr_ident_or_op "y")
        , [ Rule (Pattern_option None, Expr_const (Const_int 0)) ] ) )
;;

let _s, t = infer env simple_option_test

let%expect_test "Simple option function" =
  Printf.printf "Inferred type for simple option: %s\n" (string_of_ty t);
  [%expect {| Inferred type for simple option: int
    |}]
;;

let complex_option_test =
  Expr_let
    ( Recursive
    , Ast.Bind
        ( Pattern_ident_or_op "nested_option_map"
        , Expr_lam
            ( Pattern_ident_or_op "f"
            , Expr_lam
                ( Pattern_ident_or_op "opt"
                , Expr_match
                    ( Expr_ident_or_op "opt"
                    , Rule (Pattern_option None, Expr_option None)
                    , [ Rule
                          ( Pattern_option (Some (Pattern_ident_or_op "x"))
                          , Expr_match
                              ( Expr_ident_or_op "x"
                              , Rule
                                  ( Pattern_option None
                                  , Expr_option (Some (Expr_option None)) )
                              , [ Rule
                                    ( Pattern_option (Some (Pattern_ident_or_op "y"))
                                    , Expr_option
                                        (Some
                                           (Expr_option
                                              (Some
                                                 (Expr_apply
                                                    ( Expr_ident_or_op "f"
                                                    , Expr_ident_or_op "y" ))))) )
                                ] ) )
                      ] ) ) ) )
    , []
    , Expr_apply
        ( Expr_apply
            ( Expr_ident_or_op "nested_option_map"
            , Expr_lam
                ( Pattern_ident_or_op "x"
                , Expr_apply
                    ( Expr_apply (Expr_ident_or_op "*", Expr_ident_or_op "x")
                    , Expr_const (Const_int 2) ) ) )
        , Expr_option (Some (Expr_option (Some (Expr_const (Const_int 21))))) ) )
;;

let _s, t = infer env complex_option_test

let%expect_test "Compex option function" =
  Printf.printf "Inferred type for complex option: %s\n" (string_of_ty t);
  [%expect {| Inferred type for complex option: option<option<int>>
    |}]
;;
