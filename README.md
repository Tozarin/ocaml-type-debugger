# ocaml-type-debugger ![build](https://github.com/tozarin/lambda/actions/workflows/act.yml/badge.svg) [![test coverage](https://coveralls.io/repos/github/Tozarin/ocaml-type-debugger/badge.svg?branch=main)](https://coveralls.io/github/Tozarin/ocaml-type-debugger?branch=main)
Type inferer for subset of OCaml with expanded explanations of errors. It implements original OCaml inference algol.

## Example
Code:
```
let foo x =
    match x with 
    | 1 -> x 
    | _ -> 1 
in
foo "string"
```

Output:
```
(UnifyFail (                        
   (TGround (Int,
      [(ApplyAs (1,
          (TArrow ((TVar (ref ((Link ((TGround (Int, [])), []))), [])),
             (TVar (ref ((Link ((TGround (Int, [])), []))), [])),
             { old_lvl = 1; new_lvl = 0 }, [])),
          File "_none_", line 2, characters 0-12));
        (PatConst (Int, File "_none_", line 1, characters 25-26))]
      )),
   (TGround (String,
      [(InitConst (String, File "_none_", line 2, characters 4-12))]))
   ))
```

## How to use
- clone repo
- `dune build`
- `dune exec main <filename>` or `./main.exe <filename>`