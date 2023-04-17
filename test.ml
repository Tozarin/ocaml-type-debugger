let rec foo x = match x with 10 -> 0 | n -> foo (n + 1) in
foo 1