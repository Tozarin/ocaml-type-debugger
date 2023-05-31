  $ ./test.exe pre_inited test1
  types are correct


  $ ./test.exe pre_inited test2
  types are correct


  $ ./test.exe pre_inited test3
  (UnifyFail (
     (TGround (Int,
        [(ApplyAs (1,
            (TArrow ((TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               (TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               { old_lvl = 1; new_lvl = 1 }, [])),
            File "_none_", line 7, characters 10-19));
          (ApplyAs (3,
             (TArrow ((TGround (Int, [])),
                (TArrow ((TGround (Int, [])), (TGround (Int, [])),
                   { old_lvl = 0; new_lvl = 0 }, [])),
                { old_lvl = 0; new_lvl = 0 }, [])),
             File "_none_", line 3, characters 15-22))
          ]
        )),
     (TGround (String,
        [(InitConst (String, File "_none_", line 7, characters 14-19))]))
     ))
