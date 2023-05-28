  $ ./test.exe pre_inited test1
  (UnifyFail (
     (TGround (Int,
        [(ApplyAs (1,
            (TArrow ((TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               (TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               { old_lvl = 1; new_lvl = 0 }, [])),
            File "_none_", line 6, characters 0-12));
          (PatConst (Int, File "_none_", line 3, characters 6-7))]
        )),
     (TGround (String,
        [(InitConst (String, File "_none_", line 6, characters 4-12))]))
     ))


  $ ./test.exe pre_inited test2
  (UnifyFail (
     (TGround (Int,
        [(ApplyAs (1,
            (TArrow ((TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               (TVar (ref ((Link ((TGround (Int, [])), []))), [])),
               { old_lvl = 1; new_lvl = 0 }, [])),
            File "_none_", line 4, characters 0-9));
          (ApplyAs (1,
             (TArrow ((TGround (Int, [])),
                (TArrow ((TGround (Int, [])), (TGround (Int, [])),
                   { old_lvl = 0; new_lvl = 0 }, [])),
                { old_lvl = 0; new_lvl = 0 }, [])),
             File "_none_", line 2, characters 2-7))
          ]
        )),
     (TGround (String,
        [(InitConst (String, File "_none_", line 4, characters 4-9))]))
     ))



  $ ./test.exe pre_inited test3
  (UnifyFail (
     (TGround (Int, [(InitConst (Int, File "_none_", line 1, characters 0-1))]
        )),
     (TArrow (
        (TGround (String,
           [(InitConst (String, File "_none_", line 1, characters 2-7))])),
        (TVar (
           ref ((Unbound ("a", 0,
                   [(ResultOfWithoutName File "_none_", line 1, characters 0-7)
                     ]
                   ))),
           [])),
        { old_lvl = 0; new_lvl = 0 }, [NoReason]))
     ))


  $ ./test.exe pre_inited test4
  types are correct
