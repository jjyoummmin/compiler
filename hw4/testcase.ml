open Analysis

type  testcases = testcase list
and   testcase  = command

let testcase : testcases = [
  ( (* 1 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 5), While (Neg (Le (Var "a", Int 0)), Seq(Assign ("a", Minus (Var "a", Int 1)), Assign ("b", Plus (Var "b", Int 1))))) );
  ( (* 2 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 20), Seq (Assign ("c", Int 0), While (Conj (Neg (Le (Var "a", Int 0)), Neg (Le (Var "b", Int 15))), Seq (Assign ("a", Minus (Var "a", Int 5)), Seq (Assign ("b", Minus (Var "b", Var "a")), Assign ("c", Int (-1))))))) );
  ( (* 3 *) Seq (Assign ("a", Int 0), Seq (Assign ("b", Int 0), Seq (Assign ("c", Int 100), While (Neg (Le (Var "c", Var "a")), Seq (Assign ("a", Plus (Var "a", Var "b")), Seq (Assign ("b", Plus (Var "b", Int 2)), Assign ("c", Minus (Var "c", Var "a"))))))) );
  ( (* 4 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 0), Seq (While (Neg (Le (Var "a", Int 0)), Seq(Assign ("b", Minus (Var "b", Int 1)), Assign ("a", Plus (Var "a", Var "b")))), If ((Le (Var "a", Int 0)), Assign ("a", Mult (Var "a", Int (-1))), Assign ("b", Mult (Var "b", Int (-1)))))) );
  ( (* 5 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 0), Seq (Assign ("c", Int 5), Seq (While (Neg (Eq (Var "a", Var "b")), Seq (Assign ("a", Minus (Var "a", Int 1)), Assign ("b", Plus (Var "b", Int 1)))), Seq (If (Eq (Var "c", Var "a"), Assign ("a", Mult (Var "a", Int 0)), Skip), Assign ("c", Int 0))))) );
  ( (* 6 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 2), Seq (Assign ("c", Int 0), Seq (While (Le (Int 0, Var "a"), Seq (Assign ("c", Plus (Var "c", Var "b")), Assign ("a", Minus (Var "a", Var "b")))), If (Eq (Var "c", Int 10), Assign ("b", Plus (Var "b", Var "a")), Assign ("c", Mult (Var "c", Int (-1))))))) );
  ( (* 7 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 2), Seq (Assign ("c", Int 1), Seq (If (Neg (Le (Var "a", Int 0)), While (Le (Var "c", Var "a"), Seq (Assign ("c", Mult (Var "c", Var "b")), Assign ("a", Minus (Var "a", Var "b")))), Skip), If (Neg (Conj (Neg (Le (Var "b", Var "a")), Le (Int 0, Var "c"))), Skip, Assign ("a", Var "c"))))) );
  ( (* 8 *) Seq (Assign ("a", Int 10), Seq (Assign ("b", Int 2), Seq (Assign ("c", Int 1), Seq (Assign ("d", Int 0), Seq (While (Conj (Le (Var "c", Int 32), Le (Int 0, Var "a")), Seq (Assign ("c", Mult (Var "c", Var "b")), Seq (Assign ("a", Minus (Var "a", Var "b")), Assign ("d", Plus (Var "d", Var "c"))))), If (Le (Var "a", Var "b"), Assign ("a", Int 0), If (Neg (Le (Var "d", Int 0)), Assign ("b", Mult (Var "b", Int (-1))), Assign ("c", Mult (Var "c", Int (-1))))))))) );
  ( (* 9 *) Seq (Assign ("s", Int 10), Seq (Assign ("d", Int 5), Seq (Assign ("a", Int 1), While (Neg (Eq (Var "s", Var "d")), Seq (Assign ("a", Mult (Var "a", Var "s")), Assign ("s", Minus (Var "s", Int 1)))))) );
  ( (* 10 *) Seq (Assign ("a", Int 1), Seq (Assign ("b", Int (-1)), Seq (Assign ("c", Plus (Var "a", Var "b")), Seq (Assign ("d", Minus (Var "a", Var "b")), Seq (Assign ("e", Mult (Var "a", Var "b")), If (Le (Var "a", Var "b"), Assign ("f", Plus (Var "d", Var "e")), Assign ("f", Minus (Var "d", Var "e"))))))) );
  ( (* 11 *) Seq (Assign ("x", Int 0), While (Le (Var "x", Int 10), Assign ("x", Plus (Var "x", Int 1))) );
  ( (* 12 *) Seq (Assign ("x", Int 27), Seq (Assign ("y", Int (-3)), Seq (Assign ("z", Mult (Var "x", Int 2)), Seq (Assign ("z", Minus (Var "z", Var "y")), If (Neg (Le (Int 0, Var "x")), Assign ("y", Minus (Var "z", Int 3)), Assign ("y", Int 12))))) );
  ( (* 13 *) Seq (Assign ("x", Int 3), Seq (Assign ("y", Int 0), While (Le (Var "x", Int 100), Seq (Assign ("y", Mult (Var "x", Int 2)), Seq (If (Neg (Le (Var "y", Int 3)), Assign ("x", Mult (Var "x", Var "y")), Skip), Seq (Assign ("z", Minus (Var "x", Int 4)), Seq (If (Neg (Le (Var "z", Int 0)), Assign ("x", Plus (Var "x", Int 1)), Skip), Assign ("z", Minus (Var "z", Int 1)))))))) );
  ( (* 14 *) Seq (Assign ("a", Int 0), Seq (Assign ("b", Int (-10)), Seq (Assign ("z", Plus (Var "a", Var "b")), Seq (Assign ("y", Mult (Var "a", Var "b")), Seq (While (Le (Var "y", Plus (Var "a", Var "b")), Seq (Assign ("a", Plus (Var "a", Int 1)), Assign ("x", Plus (Var "a", Var "b")))), Assign ("z", Mult (Var "z", Var "a")))))) );
  ( (* 15 *) Seq (Assign ("x", Int 10), Seq (Assign ("y", Int (-10)), Seq (Assign ("z", Plus (Var "x", Var "y")), If (Eq (Var "z", Int 0), Assign ("p", Mult (Var "x", Var "y")), Assign ("q", Minus (Var "x", Var "y"))))) );
  ( (* 16 *) Seq (Assign ("x", Int 10), Seq (Assign ("a", Minus (Var "x", Int (-1))), Seq (Assign ("b", Minus (Var "x", Int 2)), Seq (While (Neg (Le (Var "x", Int 0)), Assign ("x", Plus (Var "x", Int (-1)))), Assign ("y", Mult (Var "x", Int 0))))) );
  ( (* 17 *) Seq (Assign ("x", Minus (Int 1, Int 1)), Seq (If (Neg (Eq (Var "x", Int 0)), Seq (Assign ("a", Int (-10)), Seq (Assign ("b", Int 10), Assign ("c", Int 10))), Seq (Assign ("a", Int 0), Seq (Assign ("b", Int 0), Assign ("c", Int (-10))))), Seq (Assign ("i", Minus (Var "a", Var "b")), Seq (Assign ("j", Plus (Var "b", Var "c")), Assign ("k", Mult (Var "c", Var "a"))))) );
  ( (* 18 *) Seq (Seq (Assign ("v0", Int 4), Seq (Assign ("v1", Int 7), Seq (Assign ("v2", Int 4), Seq (Assign ("v3", Int (-6)), Assign ("v4", Int 0))))), Seq (Assign ("v0", Plus (Var "v4", Minus (Var "v4", Plus (Var "v4", Var "v1")))), If (Le (Int (-3), Mult (Minus (Int 4, Var "v3"), Int (-10))), Assign ("v0", Minus (Int (-6), Minus (Var "v1", Plus (Var "v4", Var "v2")))), Seq (Skip, While (Le (Var "v4", Var "v1"), Seq (Assign ("v4", Plus (Var "v4", Mult (Int 6, Int (-7)))), Assign ("v3", Plus (Int 0, Mult (Var "v0", Int (-7))))))))) );
  ( (* 19 *) Seq (Seq (Assign ("v0", Int (-10)), Seq (Assign ("v1", Int (-5)), Seq (Assign ("v2", Int (-10)), Seq (Assign ("v3", Int 0), Assign ("v4", Int 4))))), If (Le (Var "v1", Minus (Var "v1", Minus (Var "v2", Int 2))), Assign ("v4", Var "v3"), Seq (Assign ("v3", Var "v0"), If (Neg (True), Assign ("v0", Minus (Minus (Var "v1", Int 7), Int (-3))), If (Eq (Var "v4", Minus (Var "v2", Int 8)), Assign ("v2", Int 9), If (Conj (False, True), Assign ("v0", Int 1), Assign ("v2", Minus (Plus (Var "v2", Var "v2"), Int 1))))))) );
  ( (* 20 *) Seq (Seq (Assign ("v0", Int (-10)), Seq (Assign ("v1", Int (-8)), Seq (Assign ("v2", Int (-8)), Seq (Assign ("v3", Int (-1)), Assign ("v4", Int 0))))), If (Eq (Var "v2", Var "v3"), Assign ("v1", Int 6), Seq (Assign ("v1", Var "v0"), Seq (Assign ("v4", Int 4), If (Neg (True), Assign ("v4", Int (-3)), Seq (Skip, Assign ("v4", Var "v2")))))) );
  ( (* 21 *) Seq (Seq (Assign ("v0", Int (-8)), Seq (Assign ("v1", Int (-5)), Seq (Assign ("v2", Int (-7)), Seq (Assign ("v3", Int (-2)), Assign ("v4", Int 3))))), Seq (Assign ("v3", Plus (Int 4, Var "v2")), While (False, If (Eq (Int (-1), Plus (Mult (Var "v0", Var "v1"), Int 7)), Assign ("v1", Minus (Int 3, Int (-1))), Seq (Assign ("v0", Int 2), If (Conj (True, True), Assign ("v3", Plus (Var "v1", Var "v0")), Assign ("v4", Mult (Plus (Var "v2", Var "v0"), Var "v4"))))))) );
  ( (* 22 *) Seq (Seq (Assign ("v0", Int 4), Seq (Assign ("v1", Int 3), Seq (Assign ("v2", Int 9), Seq (Assign ("v3", Int 8), Assign ("v4", Int 3))))), If (Le (Var "v3", Minus (Mult (Var "v4", Var "v2"), Int (-7))), Assign ("v1", Plus (Var "v0", Var "v4")), If (Le (Plus (Int (-5), Plus (Int (-6), Var "v0")), Int 9), Assign ("v4", Plus (Int 0, Int 0)), Seq (Assign ("v3", Plus (Var "v1", Mult (Var "v1", Var "v1"))), Seq (Assign ("v3", Plus (Int 4, Plus (Var "v0", Plus (Var "v0", Var "v3")))), Seq (Assign ("v0", Var "v2"), Assign ("v1", Int (-6))))))) );
  ( (* 23 *) Seq (Seq (Assign ("v0", Int (-8)), Seq (Assign ("v1", Int 8), Seq (Assign ("v2", Int (-7)), Seq (Assign ("v3", Int (-8)), Assign ("v4", Int 4))))), If (Eq (Minus (Var "v1", Plus (Var "v3", Var "v4")), Var "v2"), Skip, Seq (Assign ("v1", Int 7), If (Eq (Var "v0", Minus (Var "v3", Plus (Var "v0", Int (-6)))), Assign ("v3", Mult (Int (-8), Var "v2")), Seq (Assign ("v0", Var "v3"), If (Le (Var "v2", Mult (Plus (Var "v2", Var "v2"), Var "v4")), Assign ("v0", Int 0), Assign ("v1", Int (-2))))))) );
  ( (* 24 *) Seq (Seq (Assign ("v0", Int (-3)), Seq (Assign ("v1", Int 6), Seq (Assign ("v2", Int 9), Seq (Assign ("v3", Int (-4)), Assign ("v4", Int (-4)))))), If (Eq (Var "v3", Var "v4"), Assign ("v0", Int (-9)), If (Le (Minus (Int 5, Plus (Var "v1", Var "v3")), Var "v1"), Assign ("v0", Var "v2"), Seq (Assign ("v0", Mult (Var "v3", Minus (Var "v3", Mult (Var "v2", Var "v1")))), If (Le (Plus (Var "v3", Minus (Var "v1", Var "v4")), Int 1), Assign ("v4", Int 0), While (Neg (True), Assign ("v2", Var "v3")))))) );
  ( (* 25 *) Seq (Seq (Assign ("v0", Int 0), Seq (Assign ("v1", Int (-3)), Seq (Assign ("v2", Int 0), Seq (Assign ("v3", Int 1), Assign ("v4", Int (-7)))))), If (Conj (False, True), Assign ("v2", Var "v2"), Seq (Assign ("v1", Minus (Minus (Var "v1", Var "v4"), Var "v2")), If (Eq (Var "v4", Plus (Var "v2", Int (-7))), Assign ("v0", Minus (Minus (Var "v1", Var "v3"), Int (-6))), Seq (Assign ("v0", Plus (Var "v1", Minus (Var "v3", Int 5))), Seq (Assign ("v3", Var "v2"), Assign ("v4", Int (-9))))))) );
]