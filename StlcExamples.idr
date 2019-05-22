module StlcExamples

import Expr
import Logic
import Maps
import Stlc

%access public export

%default total

idB : Tm
idB = Abs X TyBool (Var X)

idBB : Tm
idBB = Abs X (TyArrow TyBool TyBool) (Var X)

idBBBB : Tm
idBBBB = Abs X (TyArrow (TyArrow TyBool TyBool) (TyArrow TyBool TyBool)) (Var X)

k : Tm
k = Abs X TyBool (Abs Y TyBool (Var X))

notB : Tm
notB = Abs X TyBool (Test (Var X) Fls Tru)

step_example_1 : App StlcExamples.idBB StlcExamples.idB -+>* StlcExamples.idB
step_example_1 = MultiStep (ST_AppAbs V_Abs) MultiRefl

step_example_2 : App StlcExamples.idBB (App StlcExamples.idBB StlcExamples.idB)
                 -+>* StlcExamples.idB
step_example_2 = MultiStep (ST_App2 V_Abs (ST_AppAbs V_Abs))
               $ MultiStep (ST_AppAbs V_Abs)
               $ MultiRefl

step_example_3 : App (App StlcExamples.idBB StlcExamples.notB) Tru -+>* Fls
step_example_3 = MultiStep (ST_App1 (ST_AppAbs V_Abs))
               $ MultiStep (ST_AppAbs V_Tru)
               $ MultiStep ST_TestTru
               $ MultiRefl

step_example_4 : App StlcExamples.idBB (App StlcExamples.notB Tru) -+>* Fls
step_example_4 = MultiStep (ST_App2 V_Abs (ST_AppAbs V_Tru))
               $ MultiStep (ST_App2 V_Abs ST_TestTru)
               $ MultiStep (ST_AppAbs V_Fls)
               $ MultiRefl

step_example_5 : App (App StlcExamples.idBBBB StlcExamples.idBB)
                     StlcExamples.idB
                 -+>* StlcExamples.idB
step_example_5 = MultiStep (ST_App1 (ST_AppAbs V_Abs))
               $ MultiStep (ST_AppAbs V_Abs)
               $ MultiRefl

typing_example_1 : HasType Maps.empty
                           (Abs x TyBool (Var x))
                           (TyArrow TyBool TyBool)
typing_example_1 {x} = T_Abs (T_Var (rewrite sym (beq_id_refl x) in Refl))

typing_example_2 : HasType Maps.empty
                           (Abs X TyBool
                                (Abs Y (TyArrow TyBool TyBool)
                                     (App (Var Y) (App (Var Y) (Var X)))))
                           (TyArrow TyBool
                                    (TyArrow (TyArrow TyBool TyBool)
                                             TyBool))
typing_example_2 =
  T_Abs (T_Abs (T_App (T_Var Refl) (T_App (T_Var Refl) (T_Var Refl))))

typing_example_3 : (  ty : Ty
                   ** HasType Maps.empty
                              (Abs X (TyArrow TyBool TyBool)
                                   (Abs Y (TyArrow TyBool TyBool)
                                        (Abs Z TyBool
                                             (App (Var Y)
                                                  (App (Var X) (Var Z))))))
                              ty )
typing_example_3 = ( TyArrow (TyArrow TyBool TyBool)
                             (TyArrow (TyArrow TyBool TyBool)
                                      (TyArrow TyBool TyBool))
                   ** T_Abs
                        (T_Abs (T_Abs (T_App (T_Var Refl)
                                             (T_App (T_Var Refl)
                                                    (T_Var Refl))))))

typing_nonexample_3 : Not (  ty1 : Ty ** ty2 : Ty
                          ** HasType Maps.empty
                                     (Abs X ty1 (App (Var X) (Var X)))
                                     ty2 )
typing_nonexample_3 (_ ** _ ** T_Abs (T_App (T_Var prf1) (T_Var prf2))) =
  absurd (justInjective (trans (sym prf1) prf2))

num_test : Tm
num_test = Test (IsZro (Prd (Scc (Prd (Mult (Const 2) (Const 0))))))
                (Const 5)
                (Const 6)

num_test_typechecks : HasType Maps.empty StlcExamples.num_test TyNat
num_test_typechecks =
  T_Test (T_IsZro (T_Prd (T_Scc (T_Prd (T_Mult T_Const T_Const)))))
         T_Const
         T_Const

num_test_reduces : StlcExamples.num_test -+>* Const 5
num_test_reduces = MultiStep (ST_Test
                               (ST_IsZro
                                 (ST_Prd
                                   (ST_Scc
                                     (ST_Prd ST_MultConstConst)))))
                 $ MultiStep (ST_Test (ST_IsZro (ST_Prd (ST_Scc ST_PrdZro))))
                 $ MultiStep (ST_Test (ST_IsZro (ST_Prd ST_SccConst)))
                 $ MultiStep (ST_Test (ST_IsZro ST_PrdScc))
                 $ MultiStep (ST_Test ST_IsZroZro)
                 $ MultiStep ST_TestTru
                 $ MultiRefl

prod_test : Tm
prod_test = Snd (Fst (Pair (Pair (Const 5) (Const 6)) (Const 7)))

prod_test_typechecks : HasType Maps.empty StlcExamples.prod_test TyNat
prod_test_typechecks = T_Snd (T_Fst (T_Pair (T_Pair T_Const T_Const) T_Const))

prod_test_reduces : StlcExamples.prod_test -+>* Const 6
prod_test_reduces = MultiStep (ST_Snd
                                (ST_FstPair
                                  (V_Pair (V_Pair V_Const V_Const) V_Const)))
                  $ MultiStep (ST_SndPair (V_Pair V_Const V_Const))
                  $ MultiRefl

let_test : Tm
let_test = Let X (Prd (Const 6)) (Scc (Var X))

let_test_typechecks : HasType Maps.empty StlcExamples.let_test TyNat
let_test_typechecks = T_Let (T_Prd T_Const) (T_Scc (T_Var Refl))

let_test_reduces : StlcExamples.let_test -+>* Const 6
let_test_reduces = MultiStep (ST_Let ST_PrdScc)
                 $ MultiStep (ST_LetValue V_Const)
                 $ MultiStep ST_SccConst
                 $ MultiRefl

sum_test_1 : Tm
sum_test_1 = SCase (InL TyNat (Const 5))
                   X (Var X)
                   Y (Var Y)

sum_test_1_typechecks : HasType Maps.empty StlcExamples.sum_test_1 TyNat
sum_test_1_typechecks = T_SCase (T_InL T_Const) (T_Var Refl) (T_Var Refl)

sum_test_1_reduces : StlcExamples.sum_test_1  -+>* Const 5
sum_test_1_reduces = MultiStep (ST_SCaseInL V_Const)
                   $ MultiRefl

processSum : Id
processSum = MkId "processSum"

sum_test_2 : Tm
sum_test_2 = Let processSum
                 (Abs X (TySum TyNat TyNat)
                      (SCase (Var X)
                             Y (Var Y)
                             Y (Test (IsZro (Var Y)) (Const 1) (Const 0))))
                 (Pair (App (Var processSum) (InL TyNat (Const 5)))
                       (App (Var processSum) (InR TyNat (Const 5))))

sum_test_2_typechecks : HasType Maps.empty
                                StlcExamples.sum_test_2
                                (TyProd TyNat TyNat)
sum_test_2_typechecks = T_Let (T_Abs
                                (T_SCase (T_Var Refl)
                                         (T_Var Refl)
                                         (T_Test (T_IsZro (T_Var Refl))
                                                 T_Const
                                                 T_Const)))
                              (T_Pair (T_App (T_Var Refl) (T_InL T_Const))
                                      (T_App (T_Var Refl) (T_InR T_Const)))

sum_test_2_reduces : StlcExamples.sum_test_2 -+>* Pair (Const 5) (Const 0)
sum_test_2_reduces = MultiStep (ST_LetValue V_Abs)
                   $ MultiStep (ST_Pair1 (ST_AppAbs (V_InL V_Const)))
                   $ MultiStep (ST_Pair1 (ST_SCaseInL V_Const))
                   $ MultiStep (ST_Pair2 V_Const (ST_AppAbs (V_InR V_Const)))
                   $ MultiStep (ST_Pair2 V_Const (ST_SCaseInR V_Const))
                   $ MultiStep (ST_Pair2 V_Const (ST_Test ST_IsZroScc))
                   $ MultiStep (ST_Pair2 V_Const ST_TestFls)
                   $ MultiRefl

list_test : Tm
list_test = Let Z (Cons (Const 5) (Cons (Const 6) (Nil TyNat)))
                (LCase (Var Z) (Const 0) X Y (Mult (Var X) (Var X)))

list_test_typechecks : HasType Maps.empty StlcExamples.list_test TyNat
list_test_typechecks = T_Let (T_Cons T_Const (T_Cons T_Const T_Nil))
                             (T_LCase (T_Var Refl)
                                      T_Const
                                      (T_Mult (T_Var Refl) (T_Var Refl)))

list_test_reduces : StlcExamples.list_test -+>* Const 25
list_test_reduces = MultiStep (ST_LetValue (V_Cons V_Const
                                                   (V_Cons V_Const V_Nil)))
                  $ MultiStep (ST_LCaseCons V_Const (V_Cons V_Const V_Nil))
                  $ MultiStep ST_MultConstConst
                  $ MultiRefl

fact : Tm
fact = Fix (Abs W (TyArrow TyNat TyNat)
                (Abs X TyNat
                     (Test (IsZro (Var X))
                           (Const 1)
                           (Mult (Var X) (App (Var W) (Prd (Var X)))))))

fact_typechecks : HasType Maps.empty StlcExamples.fact (TyArrow TyNat TyNat)
fact_typechecks = T_Fix (T_Abs
                          (T_Abs
                            (T_Test
                              (T_IsZro (T_Var Refl))
                              T_Const
                              (T_Mult
                                (T_Var Refl)
                                (T_App (T_Var Refl) (T_Prd (T_Var Refl)))))))

fact_reduces : App StlcExamples.fact (Const 4) -+>* Const 24
fact_reduces = MultiStep (ST_App1 ST_FixAbs)
             $ MultiStep (ST_AppAbs V_Const)
             $ MultiStep (ST_Test ST_IsZroScc)
             $ MultiStep ST_TestFls
             $ MultiStep (ST_Mult2 V_Const (ST_App1 ST_FixAbs))
             $ MultiStep (ST_Mult2 V_Const (ST_App2 V_Abs ST_PrdScc))
             $ MultiStep (ST_Mult2 V_Const (ST_AppAbs V_Const))
             $ MultiStep (ST_Mult2 V_Const (ST_Test ST_IsZroScc))
             $ MultiStep (ST_Mult2 V_Const ST_TestFls)
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const (ST_App1 ST_FixAbs)))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const (ST_App2 V_Abs ST_PrdScc)))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const (ST_AppAbs V_Const)))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const (ST_Test ST_IsZroScc)))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const ST_TestFls))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const
                                             (ST_Mult2 V_Const
                                                       (ST_App1 ST_FixAbs))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2 V_Const (ST_App2 V_Abs ST_PrdScc))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2 V_Const (ST_AppAbs V_Const))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2 V_Const (ST_Test ST_IsZroScc))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2 V_Const ST_TestFls)))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2
                               V_Const
                               (ST_Mult2 V_Const (ST_App1 ST_FixAbs)))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2
                               V_Const
                               (ST_Mult2 V_Const (ST_App2 V_Abs ST_PrdScc)))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2
                               V_Const
                               (ST_Mult2 V_Const (ST_AppAbs V_Const)))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2
                               V_Const
                               (ST_Mult2 V_Const (ST_Test ST_IsZroZro)))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2
                               V_Const
                               (ST_Mult2 V_Const ST_TestTru))))
             $ MultiStep (ST_Mult2
                           V_Const
                           (ST_Mult2
                             V_Const
                             (ST_Mult2 V_Const ST_MultConstConst)))
             $ MultiStep (ST_Mult2 V_Const
                                   (ST_Mult2 V_Const ST_MultConstConst))
             $ MultiStep (ST_Mult2 V_Const ST_MultConstConst)
             $ MultiStep ST_MultConstConst
             $ MultiRefl

map : Tm
map = Abs G (TyArrow TyNat TyNat)
          (Fix (Abs F (TyArrow (TyList TyNat) (TyList TyNat))
                    (Abs X (TyList TyNat)
                         (LCase (Var X)
                                (Nil TyNat)
                                Y Z (Cons (App (Var G) (Var Y))
                                          (App (Var F) (Var Z)))))))

map_typechecks : HasType Maps.empty
                         StlcExamples.map
                         (TyArrow (TyArrow TyNat TyNat)
                                  (TyArrow (TyList TyNat) (TyList TyNat)))
map_typechecks = T_Abs
                   (T_Fix
                     (T_Abs
                       (T_Abs
                         (T_LCase (T_Var Refl)
                                  T_Nil
                                  (T_Cons (T_App (T_Var Refl) (T_Var Refl))
                                          (T_App (T_Var Refl) (T_Var Refl)))))))

map_reduces : App (App StlcExamples.map (Abs A TyNat (Scc (Var A))))
                  (Cons (Const 1) (Cons (Const 2) (Nil TyNat)))
              -+>* Cons (Const 2) (Cons (Const 3) (Nil TyNat))
map_reduces = MultiStep (ST_App1 (ST_AppAbs V_Abs))
            $ MultiStep (ST_App1 ST_FixAbs)
            $ MultiStep (ST_AppAbs (V_Cons V_Const (V_Cons V_Const V_Nil)))
            $ MultiStep (ST_LCaseCons V_Const (V_Cons V_Const V_Nil))
            $ MultiStep (ST_Cons1 (ST_AppAbs V_Const))
            $ MultiStep (ST_Cons1 ST_SccConst)
            $ MultiStep (ST_Cons2 V_Const (ST_App1 ST_FixAbs))
            $ MultiStep (ST_Cons2 V_Const (ST_AppAbs (V_Cons V_Const V_Nil)))
            $ MultiStep (ST_Cons2 V_Const (ST_LCaseCons V_Const V_Nil))
            $ MultiStep (ST_Cons2 V_Const (ST_Cons1 (ST_AppAbs V_Const)))
            $ MultiStep (ST_Cons2 V_Const (ST_Cons1 ST_SccConst))
            $ MultiStep (ST_Cons2 V_Const (ST_Cons2 V_Const
                                                    (ST_App1 ST_FixAbs)))
            $ MultiStep (ST_Cons2 V_Const (ST_Cons2 V_Const (ST_AppAbs V_Nil)))
            $ MultiStep (ST_Cons2 V_Const (ST_Cons2 V_Const ST_LCaseNil))
            $ MultiRefl

equal : Tm
equal = Fix (Abs F (TyArrow TyNat (TyArrow TyNat TyNat))
                 (Abs A TyNat
                      (Abs B TyNat
                           (Test (IsZro (Var A))
                                 (Test (IsZro (Var B)) (Const 1) (Const 0))
                                 (Test (IsZro (Var B))
                                       (Const 0)
                                       (App (App (Var F) (Prd (Var A)))
                                            (Prd (Var B))))))))

equal_typechecks : HasType Maps.empty
                           StlcExamples.equal
                           (TyArrow TyNat (TyArrow TyNat TyNat))
equal_typechecks = T_Fix
                     (T_Abs
                       (T_Abs
                         (T_Abs
                           (T_Test (T_IsZro (T_Var Refl))
                                   (T_Test (T_IsZro (T_Var Refl))
                                           T_Const
                                           T_Const)
                                   (T_Test (T_IsZro (T_Var Refl))
                                           T_Const
                                           (T_App (T_App (T_Var Refl)
                                                         (T_Prd (T_Var Refl)))
                                                  (T_Prd (T_Var Refl))))))))

equal_reduces_1 : App (App StlcExamples.equal (Const 4)) (Const 4) -+>* Const 1
equal_reduces_1 = MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroZro)
                $ MultiStep ST_TestTru
                $ MultiStep (ST_Test ST_IsZroZro)
                $ MultiStep ST_TestTru
                $ MultiRefl

equal_reduces_2 : App (App StlcExamples.equal (Const 4)) (Const 5) -+>* Const 0
equal_reduces_2 = MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiStep (ST_App1 (ST_App1 ST_FixAbs))
                $ MultiStep (ST_App1 (ST_App2 V_Abs ST_PrdScc))
                $ MultiStep (ST_App1 (ST_AppAbs V_Const))
                $ MultiStep (ST_App2 V_Abs ST_PrdScc)
                $ MultiStep (ST_AppAbs V_Const)
                $ MultiStep (ST_Test ST_IsZroZro)
                $ MultiStep ST_TestTru
                $ MultiStep (ST_Test ST_IsZroScc)
                $ MultiStep ST_TestFls
                $ MultiRefl

evenOdd : Id
evenOdd = MkId "evenOdd"

eo : Id
eo = MkId "eo"

even : Id
even = MkId "even"

odd : Id
odd = MkId "odd"

eotest : Tm
eotest = Let evenOdd
             (Fix (Abs eo (TyProd (TyArrow TyNat TyNat) (TyArrow TyNat TyNat))
                       (Pair (Abs A TyNat
                                  (Test (IsZro (Var A))
                                        (Const 1)
                                        (App (Snd (Var eo)) (Prd (Var A)))))
                             (Abs A TyNat
                                  (Test (IsZro (Var A))
                                        (Const 0)
                                        (App (Fst (Var eo)) (Prd (Var A))))))))
             (Let even (Fst (Var evenOdd))
                  (Let odd (Snd (Var evenOdd))
                       (Pair (App (Var even) (Const 3))
                             (App (Var even) (Const 4)))))
