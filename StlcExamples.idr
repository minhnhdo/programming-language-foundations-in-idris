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
