module SmallStep

import Logic

%access public export

%default total

data Tm : Type where
  C : Nat -> Tm
  P : Tm -> Tm -> Tm

Uninhabited (C _ = P _ _) where
  uninhabited Refl impossible

Uninhabited (P _ _ = C _) where
  uninhabited Refl impossible

evalF : (t : Tm) -> Nat
evalF (C n) = n
evalF (P n m) = evalF n + evalF m

data Eval : Tm -> Nat -> Type where
  E_Const : Eval (C n) n
  E_Plus : Eval t1 n1 -> Eval t2 n2 -> Eval (P t1 t2) (n1 + n2)

infixl 5 =+>

(=+>) : (t : Tm) -> (n : Nat) -> Type
(=+>) = Eval

infix 4 -+>

data Value : Tm -> Type where
  V_Const : (n : Nat) -> Value (C n)

Uninhabited (Value (P _ _)) where
  uninhabited (V_Const _) impossible

data Step : Tm -> Tm -> Type where
  ST_PlusConstConst : Step (P (C n1) (C n2)) (C (n1 + n2))
  ST_Plus1 : Step t1 t1' -> Step (P t1 t2) (P t1' t2)
  ST_Plus2 : Value v1 -> Step t2 t2' -> Step (P v1 t2) (P v1 t2')

(-+>) : Tm -> Tm -> Type
(-+>) = Step

test_step_1 : P (P (C 0) (C 3)) (P (C 2) (C 4)) -+>
              P (C (0 + 3)) (P (C 2) (C 4))
test_step_1 = ST_Plus1 ST_PlusConstConst

test_step_2 : P (C 0) (P (C 2) (P (C 0) (C 3))) -+>
              P (C 0) (P (C 2) (C (0 + 3)))
test_step_2 = ST_Plus2 (V_Const 0) (ST_Plus2 (V_Const 2) ST_PlusConstConst)

step_deterministic : Deterministic Step
step_deterministic ST_PlusConstConst ST_PlusConstConst =
  Refl
step_deterministic (ST_Plus1 s1) (ST_Plus1 s2) =
  rewrite step_deterministic s1 s2 in Refl
step_deterministic (ST_Plus2 _ s1) (ST_Plus2 _ s2) =
  rewrite step_deterministic s1 s2 in Refl

strong_progress : (t : Tm) -> Either (Value t) (t' : Tm ** t -+> t')
strong_progress (C n) = Left (V_Const n)
strong_progress (P (C n) (C m)) = Right (C (n + m) ** ST_PlusConstConst)
strong_progress (P (C n) (P t1 t2)) = case strong_progress (P t1 t2) of
  Left _ impossible
  Right (t' ** s) => Right (P (C n) t' ** ST_Plus2 (V_Const n) s)
strong_progress (P (P t1 t2) t3) = case strong_progress (P t1 t2) of
  Left _ impossible
  Right (t' ** s) => Right (P t' t3 ** ST_Plus1 s)

value_is_nf : Value v -> NormalForm Step v
value_is_nf (V_Const _) (_ ** _) impossible

nf_is_value : NormalForm Step v -> Value v
nf_is_value {v = (C k)} _ = V_Const k
nf_is_value {v = (P (C k) (C j))} contra =
  absurd (contra (C (k + j) ** ST_PlusConstConst))
nf_is_value {v = (P (C k) (P t1 t2))} contra = case strong_progress (P t1 t2) of
  Left _ impossible
  Right (x' ** s) => absurd (contra (P (C k) x' ** ST_Plus2 (V_Const k) s))
nf_is_value {v = (P (P t1 t2) t3)} contra = case strong_progress (P t1 t2) of
  Left _ impossible
  Right (x' ** s) => absurd (contra (P x' t3 ** ST_Plus1 s))

nf_same_as_value : (NormalForm Step v) ↔ (Value v)
nf_same_as_value = (nf_is_value, value_is_nf)

namespace Temp1
  data Value1 : Tm -> Type where
    V_Const1 : (n : Nat) -> Value1 (C n)
    V_Funny1 : Value1 (P t1 (C n2))

  data Step1 : Tm -> Tm -> Type where
    ST_PlusConstConst1 : Step1 (P (C n1) (C n2)) (C (n1 + n2))
    ST_Plus11 : Step1 t1 t1' -> Step1 (P t1 t2) (P t1' t2)
    ST_Plus21 : Value1 v1 -> Step1 t2 t2' -> Step1 (P v1 t2) (P v1 t2')

  value1_not_same_as_normal_form : (v : Tm ** ( Value1 v
                                              , Not (NormalForm Step1 v) ))
  value1_not_same_as_normal_form =
    (P (C 0) (C 0) ** (V_Funny1, \contra => contra (C 0 ** ST_PlusConstConst1)))

namespace Temp2
  data Value2 : Tm -> Type where
    V_Const2 : (n : Nat) -> Value2 (C n)

  data Step2 : Tm -> Tm -> Type where
    ST_Funny2 : Step2 (C n) (P (C n) (C 0))
    ST_PlusConstConst2 : Step2 (P (C n1) (C n2)) (C (n1 + n2))
    ST_Plus12 : Step2 t1 t1' -> Step2 (P t1 t2) (P t1' t2)
    ST_Plus22 : Value2 v1 -> Step2 t1 t2' -> Step2 (P v1 t2) (P v1 t2')

  value2_not_same_as_normal_form : (v : Tm ** ( Value2 v
                                              , Not (NormalForm Step2 v) ))
  value2_not_same_as_normal_form =
    (C 0 ** (V_Const2 0, \contra => contra (P (C 0) (C 0) ** ST_Funny2)))

namespace Temp3
  data Value3 : Tm -> Type where
    V_Const3 : (n : Nat) -> Value3 (C n)

  data Step3 : Tm -> Tm -> Type where
    ST_PlusConstConst3 : Step3 (P (C n1) (C n2)) (C (n1 + n2))
    ST_Plus13 : Step3 t1 t1' -> Step3 (P t1 t2) (P t1' t2)

  value3_not_same_as_normal_form : (v : Tm ** ( Not (Value3 v)
                                              , NormalForm Step3 v ))
  value3_not_same_as_normal_form =
    (P (C 0) (P (C 0) (C 0)) ** ( \v => case v of
                                    V_Const3 _ impossible
                                , \(x' ** s) => case s of
                                    ST_Plus13 ST_PlusConstConst3 impossible
                                    ST_Plus13 (ST_Plus13 _) impossible ))

namespace Temp4
  data Tm4 : Type where
    Tru4 : Tm4
    Fls4 : Tm4
    Test4 : Tm4 -> Tm4 -> Tm4 -> Tm4

  data Value4 : Tm4 -> Type where
    V_Tru4 : Value4 Tru4
    V_Fls4 : Value4 Fls4

  data Step4 : Tm4 -> Tm4 -> Type where
    ST_IfTrue4 : Step4 (Test4 Tru4 t1 t2) t1
    ST_IfFalse4 : Step4 (Test4 Fls4 t1 t2) t2
    ST_If4 : Step4 t1 t1' -> Step4 (Test4 t1 t2 t3) (Test4 t1' t2 t3)

  bool_step_prop1 : Not (Step4 Fls4 Fls4)
  bool_step_prop1 ST_IfTrue4 impossible
  bool_step_prop1 ST_IfFalse4 impossible
  bool_step_prop1 (ST_If4 _) impossible

  bool_step_prop2 : Not (Step4 (Test4 Tru4
                                      (Test4 Tru4 Tru4 Tru4)
                                      (Test4 Fls4 Fls4 Fls4))
                               Tru4)
  bool_step_prop2 ST_IfTrue4 impossible
  bool_step_prop2 ST_IfFalse4 impossible
  bool_step_prop2 (ST_If4 _) impossible

  bool_step_prop3 : Step4 (Test4 (Test4 Tru4 Tru4 Tru4)
                                 (Test4 Tru4 Tru4 Tru4)
                                 Fls4)
                          (Test4 Tru4
                                 (Test4 Tru4 Tru4 Tru4)
                                 Fls4)
  bool_step_prop3 = ST_If4 ST_IfTrue4

  strong_progress_bool : (t : Tm4) -> Either (Value4 t) (t' : Tm4 ** Step4 t t')
  strong_progress_bool Tru4 = Left V_Tru4
  strong_progress_bool Fls4 = Left V_Fls4
  strong_progress_bool (Test4 Tru4 t2 _) = Right (t2 ** ST_IfTrue4)
  strong_progress_bool (Test4 Fls4 _ t3) = Right (t3 ** ST_IfFalse4)
  strong_progress_bool (Test4 (Test4 t1 t2 t3) t4 t5) =
    case strong_progress_bool (Test4 t1 t2 t3) of
      Left _ impossible
      Right (t' ** s) => Right (Test4 t' t4 t5 ** ST_If4 s)

  step_deterministic_bool : Step4 x y1 -> Step4 x y2 -> y1 = y2
  step_deterministic_bool ST_IfTrue4 ST_IfTrue4 = Refl
  step_deterministic_bool ST_IfFalse4 ST_IfFalse4 = Refl
  step_deterministic_bool (ST_If4 s1) (ST_If4 s2) =
    rewrite step_deterministic_bool s1 s2 in Refl

infix 4 -+>*

(-+>*) : Relation Tm
(-+>*) = Multi Step

test_multistep_1 : P (P (C 0) (C 3)) (P (C 2) (C 4)) -+>* C 9
test_multistep_1 = MultiStep (ST_Plus1 ST_PlusConstConst) $
                   MultiStep (ST_Plus2 (V_Const 3) ST_PlusConstConst) $
                   MultiStep ST_PlusConstConst $
                   MultiRefl

test_multistep_2 : C 3 -+>* C 3
test_multistep_2 = MultiRefl

test_multistep_3 : P (C 0) (C 3) -+>* P (C 0) (C 3)
test_multistep_3 = MultiRefl

test_multistep_4 : P (C 0) (P (C 2) (P (C 0) (C 3))) -+>* P (C 0) (C 5)
test_multistep_4 = MultiStep (ST_Plus2 (V_Const 0)
                                       (ST_Plus2 (V_Const 2)
                                                 ST_PlusConstConst)) $
                   MultiStep (ST_Plus2 (V_Const 0) ST_PlusConstConst) $
                   MultiRefl

NormalFormOf : (t, t' : Tm) -> Type
NormalFormOf t t' = (t -+>* t', NormalForm Step t')

normal_forms_unique : Deterministic NormalFormOf
normal_forms_unique (MultiRefl, _) (MultiRefl, _) = Refl
normal_forms_unique (MultiRefl, contra) (MultiStep {y} x_step_y _, _) =
  absurd (contra (y ** x_step_y))
normal_forms_unique (MultiStep {y} x_step_y _, _) (MultiRefl, contra) =
  absurd (contra (y ** x_step_y))
normal_forms_unique {y2}
                    p@(MultiStep x_step_y y_step_y1, contra1)
                    (MultiStep x_step_y3 y3_step_y2, contra2) =
  let y3_eq_y = sym (step_deterministic x_step_y x_step_y3)
      y_step_y2 = replace {P=\x => Multi Step x y2} y3_eq_y y3_step_y2
  in normal_forms_unique (assert_smaller p (y_step_y1, contra1))
                         (y_step_y2, contra2)

Normalizing : (r : Relation t) -> Type
Normalizing {t} r = (x : t) -> (y : t ** (Multi r x y, NormalForm r y))

multistep_congr_1 : t1 -+>* t1' -> P t1 t2 -+>* P t1' t2
multistep_congr_1 MultiRefl = MultiRefl
multistep_congr_1 (MultiStep once next) =
  MultiStep (ST_Plus1 once) (multistep_congr_1 next)

multistep_congr_2 : Value t1 -> t2 -+>* t2' -> P t1 t2 -+>* P t1 t2'
multistep_congr_2 _ MultiRefl = MultiRefl
multistep_congr_2 v (MultiStep once next) =
  MultiStep (ST_Plus2 v once) (multistep_congr_2 v next)

step_normalizing : Normalizing Step
step_normalizing (C n) =
  (C n ** (MultiRefl, \(_ ** s) => case s of
                        ST_PlusConstConst impossible
                        ST_Plus1 _ impossible
                        ST_Plus2 _ _ impossible))
step_normalizing (P t1 t2) =
  let (_ ** (s1, nf1)) = step_normalizing t1
      (_ ** (s2, nf2)) = step_normalizing t2
      v1@(V_Const n1) = nf_is_value nf1
      V_Const n2 = nf_is_value nf2
      steps = multi_trans (multistep_congr_1 {t2=t2} s1) $
              multi_trans (multistep_congr_2 v1 s2) $
              MultiStep ST_PlusConstConst MultiRefl
  in (C (n1 + n2) ** (steps, \(_ ** s) => case s of
                               ST_PlusConstConst impossible
                               ST_Plus1 _ impossible
                               ST_Plus2 _ _ impossible))

eval__multistep : t =+> n -> t -+>* C n
eval__multistep E_Const = MultiRefl
eval__multistep (E_Plus {n1} e1 e2) =
  multi_trans (multistep_congr_1 (eval__multistep e1)) $
  multi_trans (multistep_congr_2 (V_Const n1) (eval__multistep e2)) $
  MultiStep ST_PlusConstConst MultiRefl

step__eval : t -+> t' -> t' =+> n -> t =+> n
step__eval ST_PlusConstConst E_Const = E_Plus E_Const E_Const
step__eval (ST_Plus1 s1) (E_Plus e1 e2) = E_Plus (step__eval s1 e1) e2
step__eval (ST_Plus2 _ s2) (E_Plus e1 e2) = E_Plus e1 (step__eval s2 e2)

multistep__eval : NormalFormOf t t' -> (n : Nat ** (t' = C n, t =+> n))
multistep__eval (MultiRefl, nf) =
  let V_Const n = nf_is_value nf
  in (n ** (Refl, E_Const))
multistep__eval p@(MultiStep {y} once next, nf) =
  let (n ** (prf, e)) = multistep__eval (assert_smaller p (next, nf))
  in (n ** (prf, step__eval once e))

evalF_eval : (evalF t = n) ↔ (t =+> n)
evalF_eval = (forward, backward)
where forward : evalF t = n -> t =+> n
      forward {t = (C _)} prf = rewrite prf in E_Const
      forward {t = (P t1 t2)} prf with (evalF t1) proof prf1
        forward {t = (P t1 t2)} prf | _ with (evalF t2) proof prf2
          forward {t = (P t1 t2)} prf | _ | _ =
            rewrite sym prf
            in E_Plus (forward (sym prf1)) (forward (sym prf2))
      backward : t =+> n -> evalF t = n
      backward E_Const = Refl
      backward (E_Plus e1 e2) =
        rewrite backward e1
        in rewrite backward e2
        in Refl
