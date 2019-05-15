module SmallStepCombined

%access public export

%default total

data Tm : Type where
  C : Nat -> Tm
  P : Tm -> Tm -> Tm
  Tru : Tm
  Fls : Tm
  If : Tm -> Tm -> Tm -> Tm

data Value : Tm -> Type where
  V_Const : (n : Nat) -> Value (C n)
  V_Tru : Value Tru
  V_Fls : Value Fls

Uninhabited (Value (P _ _)) where
  uninhabited (V_Const _) impossible
  uninhabited V_Tru impossible
  uninhabited V_Fls impossible

data Step : Tm -> Tm -> Type where
  ST_PlusConstConst : Step (P (C n1) (C n2)) (C (n1 + n2))
  ST_Plus1 : Step t1 t1' -> Step (P t1 t2) (P t1' t2)
  ST_Plus2 : Value v1 -> Step t2 t2' -> Step (P v1 t2) (P v1 t2')
  ST_IfTrue : Step (If Tru t1 t2) t1
  ST_IfFalse : Step (If Fls t1 t2) t2
  ST_If : Step t1 t1' -> Step (If t1 t2 t3) (If t1' t2 t3)

Uninhabited (Step (C n) _) where
  uninhabited ST_PlusConstConst impossible
  uninhabited (ST_Plus1 _) impossible
  uninhabited (ST_Plus2 _ _) impossible
  uninhabited ST_IfTrue impossible
  uninhabited ST_IfFalse impossible
  uninhabited (ST_If _) impossible

Uninhabited (Step Tru _) where
  uninhabited ST_PlusConstConst impossible
  uninhabited (ST_Plus1 _) impossible
  uninhabited (ST_Plus2 _ _) impossible
  uninhabited ST_IfTrue impossible
  uninhabited ST_IfFalse impossible
  uninhabited (ST_If _) impossible

Uninhabited (Step Fls _) where
  uninhabited ST_PlusConstConst impossible
  uninhabited (ST_Plus1 _) impossible
  uninhabited (ST_Plus2 _ _) impossible
  uninhabited ST_IfTrue impossible
  uninhabited ST_IfFalse impossible
  uninhabited (ST_If _) impossible

infix 4 -+>

(-+>) : Tm -> Tm -> Type
(-+>) = Step

step_deterministic : Step x y1 -> Step x y2 -> y1 = y2
step_deterministic ST_PlusConstConst ST_PlusConstConst = Refl
step_deterministic (ST_Plus1 s1) (ST_Plus2 (V_Const _) _) = absurd s1
step_deterministic (ST_Plus1 s1) (ST_Plus2 V_Tru _) = absurd s1
step_deterministic (ST_Plus1 s1) (ST_Plus2 V_Fls _) = absurd s1
step_deterministic (ST_Plus2 (V_Const _) _) (ST_Plus1 s1) = absurd s1
step_deterministic (ST_Plus2 V_Tru _) (ST_Plus1 s1) = absurd s1
step_deterministic (ST_Plus2 V_Fls _) (ST_Plus1 s1) = absurd s1
step_deterministic (ST_Plus1 s1) (ST_Plus1 s2) =
  rewrite step_deterministic s1 s2
  in Refl
step_deterministic (ST_Plus2 v1 s1) (ST_Plus2 v2 s2) =
  rewrite step_deterministic s1 s2
  in Refl
step_deterministic ST_IfTrue ST_IfTrue = Refl
step_deterministic ST_IfFalse ST_IfFalse = Refl
step_deterministic (ST_If s1) (ST_If s2) =
  rewrite step_deterministic s1 s2
  in Refl

strong_progress : (t : Tm ** (Not (Value t), Not (t' : Tm ** t -+> t')))
strong_progress = (P Tru (C 0) ** ( \v => absurd v
                                  , \(_ ** s) => case s of
                                      ST_Plus1 s1 => absurd s1
                                      ST_Plus2 _ s2 => absurd s2 ))
