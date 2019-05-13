module SmallStep

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

Relation : (p : Type) -> Type
Relation p = p -> p -> Type

Deterministic : (r : Relation p) -> Type
Deterministic {p} r = {x, y1, y2 : p} -> r x y1 -> r x y2 -> y1 = y2

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
