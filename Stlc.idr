module Stlc

import Expr
import Logic
import Maps

%access public export

%default total

data Ty : Type where
  TyArrow : Ty -> Ty -> Ty
  TyBool : Ty
  TyNat : Ty

Uninhabited (TyArrow ty _ = ty) where
  uninhabited Refl impossible

data Tm : Type where
  Var : Id -> Tm
  App : Tm -> Tm -> Tm
  Abs : Id -> Ty -> Tm -> Tm
  Const : Nat -> Tm
  Scc : Tm -> Tm
  Prd : Tm -> Tm
  Mult : Tm -> Tm -> Tm
  IsZro : Tm -> Tm
  Tru : Tm
  Fls : Tm
  Test : Tm -> Tm -> Tm -> Tm

data Value : Tm -> Type where
  V_Abs : Value (Abs x ty t)
  V_Const : Value (Const n)
  V_Tru : Value Tru
  V_Fls : Value Fls

subst : (x : Id) -> (s : Tm) -> (t : Tm) -> Tm
subst x s (Var y) with (decEq x y)
  subst x s (Var y) | Yes _ = s
  subst x s (Var y) | No _ = Var y
subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)
subst x s (Abs y ty t) with (decEq x y)
  subst x s (Abs y ty t) | Yes _ = Abs y ty t
  subst x s (Abs y ty t) | No _ = Abs y ty (subst x s t)
subst x s (Const n) = Const n
subst x s (Scc t) = Scc (subst x s t)
subst x s (Prd t) = Prd (subst x s t)
subst x s (Mult t1 t2) = Mult (subst x s t1) (subst x s t2)
subst x s (IsZro t) = IsZro (subst x s t)
subst x s Tru = Tru
subst x s Fls = Fls
subst x s (Test t1 t2 t3) = Test (subst x s t1) (subst x s t2) (subst x s t3)

syntax "<" [x] ":=" [s] ">" [t] = subst x s t

data Substi : (s : Tm) -> (x : Id) -> Tm -> Tm -> Type where
  S_Var1 : Substi s x (Var x) s
  S_Var2 : Not (x = y) -> Substi s x (Var y) (Var y)
  S_App : Substi s x t1 t1' -> Substi s x t2 t2' ->
          Substi s x (App t1 t2) (App t1' t2')
  S_Abs1 : Substi s x (Abs x ty t) (Abs x ty t)
  S_Abs2 : Not (x = y) -> Substi s x t t' ->
           Substi s x (Abs y ty t) (Abs y ty t')
  S_Const : Substi s x (Const n) (Const n)
  S_Scc : Substi s x t t' -> Substi s x (Scc t) (Scc t')
  S_Prd : Substi s x t t' -> Substi s x (Prd t) (Prd t')
  S_Mult : Substi s x t1 t1' -> Substi s x t2 t2' ->
           Substi s x (Mult t1 t2) (Mult t1' t2')
  S_IsZro : Substi s x t t' -> Substi s x (IsZro t) (IsZro t')
  S_Tru : Substi s x Tru Tru
  S_Fls : Substi s x Fls Fls
  S_Test : Substi s x t1 t1' -> Substi s x t2 t2' -> Substi s x t3 t3' ->
           Substi s x (Test t1 t2 t3) (Test t1' t2' t3')

data Step : Tm -> Tm -> Type where
  ST_AppAbs : Value v -> Step (App (Abs x ty t) v) (subst x v t)
  ST_App1 : Step t1 t1' -> Step (App t1 t2) (App t1' t2)
  ST_App2 : Value v1 -> Step t2 t2' -> Step (App v1 t2) (App v1 t2')
  ST_SccConst : Value (Const n) -> Step (Scc (Const n)) (Const (S n))
  ST_Scc : Step t t' -> Step (Scc t) (Scc t')
  ST_PrdZro : Step (Prd (Const Z)) (Const Z)
  ST_PrdScc : Step (Prd (Const (S n))) (Const n)
  ST_Prd : Step t t' -> Step (Prd t) (Prd t')
  ST_MultConstConst : Step (Mult (Const n) (Const m)) (Const (n * m))
  ST_Mult1 : Step t1 t1' -> Step (Mult t1 t2) (Mult t1' t2)
  ST_Mult2 : Step t2 t2' -> Step (Mult t1 t2) (Mult t1 t2')
  ST_IsZroZro : Step (IsZro (Const Z)) Tru
  ST_IsZroScc : Step (IsZro (Const (S n))) Fls
  ST_IsZro : Step t t' -> Step (IsZro t) (IsZro t')
  ST_TestTru : Step (Test Tru t1 t2) t1
  ST_TestFls : Step (Test Fls t1 t2) t2
  ST_Test : Step t1 t1' -> Step (Test t1 t2 t3) (Test t1' t2 t3)

Uninhabited (Step Tru _) where
  uninhabited (ST_AppAbs _) impossible
  uninhabited (ST_App1 _) impossible
  uninhabited (ST_App2 _ _) impossible
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible

Uninhabited (Step Fls _) where
  uninhabited (ST_AppAbs _) impossible
  uninhabited (ST_App1 _) impossible
  uninhabited (ST_App2 _ _) impossible
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible

Uninhabited (Step (Abs _ _ _) _) where
  uninhabited (ST_AppAbs _) impossible
  uninhabited (ST_App1 _) impossible
  uninhabited (ST_App2 _ _) impossible
  uninhabited ST_TestTru impossible
  uninhabited ST_TestFls impossible
  uninhabited (ST_Test _) impossible

infix 4 -+>

(-+>) : Tm -> Tm -> Type
(-+>) = Step

MultiStep : Tm -> Tm -> Type
MultiStep = Multi Step

infix 4 -+>*

(-+>*) : Tm -> Tm -> Type
(-+>*) = MultiStep

Context : Type
Context = PartialMap Ty

data HasType : Context -> Tm -> Ty -> Type where
  T_Var : gamma x = Just ty -> HasType gamma (Var x) ty
  T_Abs : HasType (update x ty11 gamma) t12 ty12 ->
          HasType gamma (Abs x ty11 t12) (TyArrow ty11 ty12)
  T_App : HasType gamma t1 (TyArrow ty11 ty12) ->
          HasType gamma t2 ty11 ->
          HasType gamma (App t1 t2) ty12
  T_Const : HasType gamma (Const n) TyNat
  T_Scc : HasType gamma t TyNat -> HasType gamma (Scc t) TyNat
  T_Prd : HasType gamma t TyNat -> HasType gamma (Prd t) TyNat
  T_Mult : HasType gamma t1 TyNat -> HasType gamma t2 TyNat ->
           HasType gamma (Mult t1 t2) TyNat
  T_IsZro : HasType gamma t TyNat -> HasType gamma (IsZro t) TyBool
  T_Tru : HasType gamma Tru TyBool
  T_Fls : HasType gamma Fls TyBool
  T_Test : HasType gamma t1 TyBool ->
           HasType gamma t2 ty ->
           HasType gamma t3 ty ->
           HasType gamma (Test t1 t2 t3) ty
