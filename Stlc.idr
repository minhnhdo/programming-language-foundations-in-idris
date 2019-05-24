module Stlc

import Expr
import Logic
import Maps

%access public export

%default total

data Ty : Type where
  TyArrow : Ty -> Ty -> Ty
  TyBool : Ty
  TyList : Ty -> Ty
  TyNat : Ty
  TyProd : Ty -> Ty -> Ty
  TySum : Ty -> Ty -> Ty
  TyUnit : Ty

Uninhabited (TyArrow ty _ = ty) where
  uninhabited Refl impossible

data Tm : Type where
  -- pure STLC
  Var : Id -> Tm
  App : Tm -> Tm -> Tm
  Abs : Id -> Ty -> Tm -> Tm
  -- booleans
  Tru : Tm
  Fls : Tm
  Test : Tm -> Tm -> Tm -> Tm
  -- fix
  Fix : Tm -> Tm
  -- let
  Let : Id -> Tm -> Tm -> Tm
  -- lists
  Nil : Ty -> Tm
  Cons : Tm -> Tm -> Tm
  LCase : Tm -> Tm -> Id -> Id -> Tm -> Tm
  -- numbers
  Const : Nat -> Tm
  Scc : Tm -> Tm
  Prd : Tm -> Tm
  Mult : Tm -> Tm -> Tm
  IsZro : Tm -> Tm
  -- pairs
  Pair : Tm -> Tm -> Tm
  Fst : Tm -> Tm
  Snd : Tm -> Tm
  -- sums
  InL : Ty -> Tm -> Tm
  InR : Ty -> Tm -> Tm
  SCase : Tm -> Id -> Tm -> Id -> Tm -> Tm
  -- units
  Unit : Tm

data Value : Tm -> Type where
  V_Abs : Value (Abs x ty t)
  V_Const : Value (Const n)
  V_Tru : Value Tru
  V_Fls : Value Fls
  V_Nil : Value (Nil ty)
  V_Cons : Value vh -> Value vt -> Value (Cons vh vt)
  V_InL : Value t -> Value (InL ty t)
  V_InR : Value t -> Value (InR ty t)
  V_Unit : Value Unit
  V_Pair : Value t1 -> Value t2 -> Value (Pair t1 t2)

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
subst x s (Fix t) = Fix (subst x s t)
subst x s (Let y t1 t2) with (decEq x y)
  subst x s (Let y t1 t2) | Yes _ = Let y (subst x s t1) t2
  subst x s (Let y t1 t2) | No _ = Let y (subst x s t1) (subst x s t2)
subst x s (Nil ty) = Nil ty
subst x s (Cons t1 t2) = Cons (subst x s t1) (subst x s t2)
subst x s (LCase t t1 y z t2) with (decEq x y)
  subst x s (LCase t t1 y z t2) | Yes _ =
    LCase (subst x s t) (subst x s t1) y z t2
  subst x s (LCase t t1 y z t2) | No contra with (decEq x z)
    subst x s (LCase t t1 y z t2) | No _ | Yes _ =
      LCase (subst x s t) (subst x s t1) y z t2
    subst x s (LCase t t1 y z t2) | No _ | No _ =
      LCase (subst x s t) (subst x s t1) y z (subst x s t2)
subst x s (Pair t1 t2) = Pair (subst x s t1) (subst x s t2)
subst x s (Fst t) = Fst (subst x s t)
subst x s (Snd t) = Snd (subst x s t)
subst x s (InL ty t) = InL ty (subst x s t)
subst x s (InR ty t) = InR ty (subst x s t)
subst x s (SCase t y t1 z t2) with (decEq x y)
  subst x s (SCase t y t1 z t2) | Yes _ with (decEq x z)
    subst x s (SCase t y t1 z t2) | Yes _ | Yes _ =
      SCase (subst x s t) y t1 z t2
    subst x s (SCase t y t1 z t2) | Yes _ | No _ =
      SCase (subst x s t) y t1 z (subst x s t2)
  subst x s (SCase t y t1 z t2) | No _ with (decEq x z)
    subst x s (SCase t y t1 z t2) | No _ | Yes _ =
      SCase (subst x s t) y (subst x s t1) z t2
    subst x s (SCase t y t1 z t2) | No _ | No _ =
      SCase (subst x s t) y (subst x s t1) z (subst x s t2)
subst x s Unit = Unit

syntax "<" [x] ":=" [s] ">" [t] = subst x s t

data Substi : (s : Tm) -> (x : Id) -> Tm -> Tm -> Type where
  -- pure STLC
  S_Var1 : Substi s x (Var x) s
  S_Var2 : Not (x = y) -> Substi s x (Var y) (Var y)
  S_App : Substi s x t1 t1' -> Substi s x t2 t2' ->
          Substi s x (App t1 t2) (App t1' t2')
  S_Abs1 : Substi s x (Abs x ty t) (Abs x ty t)
  S_Abs2 : Not (x = y) -> Substi s x t t' ->
           Substi s x (Abs y ty t) (Abs y ty t')
  -- booleans
  S_Tru : Substi s x Tru Tru
  S_Fls : Substi s x Fls Fls
  S_Test : Substi s x t1 t1' -> Substi s x t2 t2' -> Substi s x t3 t3' ->
           Substi s x (Test t1 t2 t3) (Test t1' t2' t3')
  -- fix
  S_Fix : Substi s x t t' -> Substi s x (Fix t) (Fix t')
  -- let
  S_Let : Substi s x t1 t1' -> Substi s x (Let x t1 t2) (Let x t1' t2)
  S_LetY : Not (x = y) -> Substi s x t1 t1' -> Substi s x t2 t2' ->
           Substi s x (Let y t1 t2) (Let y t1' t2')
  -- lists
  S_Nil : Substi s x (Nil ty) (Nil ty)
  S_Cons : Substi s x t1 t1' -> Substi s x t2 t2' ->
           Substi s x (Cons t1 t2) (Cons t1' t2')
  S_LCase : Substi s x t t' -> Substi s x t1 t1' ->
            Substi s x (LCase t t1 x x t2) (LCase t' t1' x x t2)
  S_LCaseY : Not (x = y) -> Substi s x t t' -> Substi s x t1 t1' ->
             Substi s x (LCase t t1 y x t2) (LCase t' t1' y x t2)
  S_LCaseZ : Not (x = z) -> Substi s x t t' -> Substi s x t1 t1' ->
             Substi s x (LCase t t1 x z t2) (LCase t' t1' x z t2)
  S_LCaseYZ : Not (x = y) -> Not (x = z) -> Substi s x t t' ->
              Substi s x t1 t1' -> Substi s x t2 t2' ->
              Substi s x (LCase t t1 y z t2) (LCase t' t1' y z t2')
  -- numbers
  S_Const : Substi s x (Const n) (Const n)
  S_Scc : Substi s x t t' -> Substi s x (Scc t) (Scc t')
  S_Prd : Substi s x t t' -> Substi s x (Prd t) (Prd t')
  S_Mult : Substi s x t1 t1' -> Substi s x t2 t2' ->
           Substi s x (Mult t1 t2) (Mult t1' t2')
  S_IsZro : Substi s x t t' -> Substi s x (IsZro t) (IsZro t')
  -- pairs
  S_Pair : Substi s x t1 t1' -> Substi s x t2 t2' ->
           Substi s x (Pair t1 t2) (Pair t1' t2')
  S_Fst : Substi s x t t' -> Substi s x (Fst t) (Fst t')
  S_Snd : Substi s x t t' -> Substi s x (Snd t) (Snd t')
  -- sums
  S_InL : Substi s x t t' -> Substi s x (InL ty t) (InL ty t')
  S_InR : Substi s x t t' -> Substi s x (InR ty t) (InR ty t')
  S_SCase : Substi s x t t' ->
            Substi s x (SCase t x t1 x t2) (SCase t' x t1 x t2)
  S_SCaseY : Not (x = y) -> Substi s x t t' -> Substi s x t1 t1' ->
             Substi s x (SCase t y t1 x t2) (SCase t' y t1' x t2)
  S_SCaseZ : Not (x = z) -> Substi s x t t' -> Substi s x t2 t2' ->
             Substi s x (SCase t x t1 z t2) (SCase t' x t1 z t2')
  S_SCaseYZ : Not (x = y) -> Not (x = z) -> Substi s x t t' ->
              Substi s x t1 t1' -> Substi s x t2 t2' ->
              Substi s x (SCase t y t1 z t2) (SCase t' y t1' z t2')
  -- units
  S_Unit : Substi s x Unit Unit

data Step : Tm -> Tm -> Type where
  -- pure STLC
  ST_AppAbs : Value v -> Step (App (Abs x ty t) v) (subst x v t)
  ST_App1 : Step t1 t1' -> Step (App t1 t2) (App t1' t2)
  ST_App2 : Value v1 -> Step t2 t2' -> Step (App v1 t2) (App v1 t2')
  -- booleans
  ST_TestTru : Step (Test Tru t1 t2) t1
  ST_TestFls : Step (Test Fls t1 t2) t2
  ST_Test : Step t1 t1' -> Step (Test t1 t2 t3) (Test t1' t2 t3)
  -- fix
  ST_FixAbs : Step (Fix (Abs x ty t)) (subst x (Fix (Abs x ty t)) t)
  ST_Fix : Step t t' -> Step (Fix t) (Fix t')
  -- let
  ST_LetValue : Value v1 -> Step (Let x v1 t2) (subst x v1 t2)
  ST_Let : Step t1 t1' -> Step (Let x t1 t2) (Let x t1' t2)
  -- lists
  ST_Cons1 : Step t1 t1' -> Step (Cons t1 t2) (Cons t1' t2)
  ST_Cons2 : Value v1 -> Step t2 t2' -> Step (Cons v1 t2) (Cons v1 t2')
  ST_LCase : Step t t' -> Step (LCase t t1 y z t2) (LCase t' t1 y z t2)
  ST_LCaseNil : Step (LCase (Nil ty) t1 y z t2) t1
  ST_LCaseCons : Value vh -> Value vt ->
                 Step (LCase (Cons vh vt) t1 y z t2)
                      (subst z vt (subst y vh t2))
  -- numbers
  ST_SccConst : Step (Scc (Const n)) (Const (S n))
  ST_Scc : Step t t' -> Step (Scc t) (Scc t')
  ST_PrdZro : Step (Prd (Const Z)) (Const Z)
  ST_PrdScc : Step (Prd (Const (S n))) (Const n)
  ST_Prd : Step t t' -> Step (Prd t) (Prd t')
  ST_MultConstConst : Step (Mult (Const n) (Const m)) (Const (n * m))
  ST_Mult1 : Step t1 t1' -> Step (Mult t1 t2) (Mult t1' t2)
  ST_Mult2 : Value v1 -> Step t2 t2' -> Step (Mult v1 t2) (Mult v1 t2')
  ST_IsZroZro : Step (IsZro (Const Z)) Tru
  ST_IsZroScc : Step (IsZro (Const (S n))) Fls
  ST_IsZro : Step t t' -> Step (IsZro t) (IsZro t')
  -- pairs
  ST_Pair1 : Step t1 t1' -> Step (Pair t1 t2) (Pair t1' t2)
  ST_Pair2 : Value v1 -> Step t2 t2' -> Step (Pair v1 t2) (Pair v1 t2')
  ST_FstPair : Value (Pair v1 v2) -> Step (Fst (Pair v1 v2)) v1
  ST_Fst : Step t t' -> Step (Fst t) (Fst t')
  ST_SndPair : Value (Pair v1 v2) -> Step (Snd (Pair v1 v2)) v2
  ST_Snd : Step t t' -> Step (Snd t) (Snd t')
  -- sums
  ST_InL : Step t t' -> Step (InL ty t) (InL ty t')
  ST_InR : Step t t' -> Step (InR ty t) (InR ty t')
  ST_SCase : Step t t' -> Step (SCase t y t1 z t2) (SCase t' y t1 z t2)
  ST_SCaseInL : Value v -> Step (SCase (InL ty v) y t1 z t2) (subst y v t1)
  ST_SCaseInR : Value v -> Step (SCase (InR ty v) y t1 z t2) (subst z v t2)

Uninhabited (Step Tru _) where
  uninhabited ST_TestTru impossible

Uninhabited (Step Fls _) where
  uninhabited ST_TestFls impossible

Uninhabited (Step (Abs _ _ _) _) where
  uninhabited (ST_AppAbs _) impossible

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
  -- pure STLC
  T_Var : gamma x = Just ty -> HasType gamma (Var x) ty
  T_Abs : HasType (update x ty11 gamma) t12 ty12 ->
          HasType gamma (Abs x ty11 t12) (TyArrow ty11 ty12)
  T_App : HasType gamma t1 (TyArrow ty11 ty12) ->
          HasType gamma t2 ty11 ->
          HasType gamma (App t1 t2) ty12
  -- booleans
  T_Tru : HasType gamma Tru TyBool
  T_Fls : HasType gamma Fls TyBool
  T_Test : HasType gamma t1 TyBool ->
           HasType gamma t2 ty ->
           HasType gamma t3 ty ->
           HasType gamma (Test t1 t2 t3) ty
  -- fix
  T_Fix : HasType gamma t (TyArrow ty ty) -> HasType gamma (Fix t) ty
  -- let
  T_Let : HasType gamma t1 ty1 -> HasType (update x ty1 gamma) t2 ty2 ->
          HasType gamma (Let x t1 t2) ty2
  -- lists
  T_Nil : HasType gamma (Nil ty) (TyList ty)
  T_Cons : HasType gamma th ty -> HasType gamma tt (TyList ty) ->
           HasType gamma (Cons th tt) (TyList ty)
  T_LCase : HasType gamma t (TyList ty1) ->
            HasType gamma t2 ty ->
            HasType (update y ty1 (update z (TyList ty1) gamma)) t3 ty ->
            HasType gamma (LCase t t2 y z t3) ty
  -- numbers
  T_Const : HasType gamma (Const n) TyNat
  T_Scc : HasType gamma t TyNat -> HasType gamma (Scc t) TyNat
  T_Prd : HasType gamma t TyNat -> HasType gamma (Prd t) TyNat
  T_Mult : HasType gamma t1 TyNat -> HasType gamma t2 TyNat ->
           HasType gamma (Mult t1 t2) TyNat
  T_IsZro : HasType gamma t TyNat -> HasType gamma (IsZro t) TyBool
  -- pairs
  T_Pair : HasType gamma t1 ty1 -> HasType gamma t2 ty2 ->
           HasType gamma (Pair t1 t2) (TyProd ty1 ty2)
  T_Fst : HasType gamma t (TyProd ty1 ty2) -> HasType gamma (Fst t) ty1
  T_Snd : HasType gamma t (TyProd ty1 ty2) -> HasType gamma (Snd t) ty2
  -- sums
  T_InL : HasType gamma t1 ty1 -> HasType gamma (InL ty1 t1) (TySum ty1 ty2)
  T_InR : HasType gamma t2 ty2 -> HasType gamma (InR ty2 t2) (TySum ty1 ty2)
  T_SCase : HasType gamma t (TySum ty1 ty2) ->
            HasType (update x ty1 gamma) t1 ty ->
            HasType (update y ty2 gamma) t2 ty ->
            HasType gamma (SCase t x t1 y t2) ty
  -- unit
  T_Unit : HasType gamma Unit TyUnit
