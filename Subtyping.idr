module Subtyping

import Expr
import Maps

%access public export

%default total

data Ty : Type where
  TyTop : Ty
  TyBool : Ty
  TyBase : Id -> Ty
  TyArrow : Ty -> Ty -> Ty
  TyUnit : Ty

namespace Types
  A : Ty
  A = TyBase A

  B : Ty
  B = TyBase B

  C : Ty
  C = TyBase C

  D : Ty
  D = TyBase D

  E : Ty
  E = TyBase E

  F : Ty
  F = TyBase F

data Tm : Type where
  Var : Id -> Tm
  App : Tm -> Tm -> Tm
  Abs : Id -> Ty -> Tm -> Tm
  Tru : Tm
  Fls : Tm
  Test : Tm -> Tm -> Tm -> Tm
  Unit : Tm

subst : (x : Id) -> (s, t : Tm) -> Tm
subst x s (Var y) with (decEq x y)
  subst x s (Var y) | Yes _ = s
  subst x s (Var y) | No _ = Var y
subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)
subst x s (Abs y ty t) with (decEq x y)
  subst x s (Abs y ty t) | Yes _ = Abs y ty t
  subst x s (Abs y ty t) | No _ = Abs y ty (subst x s t)
subst x s Tru = Tru
subst x s Fls = Fls
subst x s (Test t1 t2 t3) = Test (subst x s t1) (subst x s t2) (subst x s t3)
subst x s Unit = Unit

data Value : Tm -> Type where
  V_Abs : Value (Abs x ty t)
  V_Tru : Value Tru
  V_Fls : Value Fls
  V_Unit : Value Unit

data Step : Tm -> Tm -> Type where
  ST_AppAbs : Value t2 -> Step (App (Abs x ty t1) t2) (subst x t2 t1)
  ST_App1 : Step t1 t1' -> Step (App t1 t2) (App t1' t2)
  ST_App2 : Value t1 -> Step t2 t2' -> Step (App t1 t2) (App t1 t2')
  ST_Test : Step t1 t1' -> Step (Test t1 t2 t3) (Test t1' t2 t3)
  ST_TestTru : Step (Test Tru t2 t3) t2
  ST_TestFls : Step (Test Fls t2 t3) t3

infix 4 -+>

(-+>) : Tm -> Tm -> Type
(-+>) = Step

data Subtype : Ty -> Ty -> Type where
  S_Refl : Subtype ty ty
  S_Trans : Subtype ty1 ty2 -> Subtype ty2 ty3 -> Subtype ty1 ty3
  S_Top : Subtype ty TyTop
  S_Arrow : Subtype ty3 ty1 -> Subtype ty2 ty4 ->
            Subtype (TyArrow ty1 ty2) (TyArrow ty3 ty4)

infix 4 <:

(<:) : Ty -> Ty -> Type
(<:) = Subtype

subtyping_example_0 : TyArrow C TyBool <: TyArrow C TyTop
subtyping_example_0 = S_Arrow S_Refl S_Top
