module Stlc

import Expr
import Logic
import Maps

%access public export

%default total

data Ty : Type where
  TyBool : Ty
  TyArrow : Ty -> Ty -> Ty

data Tm : Type where
  Var : Id -> Tm
  App : Tm -> Tm -> Tm
  Abs : Id -> Ty -> Tm -> Tm
  Tru : Tm
  Fls : Tm
  Test : Tm -> Tm -> Tm -> Tm

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

data Value : Tm -> Type where
  V_Abs : Value (Abs x ty t)
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
  S_Tru : Substi s x Tru Tru
  S_Fls : Substi s x Fls Fls
  S_Test : Substi s x t1 t1' -> Substi s x t2 t2' -> Substi s x t3 t3' ->
           Substi s x (Test t1 t2 t3) (Test t1' t2' t3')

substi_correct : (subst x s t = t') ↔ (Substi s x t t')
substi_correct = (forward, backward)
where forward : subst x s t = t' -> Substi s x t t'
      forward {x} {t = Var y} prf with (decEq x y)
        forward {x} {t = Var y} prf | Yes prf' = rewrite sym prf
                                                 in rewrite prf'
                                                 in S_Var1
        forward {x} {t = Var y} prf | No contra = rewrite sym prf
                                                  in S_Var2 contra
      forward {x} {s} {t = App t1 t2} prf with (subst x s t1) proof t1_prf
        forward {x} {s} {t = App t1 t2} prf | t1'
          with (subst x s t2) proof t2_prf
            forward {x} {s} {t = App t1 t2} prf | t1' | t2' =
              rewrite sym prf
              in S_App (forward (sym t1_prf)) (forward (sym t2_prf))
      forward {x} {s} {t = Abs y ty t} prf with (decEq x y)
        forward {x} {s} {t = Abs y ty t} prf | Yes prf' =
          rewrite sym prf
          in rewrite prf'
          in S_Abs1
        forward {x} {s} {t = Abs y ty t} prf | No contra
          with (subst x s t) proof t_prf
            forward {x} {s} {t = Abs y ty t} prf | No contra | t' =
              rewrite sym prf
              in S_Abs2 contra (forward (sym t_prf))
      forward {t = Tru} prf = rewrite sym prf in S_Tru
      forward {t = Fls} prf = rewrite sym prf in S_Fls
      forward {x} {s} {t = Test t1 t2 t3} prf with (subst x s t1) proof t1_prf
        forward {x} {s} {t = Test t1 t2 t3} prf | t1'
          with (subst x s t2) proof t2_prf
            forward {x} {s} {t = Test t1 t2 t3} prf | t1' | t2'
              with (subst x s t3) proof t3_prf
                forward {x} {s} {t = Test t1 t2 t3} prf | t1' | t2' | t3' =
                  rewrite sym prf
                  in S_Test (forward (sym t1_prf))
                            (forward (sym t2_prf))
                            (forward (sym t3_prf))
      backward : Substi s x t t' -> subst x s t = t'
      backward {x} S_Var1 with (decEq x x)
        backward {x} S_Var1 | Yes _ = Refl
        backward {x} S_Var1 | No contra = absurd (contra Refl)
      backward {x} {t=Var y} (S_Var2 contra) with (decEq x y)
        backward {x} {t=Var y} (S_Var2 contra) | Yes prf = absurd (contra prf)
        backward {x} {t=Var y} (S_Var2 contra) | No _ = Refl
      backward (S_App s1 s2) = rewrite backward s1
                               in rewrite backward s2
                               in Refl
      backward {x} S_Abs1 with (decEq x x)
        backward {x} S_Abs1 | Yes _ = Refl
        backward {x} S_Abs1 | No contra = absurd (contra Refl)
      backward {x} {t=Abs y _ _} (S_Abs2 contra s) with (decEq x y)
        backward {x} {t=Abs y _ _} (S_Abs2 contra s) | Yes prf =
          absurd (contra prf)
        backward {x} {t=Abs y _ _} (S_Abs2 contra s) | No _ =
          rewrite backward s in Refl
      backward S_Tru = Refl
      backward S_Fls = Refl
      backward (S_Test s1 s2 s3) = rewrite backward s1
                                   in rewrite backward s2
                                   in rewrite backward s3
                                   in Refl
