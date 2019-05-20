module StlcSubstProof

import Logic
import Maps
import Stlc

%access public export

%default total

substi_sound : (x : Id) -> (s : Tm) -> (t : Tm) ->
               subst x s t = t' -> Substi s x t t'
substi_sound x s (Var y) prf with (decEq x y)
  substi_sound x s (Var y) prf | Yes prf' = rewrite sym prf
                                            in rewrite prf'
                                            in S_Var1
  substi_sound x s (Var y) prf | No contra = rewrite sym prf
                                             in S_Var2 contra
substi_sound x s (App t1 t2) prf with (subst x s t1) proof t1_prf
  substi_sound x s (App t1 t2) prf | t1' with (subst x s t2) proof t2_prf
    substi_sound x s (App t1 t2) prf | t1' | t2' =
      rewrite sym prf
      in S_App (substi_sound x s t1 (sym t1_prf))
               (substi_sound x s t2 (sym t2_prf))
substi_sound x s (Abs y ty t) prf with (decEq x y)
  substi_sound x s (Abs y ty t) prf | Yes prf' =
    rewrite sym prf
    in rewrite prf'
    in S_Abs1
  substi_sound x s (Abs y ty t) prf | No contra with (subst x s t) proof t_prf
    substi_sound x s (Abs y ty t) prf | No contra | t' =
      rewrite sym prf in S_Abs2 contra (substi_sound x s t (sym t_prf))
substi_sound x s (Const n) prf = rewrite sym prf in S_Const
substi_sound x s (Scc t) prf with (subst x s t) proof t_prf
  substi_sound x s (Scc t) prf | t' = rewrite sym prf
                                      in S_Scc (substi_sound x s t (sym t_prf))
substi_sound x s (Prd t) prf with (subst x s t) proof t_prf
  substi_sound x s (Prd t) prf | t' = rewrite sym prf
                                      in S_Prd (substi_sound x s t (sym t_prf))
substi_sound x s (Mult t1 t2) prf with (subst x s t1) proof t1_prf
  substi_sound x s (Mult t1 t2) prf | t1' with (subst x s t2) proof t2_prf
    substi_sound x s (Mult t1 t2) prf | t1' | t2' =
      rewrite sym prf
      in S_Mult (substi_sound x s t1 (sym t1_prf))
                (substi_sound x s t2 (sym t2_prf))
substi_sound x s (IsZro t) prf with (subst x s t) proof t_prf
  substi_sound x s (IsZro t) prf | t' =
    rewrite sym prf in S_IsZro (substi_sound x s t (sym t_prf))
substi_sound x s Tru prf = rewrite sym prf in S_Tru
substi_sound x s Fls prf = rewrite sym prf in S_Fls
substi_sound x s (Test t1 t2 t3) prf with (subst x s t1) proof t1_prf
  substi_sound x s (Test t1 t2 t3) prf | t1' with (subst x s t2) proof t2_prf
    substi_sound x s (Test t1 t2 t3) prf | t1' | t2'
      with (subst x s t3) proof t3_prf
        substi_sound x s (Test t1 t2 t3) prf | t1' | t2' | t3' =
          rewrite sym prf
          in S_Test (substi_sound x s t1 (sym t1_prf))
                    (substi_sound x s t2 (sym t2_prf))
                    (substi_sound x s t3 (sym t3_prf))

substi_complete : Substi s x t t' -> subst x s t = t'
substi_complete {x} S_Var1 with (decEq x x)
  substi_complete {x} S_Var1 | Yes _ = Refl
  substi_complete {x} S_Var1 | No contra = absurd (contra Refl)
substi_complete {x} {t=Var y} (S_Var2 contra) with (decEq x y)
  substi_complete {x} {t=Var y} (S_Var2 contra) | Yes prf = absurd (contra prf)
  substi_complete {x} {t=Var y} (S_Var2 contra) | No _ = Refl
substi_complete (S_App s1 s2) = rewrite substi_complete s1
                         in rewrite substi_complete s2
                         in Refl
substi_complete {x} S_Abs1 with (decEq x x)
  substi_complete {x} S_Abs1 | Yes _ = Refl
  substi_complete {x} S_Abs1 | No contra = absurd (contra Refl)
substi_complete {x} {t=Abs y _ _} (S_Abs2 contra s) with (decEq x y)
  substi_complete {x} {t=Abs y _ _} (S_Abs2 contra s) | Yes prf =
    absurd (contra prf)
  substi_complete {x} {t=Abs y _ _} (S_Abs2 contra s) | No _ =
    rewrite substi_complete s in Refl
substi_complete S_Const = Refl
substi_complete (S_Scc s) = rewrite substi_complete s in Refl
substi_complete (S_Prd s) = rewrite substi_complete s in Refl
substi_complete (S_Mult s1 s2) = rewrite substi_complete s1
                          in rewrite substi_complete s2
                          in Refl
substi_complete (S_IsZro s) = rewrite substi_complete s in Refl
substi_complete S_Tru = Refl
substi_complete S_Fls = Refl
substi_complete (S_Test s1 s2 s3) = rewrite substi_complete s1
                             in rewrite substi_complete s2
                             in rewrite substi_complete s3
                             in Refl


substi_correct : (subst x s t = t') ↔ (Substi s x t t')
substi_correct {x} {s} {t} = (substi_sound x s t, substi_complete)
