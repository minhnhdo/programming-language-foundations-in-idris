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
substi_sound x s (Fix t) prf with (subst x s t) proof t_prf
  substi_sound x s (Fix t) prf | t' = rewrite sym prf
                                      in S_Fix (substi_sound x s t (sym t_prf))
substi_sound x s (Let y t1 t2) prf with (subst x s t1) proof t1_prf
  substi_sound x s (Let y t1 t2) prf | t1' with (decEq x y)
    substi_sound x s (Let y t1 t2) prf | t1' | Yes eq_prf =
      rewrite sym prf
      in rewrite sym eq_prf
      in S_Let (substi_sound x s t1 Refl)
    substi_sound x s (Let y t1 t2) prf | t1' | No contra
      with (subst x s t2) proof t2_prf
        substi_sound x s (Let y t1 t2) prf | t1' | No contra | t2' =
          rewrite sym prf
          in S_LetY contra
                    (substi_sound x s t1 Refl)
                    (substi_sound x s t2 (sym t2_prf))
substi_sound x s (Nil ty) prf = rewrite sym prf in S_Nil
substi_sound x s (Cons t1 t2) prf with (subst x s t1) proof t1_prf
  substi_sound x s (Cons t1 t2) prf | t1' with (subst x s t2) proof t2_prf
    substi_sound x s (Cons t1 t2) prf | t1' | t2' =
      rewrite sym prf
      in S_Cons (substi_sound x s t1 (sym t1_prf))
                (substi_sound x s t2 (sym t2_prf))
substi_sound x s (LCase t t1 y z t2) prf with (subst x s t) proof t_prf
  substi_sound x s (LCase t t1 y z t2) prf | t' with (subst x s t1) proof t1_prf
    substi_sound x s (LCase t t1 y z t2) prf | t' | t1' with (decEq x y)
      substi_sound x s (LCase t t1 y z t2) prf | t' | t1' | Yes xy_prf
        with (decEq x z)
          substi_sound x s (LCase t t1 y z t2) prf
            | t' | t1' | Yes xy_prf | Yes xz_prf =
              rewrite sym prf
              in rewrite sym xy_prf
              in rewrite sym xz_prf
              in S_LCase (substi_sound x s t Refl) (substi_sound x s t1 Refl)
          substi_sound x s (LCase t t1 y z t2) prf
            | t' | t1' | Yes xy_prf | No xz_contra =
              rewrite sym prf
              in rewrite sym xy_prf
              in S_LCaseZ xz_contra
                          (substi_sound x s t Refl)
                          (substi_sound x s t1 Refl)
      substi_sound x s (LCase t t1 y z t2) prf | t' | t1' | No xy_contra
        with (decEq x z)
          substi_sound x s (LCase t t1 y z t2) prf
            | t' | t1' | No xy_contra | Yes xz_prf =
              rewrite sym prf
              in rewrite sym xz_prf
              in S_LCaseY xy_contra
                          (substi_sound x s t Refl)
                          (substi_sound x s t1 Refl)
          substi_sound x s (LCase t t1 y z t2) prf
            | t' | t1' | No xy_contra | No xz_contra
              with (subst x s t2) proof t2_prf
                substi_sound x s (LCase t t1 y z t2) prf
                  | t' | t1' | No xy_contra | No xz_contra | t2' =
                    rewrite sym prf
                    in S_LCaseYZ xy_contra
                                 xz_contra
                                 (substi_sound x s t Refl)
                                 (substi_sound x s t1 Refl)
                                 (substi_sound x s t2 (sym t2_prf))
substi_sound x s (Pair t1 t2) prf with (subst x s t1) proof t1_prf
  substi_sound x s (Pair t1 t2) prf | t1' with (subst x s t2) proof t2_prf
    substi_sound x s (Pair t1 t2) prf | t1' | t2' =
      rewrite sym prf
      in S_Pair (substi_sound x s t1 (sym t1_prf))
                (substi_sound x s t2 (sym t2_prf))
substi_sound x s (Fst t) prf with (subst x s t) proof t_prf
  substi_sound x s (Fst t) prf | t' = rewrite sym prf
                                      in S_Fst (substi_sound x s t (sym t_prf))
substi_sound x s (Snd t) prf with (subst x s t) proof t_prf
  substi_sound x s (Snd t) prf | t' = rewrite sym prf
                                      in S_Snd (substi_sound x s t (sym t_prf))
substi_sound x s (InL ty t) prf with (subst x s t) proof t_prf
  substi_sound x s (InL ty t) prf | t' =
    rewrite sym prf
    in S_InL (substi_sound x s t (sym t_prf))
substi_sound x s (InR ty t) prf with (subst x s t) proof t_prf
  substi_sound x s (InR ty t) prf | t' =
    rewrite sym prf
    in S_InR (substi_sound x s t (sym t_prf))
substi_sound x s (SCase t y t1 z t2) prf with (subst x s t) proof t_prf
  substi_sound x s (SCase t y t1 z t2) prf | t' with (decEq x y)
    substi_sound x s (SCase t y t1 z t2) prf | t' | Yes xy_prf with (decEq x z)
      substi_sound x s (SCase t y t1 z t2) prf
        | t' | Yes xy_prf | Yes xz_prf =
          rewrite sym prf
          in rewrite sym xy_prf
          in rewrite sym xz_prf
          in S_SCase (substi_sound x s t Refl)
      substi_sound x s (SCase t y t1 z t2) prf
        | t' | Yes xy_prf | No xz_contra with (subst x s t2) proof t2_prf
          substi_sound x s (SCase t y t1 z t2) prf
            | t' | Yes xy_prf | No xz_contra | t2' =
              rewrite sym prf
              in rewrite sym xy_prf
              in S_SCaseZ xz_contra
                          (substi_sound x s t Refl)
                          (substi_sound x s t2 (sym t2_prf))
    substi_sound x s (SCase t y t1 z t2) prf | t' | No xy_contra
      with (decEq x z)
        substi_sound x s (SCase t y t1 z t2) prf
          | t' | No xy_contra | Yes xz_prf with (subst x s t1) proof t1_prf
            substi_sound x s (SCase t y t1 z t2) prf
              | t' | No xy_contra | Yes xz_prf | t1' =
                rewrite sym prf
                in rewrite sym xz_prf
                in S_SCaseY xy_contra
                            (substi_sound x s t Refl)
                            (substi_sound x s t1 (sym t1_prf))
        substi_sound x s (SCase t y t1 z t2) prf
          | t' | No xy_contra | No xz_contra with (subst x s t1) proof t1_prf
            substi_sound x s (SCase t y t1 z t2) prf
              | t' | No xy_contra | No xz_contra | t1'
                with (subst x s t2) proof t2_prf
                  substi_sound x s (SCase t y t1 z t2) prf
                    | t' | No xy_contra | No xz_contra | t1' | t2' =
                      rewrite sym prf
                      in S_SCaseYZ xy_contra
                                   xz_contra
                                   (substi_sound x s t Refl)
                                   (substi_sound x s t1 (sym t1_prf))
                                   (substi_sound x s t2 (sym t2_prf))
substi_sound x s Unit prf = rewrite sym prf in S_Unit

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
substi_complete (S_Fix s) = rewrite substi_complete s in Refl
substi_complete (S_Let {x} s) with (decEq x x)
  substi_complete (S_Let {x} s) | Yes _ = rewrite substi_complete s in Refl
  substi_complete (S_Let {x} s) | No contra = absurd (contra Refl)
substi_complete (S_LetY {x} {y} contra s1 s2) with (decEq x y)
  substi_complete (S_LetY {x} {y} contra s1 s2) | Yes prf = absurd (contra prf)
  substi_complete (S_LetY {x} {y} contra s1 s2) | No _ =
    rewrite substi_complete s1
    in rewrite substi_complete s2
    in Refl
substi_complete S_Nil = Refl
substi_complete (S_Cons s1 s2) = rewrite substi_complete s1
                                 in rewrite substi_complete s2
                                 in Refl
substi_complete (S_LCase {x} s s1) with (decEq x x)
  substi_complete (S_LCase {x} s s1) | Yes _ = rewrite substi_complete s
                                               in rewrite substi_complete s1
                                               in Refl
  substi_complete (S_LCase {x} s s1) | No contra = absurd (contra Refl)
substi_complete (S_LCaseY {x} {y} contra s s1) with (decEq x y)
  substi_complete (S_LCaseY {x} {y} contra s s1) | Yes prf = absurd (contra prf)
  substi_complete (S_LCaseY {x} {y} contra s s1) | No _ with (decEq x x)
    substi_complete (S_LCaseY {x} {y} contra s s1) | No _ | Yes _ =
      rewrite substi_complete s
      in rewrite substi_complete s1
      in Refl
    substi_complete (S_LCaseY {x} {y} contra s s1) | No _ | No x_contra =
      absurd (x_contra Refl)
substi_complete (S_LCaseZ {x} {z} contra s s2) with (decEq x x)
  substi_complete (S_LCaseZ {x} {z} contra s s2) | Yes _ =
    rewrite substi_complete s
    in rewrite substi_complete s2
    in Refl
  substi_complete (S_LCaseZ {x} {z} contra s s2) | No x_contra =
    absurd (x_contra Refl)
substi_complete (S_LCaseYZ {x} {y} {z} contra1 contra2 s s1 s2) with (decEq x y)
  substi_complete (S_LCaseYZ {x} {y} {z} contra1 contra2 s s1 s2) | Yes prf =
    absurd (contra1 prf)
  substi_complete (S_LCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
    | No _ with (decEq x z)
      substi_complete (S_LCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
        | No _ | Yes prf =
          absurd (contra2 prf)
      substi_complete (S_LCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
        | No _ | No _ =
          rewrite substi_complete s
          in rewrite substi_complete s1
          in rewrite substi_complete s2
          in Refl
substi_complete (S_Pair s1 s2) = rewrite substi_complete s1
                                 in rewrite substi_complete s2
                                 in Refl
substi_complete (S_Fst s) = rewrite substi_complete s in Refl
substi_complete (S_Snd s) = rewrite substi_complete s in Refl
substi_complete (S_InL s) = rewrite substi_complete s in Refl
substi_complete (S_InR s) = rewrite substi_complete s in Refl
substi_complete (S_SCase {x} s) with (decEq x x) proof x_prf
  substi_complete (S_SCase {x} s) | Yes _ = rewrite sym x_prf
                                            in rewrite substi_complete s
                                            in Refl
  substi_complete (S_SCase {x} s) | No contra = absurd (contra Refl)
substi_complete (S_SCaseY {x} {y} contra s s1) with (decEq x y)
  substi_complete (S_SCaseY {x} {y} contra s s1) | Yes prf = absurd (contra prf)
  substi_complete (S_SCaseY {x} {y} contra s s1) | No _ with (decEq x x)
    substi_complete (S_SCaseY {x} {y} contra s s1) | No _ | Yes _ =
      rewrite substi_complete s
      in rewrite substi_complete s1
      in Refl
    substi_complete (S_SCaseY {x} {y} contra s s1) | No _ | No x_contra =
      absurd (x_contra Refl)
substi_complete (S_SCaseZ {x} {z} contra s s2) with (decEq x z) proof xz_prf
  substi_complete (S_SCaseZ {x} {z} contra s s2) | Yes prf = absurd (contra prf)
  substi_complete (S_SCaseZ {x} {z} contra s s2) | No _ with (decEq x x)
    substi_complete (S_SCaseZ {x} {z} contra s s2) | No _ | Yes _ =
      rewrite sym xz_prf
      in rewrite substi_complete s
      in rewrite substi_complete s2
      in Refl
    substi_complete (S_SCaseZ {x} {z} contra s s2) | No _ | No x_contra =
      absurd (x_contra Refl)
substi_complete (S_SCaseYZ {x} {y} {z} contra1 contra2 s s1 s2) with (decEq x y)
  substi_complete (S_SCaseYZ {x} {y} {z} contra1 contra2 s s1 s2) | Yes prf =
    absurd (contra1 prf)
  substi_complete (S_SCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
    | No _ with (decEq x z)
      substi_complete (S_SCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
        | No _ | Yes prf =
          absurd (contra2 prf)
      substi_complete (S_SCaseYZ {x} {y} {z} contra1 contra2 s s1 s2)
        | No _ | No _ =
          rewrite substi_complete s
          in rewrite substi_complete s1
          in rewrite substi_complete s2
          in Refl
substi_complete S_Unit = Refl

substi_correct : (subst x s t = t') ↔ (Substi s x t t')
substi_correct {x} {s} {t} = (substi_sound x s t, substi_complete)
