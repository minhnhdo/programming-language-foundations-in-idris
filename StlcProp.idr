module StlcProp

import Expr
import Logic
import Maps
import Stlc

%access public export

%default total

cannonical_forms_bool : HasType Maps.empty t TyBool -> Value t ->
                        Either (t = Tru) (t = Fls)
cannonical_forms_bool _ V_Tru = Left Refl
cannonical_forms_bool _ V_Fls = Right Refl

cannonical_forms_fun : HasType Maps.empty t (TyArrow ty1 ty2) -> Value t ->
                       (x : Id ** u : Tm ** t = Abs x ty1 u)
cannonical_forms_fun (T_Abs {t12} _) (V_Abs {x}) = (x ** t12 ** Refl)

cannonical_forms_list : HasType Maps.empty t (TyList ty) -> Value t ->
                        Either (t = Nil ty)
                               (th : Tm ** tt : Tm ** ( Value th
                                                      , Value tt
                                                      , t = Cons th tt ))
cannonical_forms_list T_Nil V_Nil = Left Refl
cannonical_forms_list _ (V_Cons {th} {tt} vh vt) =
  Right (th ** tt ** (vh, vt, Refl))

cannonical_forms_nat : HasType Maps.empty t TyNat -> Value t ->
                       (n : Nat ** t = Const n)
cannonical_forms_nat T_Const (V_Const {n}) = (n ** Refl)

cannonical_forms_pair : HasType Maps.empty t (TyProd ty1 ty2) -> Value t ->
                        (t1 : Tm ** t2 : Tm ** ( Value t1
                                               , Value t2
                                               , t = Pair t1 t2 ))
cannonical_forms_pair _ (V_Pair {t1} {t2} v1 v2) =
  (t1 ** t2 ** (v1, v2, Refl))

cannonical_forms_sum : HasType Maps.empty t (TySum ty1 ty2) -> Value t ->
                       Either (t1 : Tm ** (Value t1, t = InL ty1 t1))
                              (t2 : Tm ** (Value t2, t = InR ty2 t2))
cannonical_forms_sum (T_InL _) (V_InL {t} v) = Left (t ** (v, Refl))
cannonical_forms_sum (T_InR _) (V_InR {t} v) = Right (t ** (v, Refl))

progress : HasType Maps.empty t ty -> Either (Value t) (t' : Tm ** (t -+> t'))
progress (T_Var prf) = absurd prf
progress (T_Abs _) = Left V_Abs
progress (T_App ht1 ht2) = case progress ht1 of
  Left v1 => case progress ht2 of
    Left v2 => let (x ** u ** prf) = cannonical_forms_fun ht1 v1
               in rewrite prf
               in Right (subst x _ u ** ST_AppAbs v2)
    Right (t2 ** s2) => Right (App _ t2 ** ST_App2 v1 s2)
  Right (t1 ** s1) => Right (App t1 _ ** ST_App1 s1)
progress T_Const = Left V_Const
progress (T_Scc ht) = case progress ht of
  Left v => let (n ** prf) = cannonical_forms_nat ht v
            in rewrite prf
            in Right (Const (S n) ** ST_SccConst)
  Right (t' ** s) => Right (Scc t' ** ST_Scc s)
progress (T_Prd ht) = case progress ht of
  Left v => let (n ** prf) = cannonical_forms_nat ht v
            in rewrite prf
            in case n of
               Z => Right (Const Z ** ST_PrdZro)
               S k => Right (Const k ** ST_PrdScc)
  Right (t' ** s) => Right (Prd t' ** ST_Prd s)
progress (T_Mult {t1} {t2} ht1 ht2) = case progress ht1 of
  Left v1 => case progress ht2 of
    Left v2 => let (n1 ** prf1) = cannonical_forms_nat ht1 v1
                   (n2 ** prf2) = cannonical_forms_nat ht2 v2
               in rewrite prf1
               in rewrite prf2
               in Right (Const (n1 * n2) ** ST_MultConstConst)
    Right (t2' ** s2) => Right (Mult t1 t2' ** ST_Mult2 v1 s2)
  Right (t1' ** s1) => Right (Mult t1' t2 ** ST_Mult1 s1)
progress (T_IsZro ht) = case progress ht of
  Left v => let (n ** prf) = cannonical_forms_nat ht v
            in rewrite prf
            in case n of
               Z => Right (Tru ** ST_IsZroZro)
               S _ => Right (Fls ** ST_IsZroScc)
  Right (t' ** s) => Right (IsZro t' ** ST_IsZro s)
progress T_Tru = Left V_Tru
progress T_Fls = Left V_Fls
progress (T_Test {t2} {t3} ht1 ht2 ht3) = case progress ht1 of
  Left v1 => case cannonical_forms_bool ht1 v1 of
    Left prf => rewrite prf
                in Right (t2 ** ST_TestTru)
    Right prf => rewrite prf
                 in Right (t3 ** ST_TestFls)
  Right (t1' ** s1) => Right (Test t1' t2 t3 ** ST_Test s1)
progress (T_Fix {ty} ht) = case progress ht of
  Left v => let (x ** t ** prf) = cannonical_forms_fun ht v
            in rewrite prf
            in Right (subst x (Fix (Abs x ty t)) t ** ST_FixAbs)
  Right (t' ** s) => Right (Fix t' ** ST_Fix s)
progress (T_Let {x} {t1} {t2} ht1 ht2) = case progress ht1 of
  Left v1 => Right (subst x t1 t2 ** ST_LetValue v1)
  Right (t1' ** s1) => Right (Let x t1' t2 ** ST_Let s1)
progress T_Nil = Left V_Nil
progress (T_Cons {th} {tt} ht1 ht2) = case progress ht1 of
  Left v1 => case progress ht2 of
    Left v2 =>  Left (V_Cons v1 v2)
    Right (tt' ** s2) =>  Right (Cons th tt' ** ST_Cons2 v1 s2)
  Right (th' ** s1) => Right (Cons th' tt ** ST_Cons1 s1)
progress (T_LCase {t} {t1} {t2} {y} {z} ht ht2 ht3) = case progress ht of
  Left v => case cannonical_forms_list ht v of
    Left prf => rewrite prf
                in Right (t1 ** ST_LCaseNil)
    Right (th ** tt ** (vh, vt, prf)) =>
      rewrite prf
      in Right (subst z tt (subst y th t2) ** ST_LCaseCons vh vt)
  Right (t' ** s) => Right (LCase t' t1 y z t2 ** ST_LCase s)
progress (T_Pair {t1} {t2} ht1 ht2) = case progress ht1 of
  Left v1 => case progress ht2 of
    Left v2 => Left (V_Pair v1 v2)
    Right (t2' ** s2) => Right (Pair t1 t2' ** ST_Pair2 v1 s2)
  Right (t1' ** s1) => Right (Pair t1' t2 ** ST_Pair1 s1)
progress (T_Fst ht) = case progress ht of
  Left v => case cannonical_forms_pair ht v of
    (t1 ** _ ** (v1, v2, prf)) => rewrite prf
                                  in Right (t1 ** ST_FstPair (V_Pair v1 v2))
  Right (t' ** s) => Right (Fst t' ** ST_Fst s)
progress (T_Snd ht) = case progress ht of
  Left v => case cannonical_forms_pair ht v of
    (_ ** t2 ** (v1, v2, prf)) => rewrite prf
                                  in Right (t2 ** ST_SndPair (V_Pair v1 v2))
  Right (t' ** s) => Right (Snd t' ** ST_Snd s)
progress (T_InL {ty1} ht) = case progress ht of
  Left v => Left (V_InL v)
  Right (t' ** s) => Right (InL ty1 t' ** ST_InL s)
progress (T_InR {ty2} ht) = case progress ht of
  Left v => Left (V_InR v)
  Right (t' ** s) => Right (InR ty2 t' ** ST_InR s)
progress (T_SCase {t} {y} {t1} {z} {t2} ht ht1 ht2) = case progress ht of
  Left v => case cannonical_forms_sum ht v of
    Left (t ** (v, prf)) => rewrite prf
                            in Right (subst y t t1 ** ST_SCaseInL v)
    Right (t ** (v, prf)) => rewrite prf
                             in Right (subst z t t2 ** ST_SCaseInR v)
  Right (t' ** s) => Right (SCase t' y t1 z t2 ** ST_SCase s)
progress T_Unit = Left V_Unit

data AppearsFreeIn : Id -> Tm -> Type where
  -- pure STLC
  AFI_Var : AppearsFreeIn x (Var x)
  AFI_App1 : AppearsFreeIn x t1 -> AppearsFreeIn x (App t1 t2)
  AFI_App2 : AppearsFreeIn x t2 -> AppearsFreeIn x (App t1 t2)
  AFI_Abs : Not (y = x) -> AppearsFreeIn x t -> AppearsFreeIn x (Abs y ty t)
  -- booleans
  AFI_Test1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Test t1 t2 t3)
  AFI_Test2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Test t1 t2 t3)
  AFI_Test3 : AppearsFreeIn x t3 -> AppearsFreeIn x (Test t1 t2 t3)
  -- fix
  AFI_Fix : AppearsFreeIn x t -> AppearsFreeIn x (Fix t)
  -- let
  AFI_Let1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Let y t1 t2)
  AFI_Let2 : Not (y = x) -> AppearsFreeIn x t2 -> AppearsFreeIn x (Let y t1 t2)
  -- lists
  AFI_Cons1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Cons t1 t2)
  AFI_Cons2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Cons t1 t2)
  AFI_LCase1 : AppearsFreeIn x t1 -> AppearsFreeIn x (LCase t1 t2 y z t3)
  AFI_LCase2 : AppearsFreeIn x t2 -> AppearsFreeIn x (LCase t1 t2 y z t3)
  AFI_LCase3 : Not (y = x) -> Not (z = x) -> AppearsFreeIn x t3 ->
               AppearsFreeIn x (LCase t1 t2 y z t3)
  -- numbers
  AFI_Scc : AppearsFreeIn x t -> AppearsFreeIn x (Scc t)
  AFI_Prd : AppearsFreeIn x t -> AppearsFreeIn x (Prd t)
  AFI_Mult1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Mult t1 t2)
  AFI_Mult2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Mult t1 t2)
  AFI_IsZro : AppearsFreeIn x t -> AppearsFreeIn x (IsZro t)
  -- pairs
  AFI_Pair1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Pair t1 t2)
  AFI_Pair2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Pair t1 t2)
  AFI_Fst : AppearsFreeIn x t -> AppearsFreeIn x (Fst t)
  AFI_Snd : AppearsFreeIn x t -> AppearsFreeIn x (Snd t)
  -- sums
  AFI_InL : AppearsFreeIn x t -> AppearsFreeIn x (InL ty t)
  AFI_InR : AppearsFreeIn x t -> AppearsFreeIn x (InR ty t)
  AFI_SCase1 : AppearsFreeIn x t1 -> AppearsFreeIn x (SCase t1 y t2 z t3)
  AFI_SCase2 : Not (y = x) -> AppearsFreeIn x t2 ->
               AppearsFreeIn x (SCase t1 y t2 z t3)
  AFI_SCase3 : Not (z = x) -> AppearsFreeIn x t3 ->
               AppearsFreeIn x (SCase t1 y t2 z t3)

Closed : (t : Tm) -> Type
Closed t = (x : Id) -> Not (AppearsFreeIn x t)

free_in_context : AppearsFreeIn x t -> HasType gamma t ty ->
                  (ty' : Ty ** gamma x = Just ty')
free_in_context {ty} AFI_Var (T_Var prf) = (ty ** prf)
free_in_context (AFI_App1 afi) (T_App ht1 _) = free_in_context afi ht1
free_in_context (AFI_App2 afi) (T_App _ ht2) = free_in_context afi ht2
free_in_context {x} {gamma} (AFI_Abs contra afi) (T_Abs {ty11} ht) =
  let (ty' ** prf) = free_in_context afi ht
  in (ty' ** replace {P=\r => (if r then Just ty11 else gamma x) = Just ty'}
                     (snd beq_id_false_iff contra)
                     prf)
free_in_context (AFI_Scc afi) (T_Scc ht) = free_in_context afi ht
free_in_context (AFI_Prd afi) (T_Prd ht) = free_in_context afi ht
free_in_context (AFI_Mult1 afi) (T_Mult ht1 _) = free_in_context afi ht1
free_in_context (AFI_Mult2 afi) (T_Mult _ ht2) = free_in_context afi ht2
free_in_context (AFI_IsZro afi) (T_IsZro ht) = free_in_context afi ht
free_in_context (AFI_Test1 afi) (T_Test ht1 _ _) = free_in_context afi ht1
free_in_context (AFI_Test2 afi) (T_Test _ ht2 _) = free_in_context afi ht2
free_in_context (AFI_Test3 afi) (T_Test _ _ ht3) = free_in_context afi ht3
free_in_context (AFI_Fix afi) (T_Fix ht) = free_in_context afi ht
free_in_context (AFI_Let1 afi) (T_Let ht1 _) = free_in_context afi ht1
free_in_context {gamma} (AFI_Let2 {y} {x} contra afi) (T_Let {ty1} _ ht2) =
  rewrite sym (update_neq {m=gamma} {v=ty1} contra)
  in free_in_context afi ht2
free_in_context (AFI_Cons1 afi) (T_Cons ht1 _) = free_in_context afi ht1
free_in_context (AFI_Cons2 afi) (T_Cons _ ht2) = free_in_context afi ht2
free_in_context (AFI_LCase1 afi) (T_LCase ht _ _) = free_in_context afi ht
free_in_context (AFI_LCase2 afi) (T_LCase _ ht1 _) = free_in_context afi ht1
free_in_context {gamma}
                (AFI_LCase3 contra1 contra2 afi)
                (T_LCase {ty1} {y} {z} _ _ ht2) =
  let prf1 = update_neq {x2=y} {m=gamma} {v=ty1} contra1
      prf2 = update_neq {x2=z} {m=gamma} {v=TyList ty1} contra2
  in rewrite sym prf1
  in rewrite sym prf2
  in free_in_context afi ht2
free_in_context (AFI_Pair1 afi) (T_Pair ht1 _) = free_in_context afi ht1
free_in_context (AFI_Pair2 afi) (T_Pair _ ht2) = free_in_context afi ht2
free_in_context (AFI_Fst afi) (T_Fst ht) = free_in_context afi ht
free_in_context (AFI_Snd afi) (T_Snd ht) = free_in_context afi ht
free_in_context (AFI_InL afi) (T_InL ht) = free_in_context afi ht
free_in_context (AFI_InR afi) (T_InR ht) = free_in_context afi ht
free_in_context (AFI_SCase1 afi) (T_SCase ht _ _) = free_in_context afi ht
free_in_context {gamma} (AFI_SCase2 contra afi) (T_SCase {ty1} _ ht1 _) =
  rewrite sym (update_neq {m=gamma} {v=ty1} contra)
  in free_in_context afi ht1
free_in_context {gamma} (AFI_SCase3 contra afi) (T_SCase {ty2} _ _ ht2) =
  rewrite sym (update_neq {m=gamma} {v=ty2} contra)
  in free_in_context afi ht2

typeable_empty__closed : HasType Maps.empty t ty -> Closed t
typeable_empty__closed (T_Var prf) = absurd prf
typeable_empty__closed (T_Abs {ty11} ht) = \_, afi => case afi of
  AFI_Abs contra afi => let (ty' ** prf) = free_in_context afi ht
                        in uninhabited (replace {P=\r => (if r
                                                             then Just ty11
                                                             else Nothing)
                                                         = Just ty'}
                                                (snd beq_id_false_iff contra)
                                                prf)
typeable_empty__closed (T_App ht1 ht2) = \_, afi => case afi of
  AFI_App1 afi => let (_ ** prf) = free_in_context afi ht1
                  in uninhabited prf
  AFI_App2 afi => let (_ ** prf) = free_in_context afi ht2
                  in uninhabited prf
typeable_empty__closed T_Const = \_, afi => case afi of
  AFI_Var impossible
typeable_empty__closed (T_Scc ht) = \_, afi => case afi of
  AFI_Scc afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_Prd ht) = \_, afi => case afi of
  AFI_Prd afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_Mult ht1 ht2) = \x, afi => case afi of
  AFI_Mult1 afi => let (_ ** prf) = free_in_context afi ht1
                   in uninhabited prf
  AFI_Mult2 afi => let (_ ** prf) = free_in_context afi ht2
                   in uninhabited prf
typeable_empty__closed (T_IsZro ht) = \_, afi => case afi of
  AFI_IsZro afi => let (_ ** prf) = free_in_context afi ht
                   in uninhabited prf
typeable_empty__closed T_Tru = \_, afi => case afi of
  AFI_Var impossible
typeable_empty__closed T_Fls = \_, afi => case afi of
  AFI_Var impossible
typeable_empty__closed (T_Test ht1 ht2 ht3) = \_, afi => case afi of
  AFI_Test1 afi => let (_ ** prf) = free_in_context afi ht1
                   in uninhabited prf
  AFI_Test2 afi => let (_ ** prf) = free_in_context afi ht2
                   in uninhabited prf
  AFI_Test3 afi => let (_ ** prf) = free_in_context afi ht3
                   in uninhabited prf
typeable_empty__closed (T_Fix ht) = \_, afi => case afi of
  AFI_Fix afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_Let {ty1} ht1 ht2) = \_, afi => case afi of
    AFI_Let1 afi => let (_ ** prf) = free_in_context afi ht1
                    in uninhabited prf
    AFI_Let2 contra afi => let (_ ** prf) = free_in_context afi ht2
                               pf = update_neq {m=empty} {v=ty1} contra
                           in uninhabited (trans (sym prf) pf)
typeable_empty__closed T_Nil = \_, afi => case afi of
  AFI_Var impossible
typeable_empty__closed (T_Cons ht1 ht2) = \_, afi => case afi of
  AFI_Cons1 afi => let (_ ** prf) = free_in_context afi ht1
                   in uninhabited prf
  AFI_Cons2 afi => let (_ ** prf) = free_in_context afi ht2
                   in uninhabited prf
typeable_empty__closed (T_LCase {z} {ty1} ht ht1 ht2) = \_, afi => case afi of
  AFI_LCase1 afi => let (_ ** prf) = free_in_context afi ht
                    in uninhabited prf
  AFI_LCase2 afi => let (_ ** prf) = free_in_context afi ht1
                    in uninhabited prf
  AFI_LCase3 contra1 contra2 afi =>
    let (_ ** prf) = free_in_context afi ht2
        pf1 = update_neq {m=update z (TyList ty1) empty} {v=ty1} contra1
        pf2 = update_neq {m=empty} {v=TyList ty1} contra2
    in uninhabited $ trans (sym prf)
                   $ trans pf1
                   $ pf2
typeable_empty__closed (T_Pair ht1 ht2) = \_, afi => case afi of
  AFI_Pair1 afi => let (_ ** prf) = free_in_context afi ht1
                   in uninhabited prf
  AFI_Pair2 afi => let (_ ** prf) = free_in_context afi ht2
                   in uninhabited prf
typeable_empty__closed (T_Fst ht) = \_, afi => case afi of
  AFI_Fst afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_Snd ht) = \_, afi => case afi of
  AFI_Snd afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_InL ht) = \_, afi => case afi of
  AFI_InL afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_InR ht) = \_, afi => case afi of
  AFI_InR afi => let (_ ** prf) = free_in_context afi ht
                 in uninhabited prf
typeable_empty__closed (T_SCase {ty1} {ty2} ht ht1 ht2) = \_, afi => case afi of
  AFI_SCase1 afi => let (_ ** prf) = free_in_context afi ht
                    in uninhabited prf
  AFI_SCase2 contra afi => let (_ ** prf) = free_in_context afi ht1
                               pf = update_neq {m=empty} {v=ty1} contra
                           in uninhabited (trans (sym prf) pf)
  AFI_SCase3 contra afi => let (_ ** prf) = free_in_context afi ht2
                               pf = update_neq {m=empty} {v=ty2} contra
                           in uninhabited (trans (sym prf) pf)
typeable_empty__closed T_Unit = \_, afi => case afi of
  AFI_Var impossible

context_invariance : HasType gamma t ty ->
                     ((x : Id) -> AppearsFreeIn x t -> gamma x = gamma' x) ->
                     HasType gamma' t ty
context_invariance (T_Var {x} prf) f = T_Var (rewrite sym (f x AFI_Var) in prf)
context_invariance {gamma} {gamma'} (T_Abs {x=y} {ty11} {t12} ht) f =
  T_Abs (context_invariance ht f')
where f' : (z : Id) -> AppearsFreeIn z t12 ->
           (update y ty11 gamma) z = (update y ty11 gamma') z
      f' z afi with (decEq y z)
        f' z afi | Yes prf = rewrite snd beq_id_true_iff prf in Refl
        f' z afi | No contra = rewrite snd beq_id_false_iff contra
                               in f z (AFI_Abs contra afi)
context_invariance {gamma} {gamma'} (T_App {t1} {t2} ht1 ht2) f =
  T_App (context_invariance ht1 f1) (context_invariance ht2 f2)
where f1 : (y : Id) -> AppearsFreeIn y t1 -> gamma y = gamma' y
      f1 y afi = f y (AFI_App1 afi)
      f2 : (y : Id) -> AppearsFreeIn y t2 -> gamma y = gamma' y
      f2 y afi = f y (AFI_App2 afi)
context_invariance T_Const _ = T_Const
context_invariance {gamma} {gamma'} (T_Scc {t} ht) f =
  T_Scc (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_Scc afi)
context_invariance {gamma} {gamma'} (T_Prd {t} ht) f =
  T_Prd (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_Prd afi)
context_invariance {gamma} {gamma'} (T_Mult {t1} {t2} ht1 ht2) f =
  T_Mult (context_invariance ht1 f1) (context_invariance ht2 f2)
where f1 : (y : Id) -> AppearsFreeIn y t1 -> gamma y = gamma' y
      f1 y afi = f y (AFI_Mult1 afi)
      f2 : (y : Id) -> AppearsFreeIn y t2 -> gamma y = gamma' y
      f2 y afi = f y (AFI_Mult2 afi)
context_invariance {gamma} {gamma'} (T_IsZro {t} ht) f =
  T_IsZro (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_IsZro afi)
context_invariance T_Tru _ = T_Tru
context_invariance T_Fls _ = T_Fls
context_invariance {gamma} {gamma'} (T_Test {t1} {t2} {t3} ht1 ht2 ht3) f =
  T_Test (context_invariance ht1 f1)
         (context_invariance ht2 f2)
         (context_invariance ht3 f3)
where f1 : (y : Id) -> AppearsFreeIn y t1 -> gamma y = gamma' y
      f1 y afi = f y (AFI_Test1 afi)
      f2 : (y : Id) -> AppearsFreeIn y t2 -> gamma y = gamma' y
      f2 y afi = f y (AFI_Test2 afi)
      f3 : (y : Id) -> AppearsFreeIn y t3 -> gamma y = gamma' y
      f3 y afi = f y (AFI_Test3 afi)
context_invariance {gamma} {gamma'} (T_Fix {t} ht) f =
  T_Fix (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_Fix afi)
context_invariance {gamma} {gamma'}
                   (T_Let {x=y} {t1} {t2} {ty1} ht1 ht2) f =
  T_Let (context_invariance ht1 f1) (context_invariance ht2 f2)
where f1 : (z : Id) -> AppearsFreeIn z t1 -> gamma z = gamma' z
      f1 z afi = f z (AFI_Let1 afi)
      f2 : (z : Id) -> AppearsFreeIn z t2 ->
           (update y ty1 gamma) z = (update y ty1 gamma') z
      f2 z afi with (decEq y z)
        f2 z afi | Yes prf = rewrite snd beq_id_true_iff prf in Refl
        f2 z afi | No contra = rewrite snd beq_id_false_iff contra
                               in f z (AFI_Let2 contra afi)
context_invariance T_Nil _ = T_Nil
context_invariance {gamma} {gamma'} (T_Cons {th=t1} {tt=t2} ht1 ht2) f =
  T_Cons (context_invariance ht1 f1) (context_invariance ht2 f2)
where f1 : (y : Id) -> AppearsFreeIn y t1 -> gamma y = gamma' y
      f1 y afi = f y (AFI_Cons1 afi)
      f2 : (y : Id) -> AppearsFreeIn y t2 -> gamma y = gamma' y
      f2 y afi = f y (AFI_Cons2 afi)
context_invariance {gamma} {gamma'}
                   (T_LCase {t} {ty1} {t1} {t2} {y} {z} ht ht1 ht2) f =
  T_LCase (context_invariance ht f')
          (context_invariance ht1 f1)
          (context_invariance ht2 f2)
where f' : (w : Id) -> AppearsFreeIn w t -> gamma w = gamma' w
      f' w afi = f w (AFI_LCase1 afi)
      f1 : (w : Id) -> AppearsFreeIn w t1 -> gamma w = gamma' w
      f1 w afi = f w (AFI_LCase2 afi)
      f2 : (w : Id) -> AppearsFreeIn w t2 ->
           (update y ty1 (update z (TyList ty1) gamma)) w
           = (update y ty1 (update z (TyList ty1) gamma')) w
      f2 w afi with (decEq y w)
        f2 w afi | Yes prf = rewrite snd beq_id_true_iff prf in Refl
        f2 w afi | No contra1 with (decEq z w)
          f2 w afi | No contra1 | Yes prf =
            rewrite snd beq_id_false_iff contra1
            in rewrite snd beq_id_true_iff prf
            in Refl
          f2 w afi | No contra1 | No contra2 =
            rewrite snd beq_id_false_iff contra1
            in rewrite snd beq_id_false_iff contra2
            in f w (AFI_LCase3 contra1 contra2 afi)
context_invariance {gamma} {gamma'} (T_Pair {t1} {t2} ht1 ht2) f =
  T_Pair (context_invariance ht1 f1) (context_invariance ht2 f2)
where f1 : (y : Id) -> AppearsFreeIn y t1 -> gamma y = gamma' y
      f1 y afi = f y (AFI_Pair1 afi)
      f2 : (y : Id) -> AppearsFreeIn y t2 -> gamma y = gamma' y
      f2 y afi = f y (AFI_Pair2 afi)
context_invariance {gamma} {gamma'} (T_Fst {t} ht) f =
  T_Fst (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_Fst afi)
context_invariance {gamma} {gamma'} (T_Snd {t} ht) f =
  T_Snd (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_Snd afi)
context_invariance {gamma} {gamma'} (T_InL {t1=t} ht) f =
  T_InL (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_InL afi)
context_invariance {gamma} {gamma'} (T_InR {t2=t} ht) f =
  T_InR (context_invariance ht f')
where f' : (y : Id) -> AppearsFreeIn y t -> gamma y = gamma' y
      f' y afi = f y (AFI_InR afi)
context_invariance {gamma} {gamma'}
                   (T_SCase {t} {y} {t1} {z} {t2} {ty1} {ty2} ht ht1 ht2) f =
  T_SCase (context_invariance ht f')
          (context_invariance ht1 f1)
          (context_invariance ht2 f2)
where f' : (w : Id) -> AppearsFreeIn w t -> gamma w = gamma' w
      f' w afi = f w (AFI_SCase1 afi)
      f1 : (w : Id) -> AppearsFreeIn w t1 ->
           (update y ty1 gamma) w = (update y ty1 gamma') w
      f1 w afi with (decEq y w)
        f1 w afi | Yes prf = rewrite snd beq_id_true_iff prf in Refl
        f1 w afi | No contra = rewrite snd beq_id_false_iff contra
                               in f w (AFI_SCase2 contra afi)
      f2 : (w : Id) -> AppearsFreeIn w t2 ->
           (update z ty2 gamma) w = (update z ty2 gamma') w
      f2 w afi with (decEq z w)
        f2 w afi | Yes prf = rewrite snd beq_id_true_iff prf in Refl
        f2 w afi | No contra = rewrite snd beq_id_false_iff contra
                               in f w (AFI_SCase3 contra afi)
context_invariance T_Unit _ = T_Unit

substitution_preserves_typing : HasType (Maps.update x ty2 gamma) t ty ->
                                HasType Maps.empty v ty2 ->
                                HasType gamma (subst x v t) ty
substitution_preserves_typing {x} {ty2} {ty} {gamma} {t = Var y} (T_Var prf) htv
  with (decEq x y)
  substitution_preserves_typing {x} {ty2} {ty} {gamma} {t = Var y}
                                (T_Var prf) htv | Yes prf' =
    let ty2_eq_ty = justInjective
                      (replace
                        {P=\r => (if r then Just ty2 else gamma y) = Just ty}
                        (snd beq_id_true_iff prf')
                        prf)
    in rewrite sym ty2_eq_ty
    in context_invariance htv (\z, afi =>
                                absurd (typeable_empty__closed htv z afi))
  substitution_preserves_typing {x} {ty2} {ty} {gamma} {t = Var y}
                                (T_Var prf) htv | No contra =
    T_Var (replace {P=\r => (if r then Just ty2 else gamma y) = Just ty}
                   (snd beq_id_false_iff contra) prf)
substitution_preserves_typing (T_App ht1 ht2) htv =
  T_App (substitution_preserves_typing ht1 htv)
        (substitution_preserves_typing ht2 htv)
substitution_preserves_typing {x} {ty2} {gamma} {t = Abs y ty t}
                              (T_Abs {ty12} ht) htv with (decEq x y)
    substitution_preserves_typing {x} {ty2} {gamma} {t = Abs y ty t}
                                  (T_Abs {ty12} ht) htv | Yes prf =
      let ht' = replace
                  {P=\r => HasType r t ty12}
                  (update_shadow {x=y} {v2=ty} {v1=ty2} {m=gamma})
                  (replace
                    {P=\r => HasType (\y1 => if beq_id y y1
                                                then Just ty
                                                else if beq_id r y1
                                                     then Just ty2
                                                     else gamma y1)
                                     t
                                     ty12}
                    prf
                    ht)
      in T_Abs ht'
    substitution_preserves_typing {x} {ty2} {gamma} {t = Abs y ty t}
                                  (T_Abs {ty12} ht) htv | No contra =
      T_Abs (substitution_preserves_typing
              (context_invariance
                ht
                (\z, afi =>
                  cong {f=\g => g z}
                       (update_permute {v1=ty} {v2=ty2} {m=gamma} contra)))
              htv)
substitution_preserves_typing T_Const _ = T_Const
substitution_preserves_typing (T_Scc ht) htv =
  T_Scc (substitution_preserves_typing ht htv)
substitution_preserves_typing (T_Prd ht) htv =
  T_Prd (substitution_preserves_typing ht htv)
substitution_preserves_typing (T_Mult ht1 ht2) htv =
  T_Mult (substitution_preserves_typing ht1 htv)
         (substitution_preserves_typing ht2 htv)
substitution_preserves_typing (T_IsZro ht) htv =
  T_IsZro (substitution_preserves_typing ht htv)
substitution_preserves_typing T_Tru _ = T_Tru
substitution_preserves_typing T_Fls _ = T_Fls
substitution_preserves_typing (T_Test ht1 ht2 ht3) htv =
  T_Test (substitution_preserves_typing ht1 htv)
         (substitution_preserves_typing ht2 htv)
         (substitution_preserves_typing ht3 htv)

preservation : HasType Maps.empty t ty -> t -+> t' -> HasType Maps.empty t' ty
preservation (T_App (T_Abs ht1) ht2) (ST_AppAbs v) =
  substitution_preserves_typing ht1 ht2
preservation (T_App ht1 ht2) (ST_App1 s1) = T_App (preservation ht1 s1) ht2
preservation (T_App ht1 ht2) (ST_App2 v1 s2) = T_App ht1 (preservation ht2 s2)
preservation (T_Scc _) ST_SccConst = T_Const
preservation (T_Scc ht) (ST_Scc s) = T_Scc (preservation ht s)
preservation (T_Prd _) ST_PrdZro = T_Const
preservation (T_Prd _) ST_PrdScc = T_Const
preservation (T_Prd ht) (ST_Prd s) = T_Prd (preservation ht s)
preservation (T_Mult _ _) ST_MultConstConst = T_Const
preservation (T_Mult ht1 ht2) (ST_Mult1 s1) = T_Mult (preservation ht1 s1) ht2
preservation (T_Mult ht1 ht2) (ST_Mult2 v1 s2) =
  T_Mult ht1 (preservation ht2 s2)
preservation (T_IsZro _) ST_IsZroZro = T_Tru
preservation (T_IsZro _) ST_IsZroScc = T_Fls
preservation (T_IsZro ht) (ST_IsZro s) = T_IsZro (preservation ht s)
preservation (T_Test _ ht2 _) ST_TestTru = ht2
preservation (T_Test _ _ ht3) ST_TestFls = ht3
preservation (T_Test ht1 ht2 ht3) (ST_Test s) =
  T_Test (preservation ht1 s) ht2 ht3

subject_expansion : (  t : Tm ** t' : Tm ** ty : Ty
                    ** ( t -+> t'
                       , HasType Maps.empty t' ty
                       , Not (HasType Maps.empty t ty) ))
subject_expansion = (  App (Abs X (TyArrow TyBool TyBool) (Var X)) Tru
                    ** subst X Tru (Var X)
                    ** TyBool
                    ** ( ST_AppAbs V_Tru
                       , T_Tru
                       , \ht => case ht of
                           T_App (T_Abs (T_Var prf)) _ =>
                             uninhabited (justInjective prf) ))

Stuck : (t : Tm) -> Type
Stuck t = (NormalForm Step t, Not (Value t))

soundness : HasType Maps.empty t ty -> t -+>* t' -> Not (Stuck t')
soundness ht MultiRefl (nf, not_value) = case progress ht of
  Left v => not_value v
  Right p => nf p
soundness ht (MultiStep once next) (nf, not_value) =
  soundness (preservation ht once) next (nf, not_value)

unique_types : HasType gamma e ty -> HasType gamma e ty' -> ty = ty'
unique_types (T_Var prf1) (T_Var prf2) = justInjective (trans (sym prf1) prf2)
unique_types (T_Abs ht1) (T_Abs ht2) = rewrite unique_types ht1 ht2 in Refl
unique_types {ty} {ty'} (T_App ht1 ht2) (T_App {ty11=ty2} ht3 ht4) =
  let prf = replace {P=\r => TyArrow r ty = TyArrow ty2 ty'}
                    (unique_types ht2 ht4)
                    (unique_types ht1 ht3)
  in case prf of
    Refl => Refl
unique_types T_Const T_Const = Refl
unique_types (T_Scc _) (T_Scc _) = Refl
unique_types (T_Prd _) (T_Prd _) = Refl
unique_types (T_Mult _ _) (T_Mult _ _) = Refl
unique_types (T_IsZro _) (T_IsZro _) = Refl
unique_types T_Tru T_Tru = Refl
unique_types T_Fls T_Fls = Refl
unique_types (T_Test _ ht1 _) (T_Test _ ht2 _) = unique_types ht1 ht2
