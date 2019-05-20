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
cannonical_forms_fun (T_Abs {t12} ty) (V_Abs {x}) = (x ** t12 ** Refl)

cannonical_forms_nat : HasType Maps.empty t TyNat -> Value t ->
                       (n : Nat ** t = Const n)
cannonical_forms_nat T_Const (V_Const {n}) = (n ** Refl)

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
            in Right (Const (S n) ** ST_SccConst V_Const)
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
    Right (t2' ** s2) => Right (Mult t1 t2' ** ST_Mult2 s2)
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

data AppearsFreeIn : Id -> Tm -> Type where
  AFI_Var : AppearsFreeIn x (Var x)
  AFI_App1 : AppearsFreeIn x t1 -> AppearsFreeIn x (App t1 t2)
  AFI_App2 : AppearsFreeIn x t2 -> AppearsFreeIn x (App t1 t2)
  AFI_Abs : Not (y = x) -> AppearsFreeIn x t -> AppearsFreeIn x (Abs y ty t)
  AFI_Scc : AppearsFreeIn x t -> AppearsFreeIn x (Scc t)
  AFI_Prd : AppearsFreeIn x t -> AppearsFreeIn x (Prd t)
  AFI_Mult1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Mult t1 t2)
  AFI_Mult2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Mult t1 t2)
  AFI_IsZro : AppearsFreeIn x t -> AppearsFreeIn x (IsZro t)
  AFI_Test1 : AppearsFreeIn x t1 -> AppearsFreeIn x (Test t1 t2 t3)
  AFI_Test2 : AppearsFreeIn x t2 -> AppearsFreeIn x (Test t1 t2 t3)
  AFI_Test3 : AppearsFreeIn x t3 -> AppearsFreeIn x (Test t1 t2 t3)

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
preservation (T_Scc _) (ST_SccConst _) = T_Const
preservation (T_Scc ht) (ST_Scc s) = T_Scc (preservation ht s)
preservation (T_Prd _) ST_PrdZro = T_Const
preservation (T_Prd _) ST_PrdScc = T_Const
preservation (T_Prd ht) (ST_Prd s) = T_Prd (preservation ht s)
preservation (T_Mult _ _) ST_MultConstConst = T_Const
preservation (T_Mult ht1 ht2) (ST_Mult1 s1) = T_Mult (preservation ht1 s1) ht2
preservation (T_Mult ht1 ht2) (ST_Mult2 s2) = T_Mult ht1 (preservation ht2 s2)
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
