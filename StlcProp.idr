module StlcProp

import Maps
import Stlc

%access public export

%default total

cannonical_forms_bool : HasType Maps.empty t TyBool -> Value t ->
                        Either (t = Tru) (t = Fls)
cannonical_forms_bool (T_Var _) V_Abs impossible
cannonical_forms_bool (T_Abs _) V_Abs impossible
cannonical_forms_bool (T_App _ _) V_Abs impossible
cannonical_forms_bool T_Tru V_Abs impossible
cannonical_forms_bool T_Fls V_Abs impossible
cannonical_forms_bool (T_Test _ _ _) V_Abs impossible
cannonical_forms_bool _ V_Tru = Left Refl
cannonical_forms_bool _ V_Fls = Right Refl

cannonical_forms_fun : HasType Maps.empty t (TyArrow ty1 ty2) -> Value t ->
                       (x : Id ** u : Tm ** t = Abs x ty1 u)
cannonical_forms_fun (T_Abs {t12} ty) (V_Abs {x}) = (x ** t12 ** Refl)
cannonical_forms_fun (T_Var _) V_Tru impossible
cannonical_forms_fun (T_Abs _) V_Tru impossible
cannonical_forms_fun (T_App _ _) V_Tru impossible
cannonical_forms_fun T_Tru V_Tru impossible
cannonical_forms_fun T_Fls V_Tru impossible
cannonical_forms_fun (T_Test _ _ _) V_Tru impossible
cannonical_forms_fun (T_Var _) V_Fls impossible
cannonical_forms_fun (T_Abs _) V_Fls impossible
cannonical_forms_fun (T_App _ _) V_Fls impossible
cannonical_forms_fun T_Tru V_Fls impossible
cannonical_forms_fun T_Fls V_Fls impossible
cannonical_forms_fun (T_Test _ _ _) V_Fls impossible

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
free_in_context (AFI_Test1 afi) (T_Test ht1 _ _) = free_in_context afi ht1
free_in_context (AFI_Test2 afi) (T_Test _ ht2 _) = free_in_context afi ht2
free_in_context (AFI_Test3 afi) (T_Test _ _ ht3) = free_in_context afi ht3

typeable_empty__closed : HasType Maps.empty t ty -> Closed t
typeable_empty__closed (T_Var prf) = absurd prf
typeable_empty__closed (T_Abs {ty11} ht) = \x, afi => case afi of
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
typeable_empty__closed T_Tru = \_, afi => case afi of
  AFI_Var impossible
  (AFI_App1 _) impossible
  (AFI_App2 _) impossible
  (AFI_Abs _ _) impossible
  (AFI_Test1 _) impossible
  (AFI_Test2 _) impossible
  (AFI_Test3 _) impossible
typeable_empty__closed T_Fls = \_, afi => case afi of
  AFI_Var impossible
  (AFI_App1 _) impossible
  (AFI_App2 _) impossible
  (AFI_Abs _ _) impossible
  (AFI_Test1 _) impossible
  (AFI_Test2 _) impossible
  (AFI_Test3 _) impossible
typeable_empty__closed (T_Test ht1 ht2 ht3) = \_, afi => case afi of
  AFI_Test1 afi => let (_ ** prf) = free_in_context afi ht1
                   in uninhabited prf
  AFI_Test2 afi => let (_ ** prf) = free_in_context afi ht2
                   in uninhabited prf
  AFI_Test3 afi => let (_ ** prf) = free_in_context afi ht3
                   in uninhabited prf
