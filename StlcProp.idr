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
