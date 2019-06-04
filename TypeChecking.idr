module TypeChecking

import Logic
import Maps
import Stlc

%access public export

%default total

beq_ty : Ty -> Ty -> Bool
beq_ty TyBool TyBool = True
beq_ty TyBool (TyArrow _ _) = False
beq_ty (TyArrow _ _) TyBool = False
beq_ty (TyArrow t11 t12) (TyArrow t21 t22) = beq_ty t11 t21 && beq_ty t12 t22

beq_ty_refl : TypeChecking.beq_ty ty ty = True
beq_ty_refl {ty = TyBool} = Refl
beq_ty_refl {ty = (TyArrow ty1 ty2)} = rewrite beq_ty_refl {ty=ty1}
                                       in rewrite beq_ty_refl {ty=ty2}
                                       in Refl

beq_ty__eq : TypeChecking.beq_ty ty1 ty2 = True -> ty1 = ty2
beq_ty__eq {ty1 = TyBool} {ty2 = TyBool} _ = Refl
beq_ty__eq {ty1 = TyBool} {ty2 = TyArrow ty21 ty22} prf = absurd prf
beq_ty__eq {ty1 = TyArrow ty11 ty12} {ty2 = TyBool} prf = absurd prf
beq_ty__eq {ty1 = TyArrow ty11 ty12} {ty2 = TyArrow ty21 ty22} prf =
  let (prf1, prf2) = band prf
  in rewrite beq_ty__eq {ty1=ty11} {ty2=ty21} prf1
  in rewrite beq_ty__eq {ty1=ty12} {ty2=ty22} prf2
  in Refl

type_check : (gamma : Context) -> (t : Tm) -> Maybe Ty
type_check gamma (Var x) = gamma x
type_check gamma (Abs x ty t) = do
  ty' <- type_check (update x ty gamma) t
  pure (TyArrow ty ty')
type_check gamma (App t1 t2) = do
  ty1 <- type_check gamma t1
  ty2 <- type_check gamma t2
  case ty1 of
    TyArrow ty11 ty12 => case beq_ty ty11 ty2 of
      False => Nothing
      True => pure ty12
    _ => Nothing
type_check _ Tru = Just TyBool
type_check _ Fls = Just TyBool
type_check gamma (Test cond tt tf) = do
  ty_cond <- type_check gamma cond
  ty_t <- type_check gamma tt
  ty_f <- type_check gamma tf
  case ty_cond of
    TyBool => case beq_ty ty_t ty_f of
      False => Nothing
      True => pure ty_t
    _ => Nothing

type_checking_sound : TypeChecking.type_check gamma t = Just ty ->
                      HasType gamma t ty
type_checking_sound {t = Var _} prf = T_Var prf
type_checking_sound {gamma} {t = App t1 t2} prf
  with (type_check gamma t1) proof t1_prf
    type_checking_sound {gamma} {t = App t1 t2} prf | Nothing = absurd prf
    type_checking_sound {gamma} {t = App t1 t2} prf
    | Just ty1 with (type_check gamma t2) proof t2_prf
      type_checking_sound {gamma} {t = App t1 t2} prf | Just ty1 | Nothing =
        absurd prf
      type_checking_sound {gamma} {t = App t1 t2} prf
      | Just ty1 | Just ty2 with (ty1)
        type_checking_sound {gamma} {t = App t1 t2} prf
        | Just ty1 | Just ty2 | TyArrow ty11 ty12 with (beq_ty ty11 ty2) proof ty_prf
          type_checking_sound {gamma} {t = App t1 t2} prf
          | Just ty1 | Just ty2 | TyArrow ty11 ty12 | False = absurd prf
          type_checking_sound {gamma} {t = App t1 t2} prf
          | Just ty1 | Just ty2 | TyArrow ty11 ty12 | True =
            T_App (rewrite sym (justInjective prf)
                   in type_checking_sound (sym t1_prf))
                  (rewrite beq_ty__eq {ty1=ty11} {ty2=ty2} (sym ty_prf)
                   in type_checking_sound (sym t2_prf))
        type_checking_sound {gamma} {t = App t1 t2} prf
        | Just ty1 | Just ty2 | TyBool = absurd prf
type_checking_sound {gamma} {t = Abs x ty t} prf with (_)
  type_checking_sound {gamma} {t = Abs x ty t} prf | with_pat = ?type_checking_sound_rhs_3_rhs

type_checking_sound {t = Tru} prf = rewrite sym (justInjective prf) in T_Tru
type_checking_sound {t = Fls} prf = rewrite sym (justInjective prf) in T_Fls
type_checking_sound {gamma} {t = Test cond tt tf} prf
  with (type_check gamma cond) proof cond_prf
    type_checking_sound {gamma} {t = Test cond tt tf} prf | Nothing =
      absurd prf
    type_checking_sound {gamma} {t = Test cond tt tf} prf
    | Just ty_cond with (type_check gamma tt) proof tt_prf
      type_checking_sound {gamma} {t = Test cond tt tf} prf
      | Just ty_cond | Nothing = absurd prf
      type_checking_sound {gamma} {t = Test cond tt tf} prf
      | Just ty_cond | Just ty_t with (type_check gamma tf) proof tf_prf
        type_checking_sound {gamma} {t = Test cond tt tf} prf
        | Just ty_cond | Just ty_t | Nothing = absurd prf
        type_checking_sound {gamma} {t = Test cond tt tf} prf
        | Just ty_cond | Just ty_t | Just ty_f with (ty_cond)
          type_checking_sound {gamma} {t = Test cond tt tf} prf
          | Just ty_cond | Just ty_t | Just ty_f | TyBool
            with (beq_ty ty_t ty_f) proof ty_prf
              type_checking_sound {gamma} {t = Test cond tt tf} prf
              | Just ty_cond | Just ty_t | Just ty_f | TyBool | False =
                absurd prf
              type_checking_sound {gamma} {t = Test cond tt tf} prf
              | Just ty_cond | Just ty_t | Just ty_f | TyBool | True =
                rewrite sym (justInjective prf)
                in T_Test (type_checking_sound (sym cond_prf))
                          (type_checking_sound (sym tt_prf))
                          (rewrite beq_ty__eq {ty1=ty_t} {ty2=ty_f}
                                              (sym ty_prf)
                           in type_checking_sound (sym tf_prf))
          type_checking_sound {gamma} {t = Test cond tt tf} prf
          | Just ty_cond | Just ty_t | Just ty_f | TyArrow _ _ = absurd prf
