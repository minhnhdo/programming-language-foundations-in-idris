module Inequiv

import Equiv
import Imp
import Maps

%access public export

%default total

subst_aexp : (x : Id) -> (u : AExp) -> (a : AExp) -> AExp
subst_aexp x u (ANum k) = ANum k
subst_aexp x u (AId y) = case decEq x y of
  Yes prf => u
  No contra => AId y
subst_aexp x u (APlus a1 a2) = APlus (subst_aexp x u a1) (subst_aexp x u a2)
subst_aexp x u (AMinus a1 a2) = AMinus (subst_aexp x u a1) (subst_aexp x u a2)
subst_aexp x u (AMult a1 a2) = AMult (subst_aexp x u a1) (subst_aexp x u a2)

subst_aexp_example : subst_aexp X (42 + 53) (AId Y + AId X) = AId Y + (42 + 53)
subst_aexp_example = Refl

FaultySubstEquivProperty : Type
FaultySubstEquivProperty = (x1, x2 : Id) -> (a1, a2 : AExp) ->
                           CEquiv (do x1 ::= a1; x2 ::= a2)
                                  (do x1 ::= a1; x2 ::= subst_aexp x1 a1 a2)

subst_inequiv : Not FaultySubstEquivProperty
subst_inequiv equiv =
  let -- c1 and c2 are defined only for illustration
      c1 = do X ::= AId X + 1
              Y ::= AId X
      c2 = do X ::= AId X + 1
              Y ::= AId X + 1
      c1_equiv_c2 = equiv X Y (AId X + 1) (AId X)
      st1 = t_update Y 1 $ t_update X 1 $ empty_state
      st2 = t_update Y 2 $ t_update X 1 $ empty_state
      h1 = fst (c1_equiv_c2 empty_state st1)
               (E_Seq (E_Ass Refl) (E_Ass Refl))
      h2 = snd (c1_equiv_c2 empty_state st2)
               (E_Seq (E_Ass Refl) (E_Ass Refl))
      h = snd (c1_equiv_c2 empty_state st1) h1
      st1_eq_st2 = ceval_deterministic h h2
      contra = cong {f=\st => st Y} st1_eq_st2
  in absurd $ succInjective 0 1 contra

data VarNotUsedInAExp : (x : Id) -> AExp -> Type where
  VNUNum : (n : Nat) -> VarNotUsedInAExp x (ANum n)
  VNUId : (y : Id) -> Not (x = y) -> VarNotUsedInAExp x (AId y)
  VNUPlus : (a1, a2 : AExp) ->
            VarNotUsedInAExp x a1 ->
            VarNotUsedInAExp x a2 ->
            VarNotUsedInAExp x (a1 + a2)
  VNUMinus : (a1, a2 : AExp) ->
             VarNotUsedInAExp x a1 ->
             VarNotUsedInAExp x a2 ->
             VarNotUsedInAExp x (AMinus a1 a2)
  VNUMult : (a1, a2 : AExp) ->
            VarNotUsedInAExp x a1 ->
            VarNotUsedInAExp x a2 ->
            VarNotUsedInAExp x (a1 * a2)

aeval_weakening : VarNotUsedInAExp x a ->
                  aeval (t_update x n st) a = aeval st a
aeval_weakening (VNUNum _) = Refl
aeval_weakening (VNUId _ contra) =
  rewrite snd beq_id_false_iff contra
  in Refl
aeval_weakening {x} {st} {n} (VNUPlus _ _ vnua1 vnua2) =
  rewrite aeval_weakening {x=x} {st=st} {n=n} vnua1
  in rewrite aeval_weakening {x=x} {st=st} {n=n} vnua2
  in Refl
aeval_weakening {x} {st} {n} (VNUMinus _ _ vnua1 vnua2) =
  rewrite aeval_weakening {x=x} {st=st} {n=n} vnua1
  in rewrite aeval_weakening {x=x} {st=st} {n=n} vnua2
  in Refl
aeval_weakening {x} {st} {n} (VNUMult _ _ vnua1 vnua2) =
  rewrite aeval_weakening {x=x} {st=st} {n=n} vnua1
  in rewrite aeval_weakening {x=x} {st=st} {n=n} vnua2
  in Refl

subst_aexp_equiv : VarNotUsedInAExp x a -> AEquiv a (subst_aexp x u a)
subst_aexp_equiv (VNUNum _) _ = Refl
subst_aexp_equiv {x} {u} (VNUId y contra) _ with (decEq x y)
  subst_aexp_equiv (VNUId y contra) _ | Yes prf = absurd $ contra prf
  subst_aexp_equiv (VNUId y contra) _ | No _ = Refl
subst_aexp_equiv {u} (VNUPlus _ _ xnua1 xnua2) st =
  let a1_equiv = subst_aexp_equiv {u=u} xnua1 st
      a2_equiv = subst_aexp_equiv {u=u} xnua2 st
  in rewrite a1_equiv
  in rewrite a2_equiv
  in Refl
subst_aexp_equiv {u} (VNUMinus _ _ xnua1 xnua2) st =
  let a1_equiv = subst_aexp_equiv {u=u} xnua1 st
      a2_equiv = subst_aexp_equiv {u=u} xnua2 st
  in rewrite a1_equiv
  in rewrite a2_equiv
  in Refl
subst_aexp_equiv {u} (VNUMult _ _ xnua1 xnua2) st =
  let a1_equiv = subst_aexp_equiv {u=u} xnua1 st
      a2_equiv = subst_aexp_equiv {u=u} xnua2 st
  in rewrite a1_equiv
  in rewrite a2_equiv
  in Refl

SubstEquivProperty : Type
SubstEquivProperty = (x1, x2 : Id) -> (a1, a2 : AExp) ->
                     VarNotUsedInAExp x1 a2 ->
                     CEquiv (do x1 ::= a1; x2 ::= a2)
                            (do x1 ::= a1; x2 ::= subst_aexp x1 a1 a2)

subst_equiv_property : SubstEquivProperty
subst_equiv_property _ _ _ _ x1nua2 =
  cSeq_congruence refl_cequiv (cAss_congruence (subst_aexp_equiv x1nua2))

inequiv_exercise : Not (CEquiv (CWhile BTrue CSkip) CSkip)
inequiv_exercise equiv =
  let nonterm_prf = while_true_nonterm refl_bequiv
      nonterm_equiv_skip = equiv empty_state empty_state
  in nonterm_prf $ snd nonterm_equiv_skip E_Skip
