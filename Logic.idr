module Logic

%access public export

%default total

notInvolutive : (b : Bool) -> not (not b) = b
notInvolutive False = Refl
notInvolutive True = Refl

iff : {p, q : Type} -> Type
iff {p} {q} = (p -> q, q -> p)

syntax [p] "↔" [q] = iff {p} {q}

iff_sym : (p ↔ q) -> (q ↔ p)
iff_sym (p_imp_q, q_imp_p) = (q_imp_p, p_imp_q)

not_true_iff_false : (Not (b = True)) ↔ (b = False)
not_true_iff_false {b} = (not_true_is_false b, not_true_and_false b)
  where not_true_and_false : (b : Bool) -> (b = False) -> Not (b = True)
        not_true_and_false False _ Refl impossible
        not_true_and_false True Refl _ impossible
        not_true_is_false : (b : Bool) -> Not (b = True) -> b = False
        not_true_is_false False _ = Refl
        not_true_is_false True h = absurd $ h Refl

iff_refl : p ↔ p
iff_refl = (id, id)

iff_trans : (p ↔ q) -> (q ↔ r) -> (p ↔ r)
iff_trans (p_imp_q, q_imp_p) (q_imp_r, r_imp_q) =
  (q_imp_r . p_imp_q, q_imp_p . r_imp_q)
