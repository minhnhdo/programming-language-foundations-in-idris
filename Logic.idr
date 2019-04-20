module Logic

%access public export

%default total

notInvolutive : (b : Bool) -> not (not b) = b
notInvolutive False = Refl
notInvolutive True = Refl

neqSym : Not (a = b) -> Not (b = a)
neqSym contra prf = contra $ sym prf

n_eq_succ__n_neq_0 : n = S k -> Not (n = 0)
n_eq_succ__n_neq_0 n_eq_succ n_eq_0 = SIsNotZ $ trans (sym n_eq_succ) n_eq_0

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

nat_beq_iff : {n, m : Nat} -> (n == m = True) ↔ (n = m)
nat_beq_iff = (forward, backward)
where forward : {n, m : Nat} -> n == m = True -> n = m
      forward {n = Z} {m = Z} _ = Refl
      forward {n = Z} {m = S _} prf = absurd prf
      forward {n = S _} {m = Z} prf = absurd prf
      forward {n = S k} {m = S j} prf = cong {f=S} (forward prf)
      backward : {n, m : Nat} -> n = m -> n == m = True
      backward {n = Z} {m = Z} _ = Refl
      backward {n = Z} {m = S _} prf = absurd prf
      backward {n = S _} {m = Z} prf = absurd prf
      backward {n = S k} {m = S j} prf = backward (succInjective k j prf)

nat_nbeq_iff : {n, m : Nat} -> (n == m = False) ↔ (Not (n = m))
nat_nbeq_iff = (forward, backward)
where forward : {n, m : Nat} -> n == m = False -> Not (n = m)
      forward {n = Z} {m = Z} bprf _ = absurd bprf
      forward {n = Z} {m = S _} _ prf = SIsNotZ $ sym prf
      forward {n = S _} {m = Z} _ prf = SIsNotZ prf
      forward {n = S k} {m = S j} bprf prf = forward bprf (succInjective k j prf)
      backward : {n, m : Nat} -> Not (n = m) -> n == m = False
      backward {n = Z} {m = Z} contra = absurd $ contra Refl
      backward {n = Z} {m = S _} _ = Refl
      backward {n = S _} {m = Z} _ = Refl
      backward {n = S k} {m = S j} contra =
        backward {n=k} {m=j} (\prf => contra (cong {f=S} prf))

lte_plus_minus : LTE n m -> n + (minus m n) = m
lte_plus_minus {n = Z} {m} _ = minusZeroRight m
lte_plus_minus {n = S _} {m = Z} succ_lte_m = absurd $ succNotLTEzero succ_lte_m
lte_plus_minus {n = S k} {m = S j} succ_lte_m =
  cong $ lte_plus_minus (fromLteSucc succ_lte_m)

lte_beq_iff : (n, m : Nat) -> ((lte n m = True) ↔ (LTE n m))
lte_beq_iff = \n, m => (forward, backward)
where forward : lte n m = True -> LTE n m
      forward {n = Z} _ = LTEZero
      forward {n = S _} {m = Z} prf = absurd prf
      forward {n = S k} {m = S j} prf = LTESucc (forward prf)
      backward : LTE n m -> lte n m = True
      backward LTEZero = Refl
      backward (LTESucc lte_prf) = backward lte_prf

lte_false_lt_iff : (n, m : Nat) -> ((lte n m = False) ↔ (LT m n))
lte_false_lt_iff = \n, m => (forward, backward)
where forward : lte n m = False -> LT m n
      forward {n = Z} prf = absurd prf
      forward {n = S _} {m = Z} _ = LTESucc LTEZero
      forward {n = S k} {m = S j} prf = LTESucc $ forward {n=k} {m=j} prf
      backward : LT m n -> lte n m = False
      backward {n = Z} lt_prf = absurd $ succNotLTEzero lt_prf
      backward {n = S _} {m = Z} _ = Refl
      backward {n = S k} {m = S j} lt_prf = backward (fromLteSucc lt_prf)

lte_z__eq_z : LTE n 0 -> n = 0
lte_z__eq_z {n = Z} _ = Refl
lte_z__eq_z {n = S _} lte_prf = absurd $ succNotLTEzero lte_prf

bounded__eq : LTE n m -> LTE m n -> n = m
bounded__eq {n = Z} _ above = sym $ lte_z__eq_z above
bounded__eq {n = S _} {m = Z} below _ = absurd $ succNotLTEzero below
bounded__eq {n = S _} {m = S _} below above =
  cong $ bounded__eq (fromLteSucc below) (fromLteSucc above)
