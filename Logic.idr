module Logic

%access public export

%default total

notInvolutive : (b : Bool) -> not (not b) = b
notInvolutive False = Refl
notInvolutive True = Refl

neqSym : Not (a = b) -> Not (b = a)
neqSym contra prf = contra $ sym prf

band : b1 && b2 = True -> (b1 = True, b2 = True)
band {b1 = False} prf = absurd prf
band {b1 = True} prf = (Refl, prf)

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

nat_beq_iff : (n, m : Nat) -> (n == m = True) ↔ (n = m)
nat_beq_iff = \n, m => (forward n m, backward n m)
where forward : (n, m : Nat) -> n == m = True -> n = m
      forward Z Z _ = Refl
      forward Z (S _) prf = absurd prf
      forward (S _) Z prf = absurd prf
      forward (S k) (S j) prf = cong {f=S} (forward k j prf)
      backward : (n, m : Nat) -> n = m -> n == m = True
      backward Z Z _ = Refl
      backward Z (S _) prf = absurd prf
      backward (S _) Z prf = absurd prf
      backward (S k) (S j) prf = backward k j (succInjective k j prf)

nat_nbeq_iff : (n, m : Nat) -> (n == m = False) ↔ (Not (n = m))
nat_nbeq_iff = \n, m => (forward n m, backward n m)
where forward : (n, m : Nat) -> n == m = False -> Not (n = m)
      forward Z Z bprf _ = absurd bprf
      forward Z (S _) _ prf = SIsNotZ $ sym prf
      forward (S _) Z _ prf = SIsNotZ prf
      forward (S k) (S j) bprf prf = forward k j bprf (succInjective k j prf)
      backward : (n, m : Nat) -> Not (n = m) -> n == m = False
      backward Z Z contra = absurd $ contra Refl
      backward Z (S _) _ = Refl
      backward (S _) Z _ = Refl
      backward (S k) (S j) contra =
        backward k j (\prf => contra (cong {f=S} prf))

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

lte_nbeq_iff : (n, m : Nat) -> ((lte n m = False) ↔ (LT m n))
lte_nbeq_iff = \n, m => (forward, backward)
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

lte_succ_minus : LTE n m -> minus (S m) n = S (minus m n)
lte_succ_minus {n = Z} {m} lte_prf = rewrite minusZeroRight m in Refl
lte_succ_minus {n = S _} {m = Z} lte_prf = absurd $ succNotLTEzero lte_prf
lte_succ_minus {n = S k} {m = S j} lte_prf = lte_succ_minus (fromLteSucc lte_prf)

lte_minus_plus_sum : LTE k n -> minus n k + plus m k = n + m
lte_minus_plus_sum {k = Z} {n} {m} lte_prf =
  rewrite minusZeroRight n
  in rewrite plusZeroRightNeutral m
  in Refl
lte_minus_plus_sum {k = S _} {n = Z} lte_prf = absurd $ succNotLTEzero lte_prf
lte_minus_plus_sum {k = S i} {n = S k} {m} lte_prf =
  rewrite sym (plusSuccRightSucc m i)
  in rewrite sym (plusSuccRightSucc (minus k i) (m + i))
  in cong (lte_minus_plus_sum (fromLteSucc lte_prf))

bounded__eq : LTE n m -> LTE m n -> n = m
bounded__eq {n = Z} _ above = sym $ lte_z__eq_z above
bounded__eq {n = S _} {m = Z} below _ = absurd $ succNotLTEzero below
bounded__eq {n = S _} {m = S _} below above =
  cong $ bounded__eq (fromLteSucc below) (fromLteSucc above)

notZeroImpliesGTZero : Not (n = 0) -> LT 0 n
notZeroImpliesGTZero {n = Z} contra = absurd $ contra Refl
notZeroImpliesGTZero {n = (S _)} _ = LTESucc LTEZero

plusCong : {a, b, n, m : Nat} -> a = n -> b = m -> a + b = n + m
plusCong prf1 prf2 = rewrite prf1 in rewrite prf2 in Refl

fromNotLteSucc : Not (LTE (S n) (S m)) -> Not (LTE n m)
fromNotLteSucc contra lte_prf = contra (LTESucc lte_prf)

lteImpliesNotGT : LTE n m -> Not (GT n m)
lteImpliesNotGT {n = Z} _ = succNotLTEzero
lteImpliesNotGT {n = S _} {m = Z} lte_prf = absurd $ succNotLTEzero lte_prf
lteImpliesNotGT {n = S k} {m = S j} lte_prf = \succ_prf =>
  lteImpliesNotGT (fromLteSucc lte_prf) (fromLteSucc succ_prf)

Relation : (p : Type) -> Type
Relation p = p -> p -> Type

Deterministic : (r : Relation p) -> Type
Deterministic {p} r = {x, y1, y2 : p} -> r x y1 -> r x y2 -> y1 = y2

NormalForm : (r : Relation t) -> (x : t) -> Type
NormalForm r x = Not (x' ** r x x')

data Multi : {t : Type} -> (r : Relation t) -> Relation t where
  MultiRefl : Multi r x x
  MultiStep : r x y -> Multi r y z -> Multi r x z

multi_R : {r : Relation t} -> r x y -> Multi r x y
multi_R rxy = MultiStep rxy MultiRefl

multi_trans : {r : Relation t} -> Multi r x y -> Multi r y z -> Multi r x z
multi_trans MultiRefl ryz = ryz
multi_trans (MultiStep once next) ryz = MultiStep once (multi_trans next ryz)
