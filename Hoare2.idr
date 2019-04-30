module Hoare2

import Assn
import Expr
import Hoare
import Imp
import Logic
import Maps

%access public export

%default total

reduce_to_zero : Com
reduce_to_zero = WHILE (not (X == 0)) $
                   X ::= X - 1

reduce_to_zero_correct : HoareTriple (const ())
                                     Hoare2.reduce_to_zero
                                     (\st => st X = 0)
reduce_to_zero_correct =
  let htc = hoare_consequence_pre
              (\st => ((), BAssn (not (X == 0)) st))
              (AssignSub X (X - 1) (const ()))
              (const ())
              (X ::= X - 1)
              (hoare_assign (const ()) X (X - 1))
              (\_, _ => ())
      htw = hoare_while (const ())
                        (not (X == 0))
                        (X ::= X - 1)
                        htc
  in hoare_consequence_post
       (const ())
       (\st => st X = 0)
       (\st => ((), Not (BAssn (not (X == 0)) st)))
       Hoare2.reduce_to_zero
       htw
       (\st, (_, contra) =>
           fst (nat_beq_iff (st X) 0)
               (trans (sym (notInvolutive (st X == 0)))
                      (cong {f=not} (fst not_true_iff_false contra))))

slow_assignment : Com
slow_assignment = do
  {-
    {{ X = m }}
    ->> {{ (X = m, Y = n) }}
  -}
  Y ::= 0
  {-
    {{ (X = m, Y = 0) }}
    ->> {{ X + Y = m }}
  -}
  WHILE (not (X == 0)) $ do
    {-
      {{ (X + Y = m, not (X == 0)) }}
      ->> {{ X - 1 + Y + 1 = m }}
    -}
    X ::= X - 1
    -- {{ X + Y + 1 = m }}
    Y ::= Y + 1
    -- {{ X + Y = m }}
  {-
    {{ (X + Y = m, Not (not (X == 0))) }}
    ->> {{ Y = m }}
  -}

slow_assignment_correct : HoareTriple (\st => st X = m)
                                      Hoare2.slow_assignment
                                      (\st => st Y = m)
slow_assignment_correct {m} =
  let hty = hoare_consequence_pre
              (\st => st X = m)
              (AssignSub Y 0 (\st => (st X = m, st Y = 0)))
              (\st => (st X = m, st Y = 0))
              (Y ::= 0)
              (hoare_assign (\st => (st X = m, st Y = 0)) Y 0)
              (\st, p_st => (p_st, Refl))
      htx = hoare_consequence_pre
              (\st => (st X + st Y = m, BAssn (not (X == 0)) st))
              (\st => minus (st X) 1 + (st Y + 1) = m)
              (\st => st X + (st Y + 1) = m)
              (X ::= X - 1)
              (hoare_assign (\st => st X + (st Y + 1) = m) X (X - 1))
              (\st, (prf, x_prf) =>
                  let lte_prf =
                        notZeroImpliesGTZero
                          (fst (nat_nbeq_iff (st X) 0)
                               (trans (sym (notInvolutive (st X == 0)))
                                      (cong {f=not} x_prf)))
                  in rewrite sym prf
                  in lte_minus_plus_sum lte_prf)
      hty' = hoare_assign (\st => st X + st Y = m) Y (Y + 1)
      ht_body = hoare_seq (\st => (st X + st Y = m, BAssn (not (X == 0)) st))
                          (\st => st X + (st Y + 1) = m)
                          (\st => st X + st Y = m)
                          (X ::= X - 1)
                          (Y ::= Y + 1)
                          hty'
                          htx
      htw = hoare_consequence_pre
              (\st => (st X = m, st Y = 0))
              (\st => st X + st Y = m)
              (\st => (st X + st Y = m, Not (BAssn (not (X == 0)) st)))
              (WHILE (not (X == 0)) $ do
                 X ::= X - 1
                 Y ::= Y + 1)
              (hoare_while (\st => st X + st Y = m)
                           (not (X == 0))
                           (do X ::= X - 1
                               Y ::= Y + 1)
                           ht_body)
              (\_, (x_prf, y_prf) => trans (plusCong x_prf y_prf)
                                           (plusZeroRightNeutral m))
      ht_program = hoare_seq (\st => st X = m)
                             (\st => (st X = m, st Y = 0))
                             (\st => ( st X + st Y = m
                                     , Not (BAssn (not (X == 0)) st) ))
                             (Y ::= 0)
                             (WHILE (not (X == 0)) $ do
                                X ::= X - 1
                                Y ::= Y + 1)
                             htw
                             hty
  in hoare_consequence_post
       (\st => st X = m)
       (\st => st Y = m)
       (\st => (st X + st Y = m, Not (BAssn (not (X == 0)) st)))
       Hoare2.slow_assignment
       ht_program
       (\st, (prf, contra) =>
           let st_X_eq_0 =
                 fst (nat_beq_iff (st X) 0)
                     (trans (sym (notInvolutive (st X == 0)))
                            (cong {f=not} (fst not_true_iff_false contra)))
           in replace {P=\x => x + st Y = m} st_X_eq_0 prf)

add_slowly : Com
add_slowly =
  {-
    {{ (X = m, Z = n) }}
    ->> {{ X + Z = m + n }}
  -}
  WHILE (not (X == 0)) $ do
    {-
      {{ (X + Z = m + n, BAssn (not (X == 0)) st) }}
      ->> {{ X - 1 + Z + 1 = m + n }}
    -}
    Z ::= Z + 1
    -- {{ X - 1 + Z = m + n }}
    X ::= X - 1
    -- {{ X + Z = m + n }}
  {-
    {{ (X + Z = m + n, Not (BAssn (not (X == 0)) st)) }}
    ->> {{ Z = m + n }}
  -}

parity : Nat -> Nat
parity Z = 0
parity (S Z) = 1
parity (S (S k)) = parity k

parity_ge_2 : (n : Nat) -> LTE 2 n -> parity (minus n 2) = parity n
parity_ge_2 Z lte_prf = absurd $ succNotLTEzero lte_prf
parity_ge_2 (S Z) lte_prf = absurd $ succNotLTEzero (fromLteSucc lte_prf)
parity_ge_2 (S (S k)) lte_prf = rewrite minusZeroRight k
                                in Refl

parity_lt_2 : (n : Nat) -> Not (LTE 2 n) -> parity n = n
parity_lt_2 Z _ = Refl
parity_lt_2 (S Z) _ = Refl
parity_lt_2 (S (S k)) contra =
  let lte_prf = notLTImpliesGTE contra
  in absurd $ succNotLTEzero (fromLteSucc lte_prf)

parity_correct : HoareTriple (\st => st X = m)
                             (WHILE (2 <= X) $ do
                                X ::= X - 2)
                             (\st => st X = parity m)
parity_correct {m} =
  let htx = hoare_consequence_pre
              (\st => (parity (st X) = parity m, BAssn (2 <= X) st))
              (AssignSub X (X - 2) (\st => parity (st X) = parity m))
              (\st => parity (st X) = parity m)
              (X ::= X - 2)
              (hoare_assign (\st => parity (st X) = parity m) X (X - 2))
              (\st, (prf, cond_prf) =>
                  rewrite parity_ge_2 (st X)
                                      (fst (lte_beq_iff 2 (st X)) cond_prf)
                  in prf)
      htw = hoare_while (\st => parity (st X) = parity m)
                        (2 <= X)
                        (X ::= X - 2)
                        htx
  in hoare_consequence
       (\st => st X = m)
       (\st => parity (st X) = parity m)
       (\st => st X = parity m)
       (\st => (parity (st X) = parity m, Not (BAssn (2 <= X) st)))
       (WHILE (2 <= X) $ do
          X ::= X - 2)
       htw
       (\st, p_st => cong p_st)
       (\st, (prf, nbeq_prf) =>
           let lte_prf = fst (lte_nbeq_iff 2 (st X))
                             (fst not_true_iff_false nbeq_prf)
               contra = fromNotLteSucc (lteImpliesNotGT lte_prf)
           in rewrite sym prf
           in sym (parity_lt_2 (st X) contra))

factorial : Com
factorial = do
  {-
    {{ X = m }}
    ->> {{ 1 * X! = m! }}
  -}
  Y ::= 1
  -- {{ Y * X! = m! }}
  WHILE (not (X == 0)) $ do
    {-
      {{ (Y * X! = m!, BAssn (not (X == 0)) st) }}
      ->> {{ Y * X * (X - 1)! = m! }}
    -}
    Y ::= Y * X
    -- {{ Y * (X - 1)! = m! }}
    X ::= X - 1
    -- {{ Y * X! = m! }}
  {-
    {{ (Y * X! = m!, Not (BAssn (not (X == 0)) st)) }}
    ->> {{ Y = m! }}
  -}

lemma1 : (x, y : Nat) -> Either (x = 0) (y = 0) -> minimum x y = 0
lemma1 _ _ (Left x_prf) = rewrite x_prf in Refl
lemma1 Z _ (Right _) = Refl
lemma1 (S _) _ (Right y_prf) = rewrite y_prf in Refl

lemma2 : (x, y : Nat) ->
         minimum (x `minus` 1) (y `minus` 1) = minimum x y `minus` 1
lemma2 Z _ = Refl
lemma2 (S k) Z = minimumZeroZeroLeft (minus k 0)
lemma2 (S k) (S j) = rewrite minusZeroRight k
                     in rewrite minusZeroRight j
                     in rewrite minusZeroRight (minimum k j)
                     in Refl

min : (a, b : Nat) -> Com
min a b = do
  {-
    {{ () }}
    ->> {{ 0 = minimum a b - minimum a b }}
  -}
  X ::= ANum a
  -- {{ 0 = minimum a b - minimum X b }}
  Y ::= ANum b
  -- {{ 0 = minimum a b - minimum X Y }}
  Z ::= 0
  -- {{ Z = minimum a b - minimum X Y }}
  WHILE (not (X == 0) && not (Y == 0)) $ do
    {-
      {{ (Z = minimum a b - minimum X Y, BAssn (not (X == 0) && not (Y == 0)) st) }}
      ->> {{ Z + 1 = minimum a b - minimum (X - 1) (Y - 1) }}
    -}
    X ::= X - 1
    -- {{ Z + 1 = minimum a b - minimum X (Y - 1) }}
    Y ::= Y - 1
    -- {{ Z + 1 = minimum a b - minimum X Y }}
    Z ::= Z + 1
    -- {{ Z = minimum a b - minimum X Y }}
  {-
    {{ (Z = minimum a b - minimum X Y, Not (BAssn (not (X == 0) && not (Y == 0)) st)) }}
    ->> {{ Z ::= minimum a b }}
  -}

two_loops : (a, b, c : Nat) -> Com
two_loops a b c = do
  {-
    {{ () }}
    ->> {{ c = 0 + 0 + c }}
  -}
  X ::= 0
  -- {{ c = X + 0 + c }}
  Y ::= 0
  -- {{ c = X + Y + c }}
  Z ::= ANum c
  -- {{ Z = X + Y + c }}
  WHILE (not (X == ANum a)) $ do
    {-
      {{ (Z = X + Y + c, BAssn (not (X == a)) st) }}
      ->> {{Z + 1 = X + 1 + Y + c }}
    -}
    X ::= X + 1
    -- {{ Z + 1 = X + Y + c }}
    Z ::= Z + 1
    -- {{ Z = X + Y + c }}
  {-
    {{ (Z = X + Y + c, Not (BAssn (not (X == a)) st)) }}
    ->> {{ Z = a + Y + c }}
  -}
  WHILE (not (Y == ANum b)) $ do
    {-
      {{ (Z = a + Y + c, BAssn (not (Y == b)) st) }}
      ->> {{ Z + 1 = a + Y + 1 + c }}
    -}
    Y ::= Y + 1
    -- {{ Z + 1 = a + Y + c }}
    Z ::= Z + 1
    -- {{ Z = a + Y + c }}
  {-
    {{ (Z = a + Y + c, Not (BAssn (not (Y == b)) st)) }}
    ->> {{ Z = a + b + c }}
  -}

dpow2_down : (m : Nat) -> Com
dpow2_down m = do
  {-
    {{ () }}
    ->> {{ (1 = 2^(0+1) - 1, 1 = 2^0) }}
  -}
  X ::= 0
  -- {{ (1 = 2^(X+1) - 1, 1 = 2^X) }}
  Y ::= 1
  -- {{ (Y = 2^(X+1) - 1, 1 = 2^X) }}
  Z ::= 1
  -- {{ (Y = 2^(X+1) - 1, Z = 2^X) }}
  WHILE (not (X == ANum m)) $ do
    {-
      {{ (Y = 2^(X+1) - 1, Z = 2^X, BAssn (not (X == m)) st) }}
      ->> {{ (Y + 2*Z = 2^(X+1+1) - 1, 2*Z = 2^(X+1)) }}
    -}
    Z ::= 2 * Z
    -- {{ (Y + Z = 2^(X+1+1) - 1, Z = 2^(X+1)) }}
    Y ::= Y + Z
    -- {{ (Y = 2^(X+1+1) - 1, Z = 2^(X+1)) }}
    X ::= X + 1
    -- {{ (Y = 2^(X+1) - 1, Z = 2^X) }}
  {-
    {{ (Y = 2^(X+1) - 1, Z = 2^X, Not (BAssn (not (X == m)) st)) }}
    ->> {{ Y = 2^(m+1) - 1 }}
  -}

IsWP : (p : Assertion) -> (c : Com) -> (q : Assertion) -> Type
IsWP p c q = ( HoareTriple p c q
             , (p' : Assertion) -> HoareTriple p' c q -> p' ->> p )

{-
  {{ X = 5 }} SKIP {{ X = 5 }}

  {{ Y + Z = 5 }} X ::= Y + Z {{ X = 5 }}

  {{ True }} X ::= Y {{ X = Y }}

  {{ Either (X = 0, Z = 4) (Not (X = 0), W = 3) }}
  IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
  {{ Y = 5 }}

  {{ Void }} X ::= 5 {{ X = 0 }}

  {{ () }}
  WHILE BTrue $ do X ::= 0
  {{ X = 0 }}
-}

is_wp_example : IsWP (\st => LTE (st Y) 4)
                     (X ::= Y + 1)
                     (\st => LTE (st X) 5)
is_wp_example = (ht, imp)
where ht : HoareTriple (\st => LTE (st Y) 4) (X ::= Y + 1) (\st => LTE (st X) 5)
      ht = hoare_consequence_pre (\st => LTE (st Y) 4)
                                 (\st => LTE (st Y + 1) 5)
                                 (\st => LTE (st X) 5)
                                 (X ::= Y + 1)
                                 (hoare_assign (\st => LTE (st X) 5) X (Y + 1))
                                 (\st, p_st => rewrite plusCommutative (st Y) 1
                                               in LTESucc p_st)
      imp : (p' : Assertion) ->
            HoareTriple p' (X ::= Y + 1) (\st => LTE (st X) 5) ->
            p' ->> (\st => LTE (st Y) 4)
      imp p' ht' st p'_st =
        fromLteSucc (replace {P=\x => LTE x 5}
                             (plusCommutative (st Y) 1)
                             (ht' st _ (E_Ass Refl) p'_st))

hoare_assign_weakest : IsWP (AssignSub x a q) (x ::= a) q
hoare_assign_weakest {x} {a} {q} = (hoare_assign q x a, imp)
where imp : (p' : Assertion) -> HoareTriple p' (x ::= a) q ->
            p' ->> AssignSub x a q
      imp p' ht st p'_st = ht st _ (E_Ass Refl) p'_st
