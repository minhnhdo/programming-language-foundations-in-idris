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
