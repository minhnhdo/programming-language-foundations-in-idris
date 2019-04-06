module Equiv

import Imp
import Logic
import Maps

%access public export

%default total

AEquiv : (a1, a2 : AExp) -> Type
AEquiv a1 a2 = (st : State) -> aeval st a1 = aeval st a2

BEquiv : (b1, b2 : BExp) -> Type
BEquiv b1 b2 = (st : State) -> beval st b1 = beval st b2

AEquiv_example : AEquiv (AMinus (AId X) (AId X)) (ANum 0)
AEquiv_example st with (st X)
  AEquiv_example st | Z = Refl
  AEquiv_example st | S k = sym $ minusZeroN k

BEquiv_example : BEquiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue
BEquiv_example st with (st X)
  BEquiv_example st | Z = Refl
  BEquiv_example st | S k = rewrite sym $ minusZeroN k in Refl

CEquiv : (c1, c2 : Com) -> Type
CEquiv c1 c2 = (st, st' : State) -> ((c1 / st \\ st') ↔ (c2 / st \\ st'))

skip_left : CEquiv (do SKIP; c) c
skip_left st st' = (forward, backward)
where forward : ((do SKIP; c) / st \\ st') -> (c / st \\ st')
      forward (E_Seq E_Skip rel) = rel
      backward : (c / st \\ st') -> ((do SKIP; c) / st \\ st')
      backward rel = E_Seq E_Skip rel

skip_right : CEquiv (do c; SKIP) c
skip_right st st' = (forward, backward)
where forward : ((do c; SKIP) / st \\ st') -> (c / st \\ st')
      forward (E_Seq rel E_Skip) = rel
      backward : (c / st \\ st') -> ((do c; SKIP) / st \\ st')
      backward rel = E_Seq rel E_Skip

test_true_simple : CEquiv (IFB BTrue THEN c1 ELSE c2 FI) c1
test_true_simple st st' = (forward, backward)
where forward : ((IFB BTrue THEN c1 ELSE c2 FI) / st \\ st') ->
                (c1 / st \\ st')
      forward (E_IfTrue _ rel) = rel
      forward (E_IfFalse prf _) = absurd prf
      backward : (c1 / st \\ st') ->
                 ((IFB BTrue THEN c1 ELSE c2 FI) / st \\ st')
      backward rel = E_IfTrue Refl rel

test_true : BEquiv b BTrue -> CEquiv (IFB b THEN c1 ELSE c2 FI) c1
test_true {b} btrue st st' = (forward, backward)
where forward : ((IFB b THEN c1 ELSE c2 FI) / st \\ st') ->
                (c1 / st \\ st')
      forward (E_IfTrue _ rel) = rel
      forward (E_IfFalse prf _) = absurd $ trans (sym $ btrue st) prf
      backward : (c1 / st \\ st') ->
                 ((IFB b THEN c1 ELSE c2 FI) / st \\ st')
      backward rel = E_IfTrue (btrue st) rel

test_false : BEquiv b BFalse -> CEquiv (IFB b THEN c1 ELSE c2 FI) c2
test_false {b} bfalse st st' = (forward, backward)
where forward : ((IFB b THEN c1 ELSE c2 FI) / st \\ st') ->
                (c2 / st \\ st')
      forward (E_IfTrue prf _) = absurd $ trans (sym $ bfalse st) prf
      forward (E_IfFalse _ rel) = rel
      backward : (c2 / st \\ st') ->
                 ((IFB b THEN c1 ELSE c2 FI) / st \\ st')
      backward rel = E_IfFalse (bfalse st) rel

swap_if_branches : CEquiv (IFB b THEN c1 ELSE c2 FI)
                          (IFB BNot b THEN c2 ELSE c1 FI)
swap_if_branches {b} st st' = (forward, backward)
where forward : ((IFB b THEN c1 ELSE c2 FI) / st \\ st') ->
                ((IFB BNot b THEN c2 ELSE c1 FI) / st \\ st')
      forward (E_IfTrue prf rel) = E_IfFalse (cong {f=not} prf) rel
      forward (E_IfFalse prf rel) = E_IfTrue (cong {f=not} prf) rel
      backward : ((IFB BNot b THEN c2 ELSE c1 FI) / st \\ st') ->
                 ((IFB b THEN c1 ELSE c2 FI) / st \\ st')
      backward (E_IfTrue prf rel) =
        E_IfFalse (trans (sym $ notInvolutive (beval st b))
                         (cong {f=not} prf))
                  rel
      backward (E_IfFalse prf rel) =
        E_IfTrue (trans (sym $ notInvolutive (beval st b))
                        (cong {f=not} prf))
                 rel

while_false : BEquiv b BFalse -> CEquiv (WHILE b c) SKIP
while_false {b} bfalse st _ = (forward, backward)
where forward : ((WHILE b c) / st \\ st') -> (SKIP / st \\ st')
      forward rel = case rel of
        E_WhileEnd _ => E_Skip
        E_WhileLoop prf _ _ => absurd $ trans (sym $ bfalse st) prf
      backward : (SKIP / st \\ st') -> ((WHILE b c) / st \\ st')
      backward rel = case rel of
        E_Skip => E_WhileEnd (bfalse st)
