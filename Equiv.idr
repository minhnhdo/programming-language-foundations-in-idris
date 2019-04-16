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

AEquiv_example : AEquiv (X - X) 0
AEquiv_example st with (st X)
  AEquiv_example st | Z = Refl
  AEquiv_example st | S k = sym $ minusZeroN k

BEquiv_example : BEquiv (X - X == 0) BTrue
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
                          (IFB not b THEN c2 ELSE c1 FI)
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

while_true_nonterm : BEquiv b BTrue -> Not ((WHILE b c) / st \\ st')
while_true_nonterm {st'} btrue (E_WhileEnd prf) =
  absurd $ trans (sym $ btrue st') prf
while_true_nonterm btrue (E_WhileLoop prf rel next) =
  while_true_nonterm btrue next

while_true : BEquiv b BTrue -> CEquiv (WHILE b c) (WHILE BTrue SKIP)
while_true {b} btrue st st' = (forward, backward)
where forward : ((WHILE b c) / st \\ st') -> ((WHILE BTrue SKIP) / st \\ st')
      forward rel = case rel of
        E_WhileEnd prf => absurd $ trans (sym $ btrue st) prf
        E_WhileLoop _ _ next => void $ while_true_nonterm btrue next
      btrue_is_true : BEquiv BTrue BTrue
      btrue_is_true _ = Refl
      backward : ((WHILE BTrue SKIP) / st \\ st') -> ((WHILE b c) / st \\ st')
      backward rel = case rel of
        E_WhileEnd prf => absurd prf
        E_WhileLoop Refl _ next => void $ while_true_nonterm btrue_is_true next

loop_unrolling : CEquiv (WHILE b c) (IFB b THEN (do c; WHILE b c) ELSE SKIP FI)
loop_unrolling st st' = (forward, backward)
where forward : ((WHILE b c) / st \\ st') ->
                ((IFB b THEN (do c; WHILE b c) ELSE SKIP FI) / st \\ st')
      forward rel = case rel of
        E_WhileEnd prf => E_IfFalse prf E_Skip
        E_WhileLoop prf rel next => E_IfTrue prf (E_Seq rel next)
      backward : ((IFB b THEN (do c; WHILE b c) ELSE SKIP FI) / st \\ st') ->
                 ((WHILE b c) / st \\ st')
      backward (E_IfTrue prf (E_Seq rel next)) = E_WhileLoop prf rel next
      backward (E_IfFalse prf rel) = case rel of
        E_Skip => E_WhileEnd prf

seq_assoc : CEquiv (do (do c1; c2); c3) (do c1; (do c2; c3))
seq_assoc st st' = (forward, backward)
where forward : ((do (do c1; c2); c3) / st \\ st') ->
                ((do c1; (do c2; c3)) / st \\ st')
      forward (E_Seq (E_Seq r1 r2) r3) = E_Seq r1 (E_Seq r2 r3)
      backward : ((do c1; (do c2; c3)) / st \\ st') ->
                 ((do (do c1; c2); c3) / st \\ st')
      backward (E_Seq r1 (E_Seq r2 r3)) = E_Seq (E_Seq r1 r2) r3

identity_assignment : CEquiv (x ::= AId x) SKIP
identity_assignment {x} st st' = (forward, backward)
where forward : ((x ::= AId x) / st \\ st') -> (SKIP / st \\ st')
      forward rel = case rel of
        E_Ass prf => rewrite sym prf
                     in rewrite t_update_same {m=st} {x=x}
                     in E_Skip
      backward : (SKIP / st \\ st') -> ((x ::= AId x) / st \\ st')
      backward rel = case rel of
        E_Skip => replace (t_update_same {m=st} {x=x}) (E_Ass Refl)
                    {P=\s => (x ::= AId x) / st \\ s}

assign_aequiv : AEquiv (AId x) e -> CEquiv SKIP (x ::= e)
assign_aequiv {x} {e} x_eq_e st st' = (forward, backward)
where forward : (SKIP / st \\ st') -> ((x ::= e) / st \\ st')
      forward rel = case rel of
        E_Skip => replace (t_update_same {m=st} {x=x}) (E_Ass (sym $ x_eq_e st))
                    {P=\s => (x ::= e) / st \\ s}
      backward : ((x ::= e) / st \\ st') -> (SKIP / st \\ st')
      backward rel = case rel of
        E_Ass prf => rewrite sym prf
                     in rewrite sym $ x_eq_e st
                     in rewrite t_update_same {m=st} {x=x}
                     in E_Skip

prog_a : Com
prog_a =
  WHILE (not (X <= 0)) $
    X ::= X + 1

prog_b : Com
prog_b = do
  IFB X == 0
      THEN do X ::= X + 1
              Y ::= 1
      ELSE Y ::= 0
  FI
  X ::= X - Y
  Y ::= 0

prog_c : Com
prog_c = SKIP

prog_d : Com
prog_d =
  WHILE (not (X == 0)) $
    X ::= X * Y + 1

prog_e : Com
prog_e = Y ::= 0

prog_f : Com
prog_f = do
  Y ::= X + 1
  WHILE (not (X == Y)) $
    Y ::= X + 1

prog_g : Com
prog_g = WHILE BTrue SKIP

prog_h : Com
prog_h =
  WHILE (not (X == X)) $
    X ::= X + 1

prog_i : Com
prog_i =
  WHILE (not (X == Y)) $
    X ::= Y + 1

equiv_classes : List (List Com)
equiv_classes = [ [prog_a, prog_f, prog_g]
                , [prog_b]
                , [prog_c, prog_h]
                , [prog_d]
                , [prog_e]
                , [prog_i] ]

refl_aequiv : AEquiv a a
refl_aequiv _ = Refl

sym_aequiv : AEquiv a1 a2 -> AEquiv a2 a1
sym_aequiv a1_equiv_a2 st = sym $ a1_equiv_a2 st

trans_aequiv : AEquiv a1 a2 -> AEquiv a2 a3 -> AEquiv a1 a3
trans_aequiv a1_equiv_a2 a2_equiv_a3 st = rewrite a1_equiv_a2 st
                                          in a2_equiv_a3 st

refl_bequiv : BEquiv b b
refl_bequiv _ = Refl

sym_bequiv : BEquiv b1 b2 -> BEquiv b2 b1
sym_bequiv b1_equiv_b2 st = sym $ b1_equiv_b2 st

trans_bequiv : BEquiv b1 b2 -> BEquiv b2 b3 -> BEquiv b1 b3
trans_bequiv b1_equiv_b2 b2_equiv_b3 st = rewrite b1_equiv_b2 st
                                          in b2_equiv_b3 st

refl_cequiv : CEquiv c c
refl_cequiv _ _ = (id, id)

sym_cequiv : CEquiv c1 c2 -> CEquiv c2 c1
sym_cequiv c1_equiv_c2 st st' = swap $ c1_equiv_c2 st st'

trans_cequiv : CEquiv c1 c2 -> CEquiv c2 c3 -> CEquiv c1 c3
trans_cequiv c1_equiv_c2 c2_equiv_c3 st st' =
  let (forward_c1_c2, backward_c2_c1) = c1_equiv_c2 st st'
      (forward_c2_c3, backward_c3_c2) = c2_equiv_c3 st st'
  in (forward_c2_c3 . forward_c1_c2, backward_c2_c1 . backward_c3_c2)

cAss_congruence : AEquiv a1 a2 -> CEquiv (x ::= a1) (x ::= a2)
cAss_congruence {a1} {a2} a1_equiv_a2 st st' = (forward, backward)
where forward : ((x ::= a1) / st \\ st') -> ((x ::= a2) / st \\ st')
      forward rel = case rel of
        E_Ass prf => rewrite sym prf
                     in rewrite a1_equiv_a2 st
                     in E_Ass Refl
      backward : ((x ::= a2) / st \\ st') -> ((x ::= a1) / st \\ st')
      backward rel = case rel of
        E_Ass prf => rewrite sym prf
                     in rewrite sym $ a1_equiv_a2 st
                     in E_Ass Refl

cWhile_congruence : BEquiv b1 b2 -> CEquiv c1 c2 ->
                    CEquiv (WHILE b1 c1) (WHILE b2 c2)
cWhile_congruence {b1} {b2} {c1} {c2} b1_equiv_b2 c1_equiv_c2 _ _ =
  (forward, backward)
where forward : ((WHILE b1 c1) / st \\ st') -> ((WHILE b2 c2) / st \\ st')
      forward {st} rel = case rel of
        E_WhileEnd prf => E_WhileEnd $ trans (sym $ b1_equiv_b2 st) prf
        E_WhileLoop {st1} prf rel next =>
          E_WhileLoop (trans (sym $ b1_equiv_b2 st) prf)
                      (fst (c1_equiv_c2 st st1) rel)
                      (forward {st=st1} next)
      backward : ((WHILE b2 c2) / st \\ st') -> ((WHILE b1 c1) / st \\ st')
      backward {st} rel = case rel of
        E_WhileEnd prf => E_WhileEnd $ trans (b1_equiv_b2 st) prf
        E_WhileLoop {st1} prf rel next =>
          E_WhileLoop (trans (b1_equiv_b2 st) prf)
                      (snd (c1_equiv_c2 st st1) rel)
                      (backward {st=st1} next)

cSeq_congruence : CEquiv c1 c2 -> CEquiv c3 c4 -> CEquiv (do c1; c3) (do c2; c4)
cSeq_congruence {c1} {c2} {c3} {c4} c1_equiv_c2 c3_equiv_c4 st st' =
  (forward, backward)
where forward : ((do c1; c3) / st \\ st') -> ((do c2; c4) / st \\ st')
      forward (E_Seq {st2} r1 r2) = E_Seq (fst (c1_equiv_c2 st st2) r1)
                                          (fst (c3_equiv_c4 st2 st') r2)
      backward : ((do c2; c4) / st \\ st') -> ((do c1; c3) / st \\ st')
      backward (E_Seq {st2} r3 r4) = E_Seq (snd (c1_equiv_c2 st st2) r3)
                                           (snd (c3_equiv_c4 st2 st') r4)

cIf_congruence : BEquiv b1 b2 -> CEquiv c1 c2 -> CEquiv c3 c4 ->
                 CEquiv (IFB b1 THEN c1 ELSE c3 FI) (IFB b2 THEN c2 ELSE c4 FI)
cIf_congruence {b1} {b2} {c1} {c2} {c3} {c4}
               b1_equiv_b2 c1_equiv_c2 c3_equiv_c4 st st' =
  (forward, backward)
where forward : ((IFB b1 THEN c1 ELSE c3 FI) / st \\ st') ->
                ((IFB b2 THEN c2 ELSE c4 FI) / st \\ st')
      forward (E_IfTrue prf rel) = E_IfTrue (trans (sym $ b1_equiv_b2 st) prf)
                                            (fst (c1_equiv_c2 st st') rel)
      forward (E_IfFalse prf rel) = E_IfFalse (trans (sym $ b1_equiv_b2 st) prf)
                                              (fst (c3_equiv_c4 st st') rel)
      backward : ((IFB b2 THEN c2 ELSE c4 FI) / st \\ st') ->
                 ((IFB b1 THEN c1 ELSE c3 FI) / st \\ st')
      backward (E_IfTrue prf rel) = E_IfTrue (trans (b1_equiv_b2 st) prf)
                                             (snd (c1_equiv_c2 st st') rel)
      backward (E_IfFalse prf rel) = E_IfFalse (trans (b1_equiv_b2 st) prf)
                                               (snd (c3_equiv_c4 st st') rel)

congruence_example : CEquiv
  (do X ::= 0
      IFB X == 0
          THEN Y ::= 0
          ELSE Y ::= 42
      FI)
  (do X ::= 0
      IFB X == 0
          THEN Y ::= X - X
          ELSE Y ::= 42
      FI)
congruence_example =
  cSeq_congruence refl_cequiv
                  (cIf_congruence refl_bequiv statements_equiv refl_cequiv)
where forward : ((Y ::= 0) / st \\ st') ->
                ((Y ::= X - X) / st \\ st')
      forward {st} (E_Ass prf) = E_Ass $ trans (sym $ minusZeroN (st X)) prf
      backward : ((Y ::= X - X) / st \\ st') ->
                 ((Y ::= 0) / st \\ st')
      backward {st} (E_Ass prf) = rewrite minusZeroN (st X)
                                  in rewrite prf
                                  in E_Ass Refl
      statements_equiv : CEquiv (Y ::= 0) (Y ::= X - X)
      statements_equiv _ _ = (forward, backward)

ATransSound : (atrans : AExp -> AExp) -> Type
ATransSound atrans = (a : AExp) -> AEquiv a (atrans a)

BTransSound : (btrans : BExp -> BExp) -> Type
BTransSound btrans = (b : BExp) -> BEquiv b (btrans b)

CTransSound : (ctrans : Com -> Com) -> Type
CTransSound ctrans = (c : Com) -> CEquiv c (ctrans c)
