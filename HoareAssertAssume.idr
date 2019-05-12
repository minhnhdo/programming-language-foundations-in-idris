module HoareAssertAssume

import Assn
import Expr
import Logic
import Maps

%access public export

%default total

data Com : Type where
  CSkip : Com
  CAss : Id -> AExp -> Com
  CSeq : Com -> Com -> Com
  CIf : BExp -> Com -> Com -> Com
  CWhile : BExp -> Com -> Com
  CAssert : BExp -> Com
  CAssume : BExp -> Com

infix 5 ::=

SKIP : Com
SKIP = CSkip

(::=) : Id -> AExp -> Com
(::=) = CAss

(>>=) : Com -> (() -> Com) -> Com
(>>=) c f = CSeq c (f ())

syntax IFB [b] THEN [c1] ELSE [c2] FI = CIf b c1 c2

WHILE : BExp -> Com -> Com
WHILE = CWhile

ASSERT : BExp -> Com
ASSERT = CAssert

ASSUME : BExp -> Com
ASSUME = CAssume

data Result : Type where
  RNormal : State -> Result
  RError : Result

rNormalInjective : RNormal st1 = RNormal st2 -> st1 = st2
rNormalInjective Refl = Refl

Uninhabited (RError = RNormal st) where
  uninhabited Refl impossible

data CEval : Com -> State -> Result -> Type where
  E_Skip : CEval CSkip st (RNormal st)
  E_Ass : aeval st a1 = n -> CEval (CAss x a1) st (RNormal (t_update x n st))
  E_SeqNormal : CEval c1 st1 (RNormal st2) -> CEval c2 st2 r ->
                CEval (CSeq c1 c2) st1 r
  E_SeqError : CEval c1 st RError -> CEval (CSeq c1 c2) st RError
  E_IfTrue : beval st b = True -> CEval c1 st r -> CEval (CIf b c1 c2) st r
  E_IfFalse : beval st b = False -> CEval c2 st r -> CEval (CIf b c1 c2) st r
  E_WhileEnd : beval st b = False -> CEval (CWhile b c) st (RNormal st)
  E_WhileLoopNormal : beval st b = True ->
                      CEval c st (RNormal st1) -> CEval (CWhile b c) st1 r ->
                      CEval (CWhile b c) st r
  E_WhileLoopError : beval st b = True -> CEval c st RError ->
                     CEval (CWhile b c) st RError
  E_AssertTrue : beval st b = True -> CEval (CAssert b) st (RNormal st)
  E_AssertFalse : beval st b = False -> CEval (CAssert b) st RError
  E_Assume : beval st b = True -> CEval (CAssume b) st (RNormal st)

syntax [c1] "/" [st1] "\\\\" [st2] = CEval c1 st1 st2

HoareTriple : (p : Assertion) -> (c : Com) -> (q : Assertion) -> Type
HoareTriple p c q = (st : State) -> (r : Result) -> (c / st \\ r) -> p st ->
                    (st' : State ** (r = RNormal st', q st'))

assert_assume_differ : DPair (Assertion, BExp, Assertion)
                             (\(p, b, q) => ( HoareTriple p (ASSUME b) q
                                            , Not (HoareTriple p (ASSERT b) q) ))
assert_assume_differ = ((const (), 0 == 1, const ()) ** (assume, not_assert))
where assume : HoareTriple (const ()) (ASSUME (0 == 1)) (const ())
      assume st (RNormal _) (E_Assume _) _ = (st ** (Refl, ()))
      not_assert : Not (HoareTriple (const ()) (ASSERT (0 == 1)) (const ()))
      not_assert ht =
        let (_ ** (prf, _)) = ht empty_state RError (E_AssertFalse Refl) ()
        in absurd prf

assert_implies_assume : (p : Assertion) -> (b : BExp) -> (q : Assertion) ->
                        HoareTriple p (ASSERT b) q -> HoareTriple p (ASSUME b) q
assert_implies_assume p b q ht st (RNormal st) (E_Assume prf) p_st =
  ht st (RNormal st) (E_AssertTrue prf) p_st

hoare_assign : (q : Assertion) -> (x : Id) -> (a : AExp) ->
               HoareTriple (AssignSub x a q) (x ::= a) q
hoare_assign q x a st _ (E_Ass {n} prf) p_st =
  let q_st = replace {P=\m => q (t_update x m st)} prf p_st
  in (t_update x n st ** (Refl, q_st))

hoare_consequence_pre : (p, p', q : Assertion) -> (c : Com) ->
                        HoareTriple p' c q -> p ->> p' -> HoareTriple p c q
hoare_consequence_pre p p' q c htc imp st r rel p_st = htc st r rel (imp st p_st)

hoare_consequence_post : (p, q, q' : Assertion) -> (c : Com) ->
                         HoareTriple p c q' -> q' ->> q -> HoareTriple p c q
hoare_consequence_post p q q' c htc imp st r rel p_st =
  let (st' ** (prf, q'_st')) = htc st r rel p_st
  in (st' ** (prf, imp st' q'_st'))

hoare_seq : (p, q, r : Assertion) -> (c1, c2 : Com) ->
            HoareTriple q c2 r -> HoareTriple p c1 q ->
            HoareTriple p (do c1; c2) r
hoare_seq p q r c1 c2 htc2 htc1 st res (E_SeqNormal {st2} cc1 cc2) p_st =
  let (st2 ** (pf, q_st2)) = htc1 st (RNormal st2) cc1 p_st
      cc2' = replace {P=\x => CEval c2 x res} (rNormalInjective pf) cc2
  in htc2 st2 res cc2' q_st2
hoare_seq p q r c1 c2 htc2 htc1 st RError (E_SeqError cc1) p_st =
  let (_ ** (prf, _)) = htc1 st RError cc1 p_st
  in absurd prf

hoare_skip : (p : Assertion) -> HoareTriple p SKIP p
hoare_skip p st (RNormal st) E_Skip p_st = (st ** (Refl, p_st))

hoare_if : (p, q : Assertion) -> (b : BExp) -> (ct, cf : Com) ->
           HoareTriple (\st => (p st, BAssn b st)) ct q ->
           HoareTriple (\st => (p st, Not (BAssn b st))) cf q ->
           HoareTriple p (CIf b ct cf) q
hoare_if p q b ct cf htct htcf st r (E_IfTrue prf cct) p_st =
  htct st r cct (p_st, prf)
hoare_if p q b ct cf htct htcf st r (E_IfFalse prf ccf) p_st =
  htcf st r ccf (p_st, bexp_eval_false prf)

hoare_while : (p : Assertion) -> (b : BExp) -> (c : Com) ->
              HoareTriple (\st => (p st, BAssn b st)) c p ->
              HoareTriple p (CWhile b c) (\st => (p st, Not (BAssn b st)))
hoare_while p b c htc st (RNormal st) (E_WhileEnd prf) p_st =
  (st ** (Refl, p_st, bexp_eval_false prf))
hoare_while p b c htc st r w@(E_WhileLoopNormal {st1} prf cc cnext) p_st =
  let (st2 ** (pf, p_st2)) = htc st (RNormal st1) cc (p_st, prf)
      cnext' = assert_smaller w
                              (replace {P=\x => CEval (CWhile b c) x r}
                                       (rNormalInjective pf) cnext)
  in hoare_while p b c htc st2 r cnext' p_st2
hoare_while p b c htc st RError (E_WhileLoopError prf cc) p_st =
  let (_ ** (pf, _)) = htc st RError cc (p_st, prf)
  in absurd pf

hoare_assert : (p : Assertion) -> (b : BExp) ->
               p ->> (\st => BAssn b st) -> HoareTriple p (ASSERT b) p
hoare_assert p b _ st (RNormal st) (E_AssertTrue prf) p_st = (st ** (Refl, p_st))
hoare_assert p b imp st RError (E_AssertFalse prf) p_st =
  absurd $ trans (sym prf) (imp st p_st)

hoare_assume : (p : Assertion) -> (b : BExp) ->
               HoareTriple p (ASSUME b) (\st => (p st, BAssn b st))
hoare_assume p b st (RNormal st) (E_Assume prf) p_st = (st ** (Refl, p_st, prf))

assert_assume_example : HoareTriple (const ())
                                    (do ASSUME (X == 1)
                                        X ::= X + 1
                                        ASSERT (X == 2))
                                    (const ())
assert_assume_example =
  let ht_assm = hoare_consequence_post
                  (const ())
                  (\st => st X = 1)
                  (\st => ((), BAssn (X == 1) st))
                  (ASSUME (X == 1))
                  (hoare_assume (const ()) (X == 1))
                  (\st, (_, prf) => fst (nat_beq_iff (st X) 1) prf)
      ht_asgn = hoare_consequence_pre
                  (\st => st X = 1)
                  (\st => st X + 1 = 2)
                  (\st => st X = 2)
                  (X ::= X + 1)
                  (hoare_assign (\st => st X = 2) X (X + 1))
                  (\st, p_st => plusConstantRight (st X) 1 1 p_st)
      ht_asrt = hoare_consequence_post
                  (\st => st X = 2)
                  (const ())
                  (\st => st X = 2)
                  (ASSERT (X == 2))
                  (hoare_assert (\st => st X = 2)
                                (X == 2)
                                (\st, prf => snd (nat_beq_iff (st X) 2) prf))
                  (\_, _ => ())
  in hoare_seq (const ())
               (\st => st X = 1)
               (const ())
               (ASSUME (X == 1))
               (do X ::= X + 1
                   ASSERT (X == 2))
               (hoare_seq (\st => st X = 1)
                          (\st => st X = 2)
                          (const ())
                          (X ::= X + 1)
                          (ASSERT (X == 2))
                          ht_asrt
                          ht_asgn)
               ht_assm
