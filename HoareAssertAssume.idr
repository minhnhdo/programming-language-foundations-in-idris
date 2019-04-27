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
