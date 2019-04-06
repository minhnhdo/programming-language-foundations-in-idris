module Imp

import Logic
import Maps

%access public export

%default total

State : Type
State = TotalMap Nat

empty_state : State
empty_state = t_empty 0

W : Id
W = MkId "W"

X : Id
X = MkId "X"

Y : Id
Y = MkId "Y"

Z : Id
Z = MkId "Z"

data AExp : Type where
  ANum : Nat -> AExp
  AId : Id -> AExp
  APlus : AExp -> AExp -> AExp
  AMinus : AExp -> AExp -> AExp
  AMult : AExp -> AExp -> AExp

data BExp : Type where
  BTrue : BExp
  BFalse : BExp
  BEq : AExp -> AExp -> BExp
  BLe : AExp -> AExp -> BExp
  BNot : BExp -> BExp
  BAnd : BExp -> BExp -> BExp

aeval : State -> AExp -> Nat
aeval _ (ANum n) = n
aeval st (AId i) = st i
aeval st (APlus a1 a2) = aeval st a1 + aeval st a2
aeval st (AMinus a1 a2) = aeval st a1 `minus` aeval st a2
aeval st (AMult a1 a2) = aeval st a1 * aeval st a2

beval : State -> BExp -> Bool
beval _ BTrue = True
beval _ BFalse = False
beval st (BEq a1 a2) = aeval st a1 == aeval st a2
beval st (BLe a1 a2) = lte (aeval st a1) (aeval st a2)
beval st (BNot b) = not $ beval st b
beval st (BAnd b1 b2) = beval st b1 && beval st b2

data Com : Type where
  CSkip : Com
  CAss : Id -> AExp -> Com
  CSeq : Com -> Com -> Com
  CIf : BExp -> Com -> Com -> Com
  CWhile : BExp -> Com -> Com

infix 5 ::=

SKIP : Com
SKIP = CSkip

(::=) : Id -> AExp -> Com
(::=) = CAss

(>>=) : Com -> (() -> Com) -> Com
(>>=) c f = CSeq c (f ())

WHILE : BExp -> Com -> Com
WHILE = CWhile

syntax IFB [c1] THEN [c2] ELSE [c3] FI = CIf c1 c2 c3

data CEval : Com -> State -> State -> Type where
  E_Skip : CEval CSkip st st
  E_Ass : aeval st a1 = n -> CEval (CAss x a1) st (t_update x n st)
  E_Seq : CEval c1 st1 st2 -> CEval c2 st2 st3 ->
          CEval (CSeq c1 c2) st1 st3
  E_IfTrue : beval st b = True -> CEval c1 st st1 ->
             CEval (CIf b c1 c2) st st1
  E_IfFalse : beval st b = False -> CEval c2 st st1 ->
              CEval (CIf b c1 c2) st st1
  E_WhileEnd : beval st b = False -> CEval (CWhile b c) st st
  E_WhileLoop : beval st b = True ->
                CEval c st st1 -> CEval (CWhile b c) st1 st2 ->
                CEval (CWhile b c) st st2

syntax [c1] "/" [st1] "\\\\" [st2] = CEval c1 st1 st2
