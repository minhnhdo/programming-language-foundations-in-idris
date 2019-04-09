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

Num AExp where
  (+) = APlus
  (*) = AMult
  fromInteger = ANum . fromIntegerNat

Uninhabited (ANum _ = AId _) where
  uninhabited Refl impossible

Uninhabited (ANum _ = APlus _ _) where
  uninhabited Refl impossible

Uninhabited (ANum _ = AMinus _ _) where
  uninhabited Refl impossible

Uninhabited (ANum _ = AMult _ _) where
  uninhabited Refl impossible

Uninhabited (APlus _ _ = ANum _) where
  uninhabited Refl impossible

Uninhabited (AMinus _ _ = ANum _) where
  uninhabited Refl impossible

Uninhabited (AMult _ _ = ANum _) where
  uninhabited Refl impossible

Uninhabited (AId _ = ANum _) where
  uninhabited Refl impossible

Uninhabited (AId _ = APlus _ _) where
  uninhabited Refl impossible

Uninhabited (AId _ = AMinus _ _) where
  uninhabited Refl impossible

Uninhabited (AId _ = AMult _ _) where
  uninhabited Refl impossible

Uninhabited (APlus _ _ = AId _) where
  uninhabited Refl impossible

Uninhabited (AMinus _ _ = AId _) where
  uninhabited Refl impossible

Uninhabited (AMult _ _ = AId _) where
  uninhabited Refl impossible

aNumInjective : ANum n = ANum m -> n = m
aNumInjective Refl = Refl

aIdInjective : AId x = AId y -> x = y
aIdInjective Refl = Refl

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

ceval_deterministic : (c / st \\ st1) -> (c / st \\ st2) -> st1 = st2
ceval_deterministic E_Skip E_Skip = Refl
ceval_deterministic (E_Ass aev1) (E_Ass aev2) =
  rewrite sym aev1
  in rewrite sym aev2
  in Refl
ceval_deterministic {st2} (E_Seq cev11 cev12) (E_Seq {c2} cev21 cev22) =
  let ih = ceval_deterministic cev11 cev21
      cev22' = replace (sym ih) cev22 {P=\x=>CEval c2 x st2}
  in ceval_deterministic cev12 cev22'
ceval_deterministic (E_IfTrue _ cev1) (E_IfTrue _ cev2) =
  ceval_deterministic cev1 cev2
ceval_deterministic (E_IfTrue prf1 _) (E_IfFalse prf2 _) =
  absurd $ replace prf1 prf2 {P=\x=>x=False}
ceval_deterministic (E_IfFalse prf1 _) (E_IfTrue prf2 _) =
  absurd $ replace prf2 prf1 {P=\x=>x=False}
ceval_deterministic (E_IfFalse _ cev1) (E_IfFalse _ cev2) =
  ceval_deterministic cev1 cev2
ceval_deterministic (E_WhileEnd _) (E_WhileEnd _) = Refl
ceval_deterministic (E_WhileEnd prf1) (E_WhileLoop prf2 _ _) =
  absurd $ replace prf2 prf1 {P=\x=>x=False}
ceval_deterministic (E_WhileLoop prf1 _ _) (E_WhileEnd prf2) =
  absurd $ replace prf1 prf2 {P=\x=>x=False}
ceval_deterministic {st2} (E_WhileLoop _ cev11 cev12)
                          (E_WhileLoop {b} {c} _ cev21 cev22) =
  let ih = ceval_deterministic cev11 cev21
      cev22' = replace (sym ih) cev22 {P=\x=>CEval (CWhile b c) x st2}
  in ceval_deterministic cev12 cev22'
