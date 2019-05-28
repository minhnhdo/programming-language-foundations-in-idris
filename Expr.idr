module Expr

import Maps

%access public export

%default total

State : Type
State = TotalMap Nat

empty_state : State
empty_state = t_empty 0

A : Id
A = MkId "A"

B : Id
B = MkId "B"

C : Id
C = MkId "C"

D : Id
D = MkId "D"

E : Id
E = MkId "E"

F : Id
F = MkId "F"

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

namespace VariableNames
  A : AExp
  A = AId A

  B : AExp
  B = AId B

  C : AExp
  C = AId C

  D : AExp
  D = AId D

  E : AExp
  E = AId E

  F : AExp
  F = AId F

  W : AExp
  W = AId W

  X : AExp
  X = AId X

  Y : AExp
  Y = AId Y

  Z : AExp
  Z = AId Z

Num AExp where
  (+) = APlus
  (*) = AMult
  fromInteger = ANum . fromIntegerNat

(-) : AExp -> AExp -> AExp
(-) = AMinus

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

(==) : AExp -> AExp -> BExp
(==) = BEq

(<=) : AExp -> AExp -> BExp
(<=) = BLe

not : BExp -> BExp
not = BNot

(&&) : BExp -> BExp -> BExp
(&&) = BAnd

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
