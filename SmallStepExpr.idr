module SmallStepExpr

import Expr
import Maps

%access public export

%default total

data AVal : AExp -> Type where
  AV_Num : (n : Nat) -> AVal (ANum n)

data AStep : State -> AExp -> AExp -> Type where
  AS_Id : AStep st (AId i) (ANum (st i))
  AS_Plus1 : AStep st a1 a1' -> AStep st (APlus a1 a2) (APlus a1' a2)
  AS_Plus2 : AVal v1 -> AStep st a2 a2' -> AStep st (APlus v1 a2) (APlus v1 a2')
  AS_Plus : AStep st (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))
  AS_Minus1 : AStep st a1 a1' -> AStep st (AMinus a1 a2) (AMinus a1' a2)
  AS_Minus2 : AVal v1 -> AStep st a2 a2' ->
              AStep st (AMinus v1 a2) (AMinus v1 a2')
  AS_Minus : AStep st (AMinus (ANum n1) (ANum n2)) (ANum (minus n1 n2))
  AS_Mult1 : AStep st a1 a1' -> AStep st (AMult a1 a2) (AMult a1' a2)
  AS_Mult2 : AVal v1 -> AStep st a2 a2' -> AStep st (AMult v1 a2) (AMult v1 a2')
  AS_Mult : AStep st (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2))

syntax [t] "/" [st] "-+>a" [t'] = AStep st t t'

data BStep : State -> BExp -> BExp -> Type where
  BS_Eq1 : AStep st a1 a1' -> BStep st (BEq a1 a2) (BEq a1' a2)
  BS_Eq2 : AVal v1 -> AStep st a2 a2' -> BStep st (BEq v1 a2) (BEq v1 a2')
  BS_Eq : BStep st
                (BEq (ANum n1) (ANum n2))
                (if n1 == n2 then BTrue else BFalse)
  BS_Le1 : AStep st a1 a1' -> BStep st (BLe a1 a2) (BLe a1' a2)
  BS_Le2 : AVal v1 -> AStep st a2 a2' -> BStep st (BLe v1 a2) (BLe v1 a2')
  BS_Le : BStep st
                (BLe (ANum n1) (ANum n2))
                (if lte n1 n2 then BTrue else BFalse)
  BS_NotStep : BStep st b b' -> BStep st (BNot b) (BNot b')
  BS_NotTrue : BStep st (BNot BTrue) BFalse
  BS_NotFalse : BStep st (BNot BFalse) BTrue
  BS_AndStep : BStep st b1 b1' -> BStep st (BAnd b1 b2) (BAnd b1' b2)
  BS_AndTrueStep : BStep st b2 b2' -> BStep st (BAnd BTrue b2) (BAnd BTrue b2')
  BS_AndTrueTrue : BStep st (BAnd BTrue BTrue) BTrue
  BS_AndTrueFalse : BStep st (BAnd BTrue BFalse) BFalse
  BS_AndFalse : BStep st (BAnd BFalse b2) BFalse

syntax [t] "/" [st] "-+>b" [t'] = BStep st t t'
