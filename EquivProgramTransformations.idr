module EquivProgramTransformations

import Equiv
import Logic
import Imp
import Maps

%access public export

%default total

ATransSound : (atrans : AExp -> AExp) -> Type
ATransSound atrans = (a : AExp) -> AEquiv a (atrans a)

BTransSound : (btrans : BExp -> BExp) -> Type
BTransSound btrans = (b : BExp) -> BEquiv b (btrans b)

CTransSound : (ctrans : Com -> Com) -> Type
CTransSound ctrans = (c : Com) -> CEquiv c (ctrans c)

fold_constants_aexp : (a : AExp) -> AExp
fold_constants_aexp (ANum k) = ANum k
fold_constants_aexp (AId x) = AId x
fold_constants_aexp (APlus a1 a2) =
  case (fold_constants_aexp a1, fold_constants_aexp a2) of
    (ANum n1, ANum n2) => ANum (n1 + n2)
    (e1, e2) => APlus e1 e2
fold_constants_aexp (AMinus a1 a2) =
  case (fold_constants_aexp a1, fold_constants_aexp a2) of
    (ANum n1, ANum n2) => ANum (minus n1 n2)
    (e1, e2) => AMinus e1 e2
fold_constants_aexp (AMult a1 a2) =
  case (fold_constants_aexp a1, fold_constants_aexp a2) of
    (ANum n1, ANum n2) => ANum (n1 * n2)
    (e1, e2) => AMult e1 e2

fold_aexp_example_1 : fold_constants_aexp (AMult (APlus (ANum 1) (ANum 2))
                                                 (AId X))
                    = AMult (ANum 3) (AId X)
fold_aexp_example_1 = Refl

fold_aexp_example_2 : fold_constants_aexp (AMinus (AId X)
                                                  (APlus (AMult (ANum 0)
                                                                (ANum 6))
                                                         (AId Y)))
                    = AMinus (AId X) (APlus (ANum 0) (AId Y))
fold_aexp_example_2 = Refl

fold_constants_bexp : (b : BExp) -> BExp
fold_constants_bexp BTrue = BTrue
fold_constants_bexp BFalse = BFalse
fold_constants_bexp (BEq a1 a2) =
  case (fold_constants_aexp a1, fold_constants_aexp a2) of
    (ANum n1, ANum n2) => if n1 == n2 then BTrue else BFalse
    (e1, e2) => BEq e1 e2
fold_constants_bexp (BLe a1 a2) =
  case (fold_constants_aexp a1, fold_constants_aexp a2) of
    (ANum n1, ANum n2) => if lte n1 n2 then BTrue else BFalse
    (e1, e2) => BLe e1 e2
fold_constants_bexp (BNot b) =
  case fold_constants_bexp b of
    BTrue => BFalse
    BFalse => BTrue
    e => BNot e
fold_constants_bexp (BAnd b1 b2) =
  case (fold_constants_bexp b1, fold_constants_bexp b2) of
    (BTrue, BTrue) => BTrue
    (BFalse, BTrue) => BFalse
    (BTrue, BFalse) => BFalse
    (BFalse, BFalse) => BFalse
    (e1, e2) => BAnd e1 e2

fold_bexp_example_1 : fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
                    = BTrue
fold_bexp_example_1 = Refl

fold_bexp_example_2 : fold_constants_bexp (BAnd (BEq (AId X) (AId Y))
                                                (BEq (ANum 0) (AMinus (ANum 2)
                                                     (APlus (ANum 1) (ANum 1)))))
                    = BAnd (BEq (AId X) (AId Y)) BTrue
fold_bexp_example_2 = Refl

fold_constants_com : (c : Com) -> Com
fold_constants_com CSkip = CSkip
fold_constants_com (CAss x e) = x ::= fold_constants_aexp e
fold_constants_com (CSeq c1 c2) = CSeq (fold_constants_com c1)
                                       (fold_constants_com c2)
fold_constants_com (CIf b ct cf) =
  case fold_constants_bexp b of
    BTrue => fold_constants_com ct
    BFalse => fold_constants_com cf
    e => CIf e (fold_constants_com ct) (fold_constants_com cf)
fold_constants_com (CWhile b c) =
  case fold_constants_bexp b of
    BTrue => CWhile BTrue SKIP
    BFalse => SKIP
    e => CWhile e (fold_constants_com c)

fold_com_example_1 :
  fold_constants_com
    (do X ::= APlus (ANum 4) (ANum 5)
        Y ::= AMinus (AId X) (ANum 3)
        IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4))
            THEN SKIP
            ELSE Y ::= ANum 0
        FI
        IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
            THEN Y ::= ANum 0
            ELSE SKIP
        FI
        WHILE (BEq (AId Y) (ANum 0)) $
          X ::= APlus (AId X) (ANum 1))
  = (do X ::= ANum 9
        Y ::= AMinus (AId X) (ANum 3)
        IFB BEq (AMinus (AId X) (AId Y)) (ANum 6)
            THEN SKIP
            ELSE Y ::= ANum 0
        FI
        Y ::= ANum 0
        WHILE (BEq (AId Y) (ANum 0)) $
          X ::= APlus (AId X) (ANum 1))
fold_com_example_1 = Refl

fold_constants_aexp_sound :
  ATransSound EquivProgramTransformations.fold_constants_aexp
fold_constants_aexp_sound (ANum _) _ = Refl
fold_constants_aexp_sound (AId _) _ = Refl
fold_constants_aexp_sound (APlus a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (APlus a1 a2) st | ANum k
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (APlus a1 a2) st | ANum k | ANum j =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum k | AId x =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum k | APlus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum k | AMinus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum k | AMult a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AId a3 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | APlus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AMinus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AMult a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_aexp_sound (AMinus a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (AMinus a1 a2) st | ANum k
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum k | ANum j =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum k | AId x =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum k | APlus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum k | AMinus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum k | AMult a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AId x =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | APlus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AMinus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AMult a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_aexp_sound (AMult a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (AMult a1 a2) st | ANum k
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (AMult a1 a2) st | ANum k | ANum j =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum k | AId x =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum k | APlus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum k | AMinus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum k | AMult a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AId x =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | APlus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AMinus a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AMult a3 a4 =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl

fold_constants_bexp_sound :
  BTransSound EquivProgramTransformations.fold_constants_bexp
fold_constants_bexp_sound BTrue _ = Refl
fold_constants_bexp_sound BFalse _ = Refl
fold_constants_bexp_sound (BEq a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_bexp_sound (BEq a1 a2) st | ANum k
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_bexp_sound (BEq a1 a2) st | ANum k | ANum j
          with (k == j) proof eprf
            fold_constants_bexp_sound (BEq a1 a2) st | ANum k | ANum j | False =
              rewrite fold_constants_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite fold_constants_aexp_sound a2 st
              in rewrite sym a2prf
              in rewrite sym eprf
              in Refl
            fold_constants_bexp_sound (BEq a1 a2) st | ANum k | ANum j | True =
              rewrite fold_constants_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite fold_constants_aexp_sound a2 st
              in rewrite sym a2prf
              in rewrite sym eprf
              in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum k | AId x =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum k | APlus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum k | AMinus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum k | AMult a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AId x =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | APlus x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AMinus x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AMult x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_bexp_sound (BLe a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_bexp_sound (BLe a1 a2) st | ANum k
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_bexp_sound (BLe a1 a2) st | ANum k | ANum j
          with (lte k j) proof lte_prf
            fold_constants_bexp_sound (BLe a1 a2) st | ANum k | ANum j | False =
              rewrite fold_constants_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite fold_constants_aexp_sound a2 st
              in rewrite sym a2prf
              in rewrite lte_prf
              in Refl
            fold_constants_bexp_sound (BLe a1 a2) st | ANum k | ANum j | True =
              rewrite fold_constants_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite fold_constants_aexp_sound a2 st
              in rewrite sym a2prf
              in rewrite lte_prf
              in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum k | AId x =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum k | APlus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum k | AMinus a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum k | AMult a3 a4 =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AId x =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | APlus x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AMinus x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AMult x y =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_bexp_sound (BNot b) st
  with (fold_constants_bexp b) proof bprf
    fold_constants_bexp_sound (BNot b) st | BTrue =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BFalse =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BEq a1 a2 =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BLe a1 a2 =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BNot b1 =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BAnd b1 b2 =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
fold_constants_bexp_sound (BAnd b1 b2) st
  with (fold_constants_bexp b1) proof b1prf
    fold_constants_bexp_sound (BAnd b1 b2) st | BTrue
      with (fold_constants_bexp b2) proof b2prf
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BTrue =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BFalse =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BEq a1 a2 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BLe a1 a2 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BNot b =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BTrue | BAnd b3 b4 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in rewrite fold_constants_bexp_sound b2 st
          in rewrite sym b2prf
          in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BFalse
      with (fold_constants_bexp b2) proof b2prf
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BTrue =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BFalse =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BEq a1 a2 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BLe a1 a2 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BNot b =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
        fold_constants_bexp_sound (BAnd b1 b2) st | BFalse | BAnd b3 b4 =
          rewrite fold_constants_bexp_sound b1 st
          in rewrite sym b1prf
          in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BEq a1 a2 =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BLe a1 a2 =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BNot b =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BAnd b3 b4 =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl

fold_constants_com_sound :
  CTransSound EquivProgramTransformations.fold_constants_com
fold_constants_com_sound CSkip = refl_cequiv
fold_constants_com_sound (CAss x e) =
  cAss_congruence (fold_constants_aexp_sound e)
fold_constants_com_sound (CSeq c1 c2) =
  cSeq_congruence (fold_constants_com_sound c1) (fold_constants_com_sound c2)
fold_constants_com_sound (CIf b ct cf) = \st, st' =>
  (forward st st', backward st st')
where forward :
        (st, st' : State) ->
        ((CIf b ct cf) / st \\ st') ->
        ((EquivProgramTransformations.fold_constants_com (CIf b ct cf))
         / st \\ st')
      forward st st' (E_IfTrue prf rel) with (fold_constants_bexp b) proof bprf
        forward st st' (E_IfTrue prf rel) | BTrue =
          fst (fold_constants_com_sound ct st st') rel
        forward st st' (E_IfTrue prf rel) | BFalse =
          let pf = fold_constants_bexp_sound b st
          in absurd $ replace (sym bprf) (trans (sym prf) pf)
                        {P=\x => True = beval st x}
        forward st st' (E_IfTrue prf rel) | BEq a1 a2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = True}
          in E_IfTrue cond_prf $ fst (fold_constants_com_sound ct st st') rel
        forward st st' (E_IfTrue prf rel) | BLe a1 a2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = True}
          in E_IfTrue cond_prf $ fst (fold_constants_com_sound ct st st') rel
        forward st st' (E_IfTrue prf rel) | BNot b1 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = True}
          in E_IfTrue cond_prf $ fst (fold_constants_com_sound ct st st') rel
        forward st st' (E_IfTrue prf rel) | BAnd b1 b2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = True}
          in E_IfTrue cond_prf $ fst (fold_constants_com_sound ct st st') rel
      forward st st' (E_IfFalse prf rel) with (fold_constants_bexp b) proof bprf
        forward st st' (E_IfFalse prf rel) | BTrue =
          let pf = fold_constants_bexp_sound b st
          in absurd $ replace (sym bprf) (trans (sym prf) pf)
                        {P=\x => False = beval st x}
        forward st st' (E_IfFalse prf rel) | BFalse =
          fst (fold_constants_com_sound cf st st') rel
        forward st st' (E_IfFalse prf rel) | BEq a1 a2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = False}
          in E_IfFalse cond_prf $ fst (fold_constants_com_sound cf st st') rel
        forward st st' (E_IfFalse prf rel) | BLe a1 a2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = False}
          in E_IfFalse cond_prf $ fst (fold_constants_com_sound cf st st') rel
        forward st st' (E_IfFalse prf rel) | BNot b1 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = False}
          in E_IfFalse cond_prf $ fst (fold_constants_com_sound cf st st') rel
        forward st st' (E_IfFalse prf rel) | BAnd b1 b2 =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) (trans (sym pf) prf)
                           {P=\x => beval st x = False}
          in E_IfFalse cond_prf $ fst (fold_constants_com_sound cf st st') rel
      backward :
        (st, st' : State) ->
        ((EquivProgramTransformations.fold_constants_com (CIf b ct cf))
         / st \\ st') ->
        ((CIf b ct cf) / st \\ st')
      backward st st' rel with (fold_constants_bexp b) proof bprf
        backward st st' rel | BTrue =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfTrue cond_prf $ snd (fold_constants_com_sound ct st st') rel
        backward st st' rel | BFalse =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfFalse cond_prf $ snd (fold_constants_com_sound cf st st') rel
        backward st st' (E_IfTrue prf rel) | (BEq x y) =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfTrue (trans cond_prf prf) $
               snd (fold_constants_com_sound ct st st') rel
        backward st st' (E_IfFalse prf rel) | (BEq x y) =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfFalse (trans cond_prf prf) $
               snd (fold_constants_com_sound cf st st') rel
        backward st st' (E_IfTrue prf rel) | BLe x y =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfTrue (trans cond_prf prf) $
               snd (fold_constants_com_sound ct st st') rel
        backward st st' (E_IfFalse prf rel) | BLe x y =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfFalse (trans cond_prf prf) $
               snd (fold_constants_com_sound cf st st') rel
        backward st st' (E_IfTrue prf rel) | BNot x =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfTrue (trans cond_prf prf) $
               snd (fold_constants_com_sound ct st st') rel
        backward st st' (E_IfFalse prf rel) | BNot x =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfFalse (trans cond_prf prf) $
               snd (fold_constants_com_sound cf st st') rel
        backward st st' (E_IfTrue prf rel) | BAnd x y =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfTrue (trans cond_prf prf) $
               snd (fold_constants_com_sound ct st st') rel
        backward st st' (E_IfFalse prf rel) | BAnd x y =
          let pf = fold_constants_bexp_sound b st
              cond_prf = replace (sym bprf) pf
                           {P=\x => beval st b = beval st x}
          in E_IfFalse (trans cond_prf prf) $
               snd (fold_constants_com_sound cf st st') rel
fold_constants_com_sound (CWhile b c) = \st, st' =>
  (forward st st', backward st st')
where forward :
        (st, st' : State) ->
        ((CWhile b c) / st \\ st') ->
        ((EquivProgramTransformations.fold_constants_com (CWhile b c))
         / st \\ st')
      forward st st (E_WhileEnd prf) with (fold_constants_bexp b) proof bprf
        forward st st (E_WhileEnd prf) | BTrue =
          let pf = fold_constants_bexp_sound b st
          in absurd $ replace (sym bprf) (trans (sym prf) pf)
                        {P=\x => False = beval st x}
        forward st st (E_WhileEnd prf) | BFalse = E_Skip
        forward st st (E_WhileEnd prf) | BEq x y =
          let pf = fold_constants_bexp_sound b st
          in E_WhileEnd $ replace (sym bprf) (trans (sym pf) prf)
                            {P=\x => beval st x = False}
        forward st st (E_WhileEnd prf) | BLe x y =
          let pf = fold_constants_bexp_sound b st
          in E_WhileEnd $ replace (sym bprf) (trans (sym pf) prf)
                            {P=\x => beval st x = False}
        forward st st (E_WhileEnd prf) | BNot x =
          let pf = fold_constants_bexp_sound b st
          in E_WhileEnd $ replace (sym bprf) (trans (sym pf) prf)
                            {P=\x => beval st x = False}
        forward st st (E_WhileEnd prf) | BAnd x y =
          let pf = fold_constants_bexp_sound b st
          in E_WhileEnd $ replace (sym bprf) (trans (sym pf) prf)
                            {P=\x => beval st x = False}
      forward st st' (E_WhileLoop {st1} prf rel next)
        with (fold_constants_bexp b) proof bprf
          forward st st' (E_WhileLoop prf rel next) | BTrue = ?forward_rhs_2_rhs_1
          forward st st' (E_WhileLoop prf rel next) | BFalse =
            let pf = fold_constants_bexp_sound b st
            in absurd $ replace (sym bprf) (trans (sym pf) prf)
                          {P=\x => beval st x = True}
          forward st st' (E_WhileLoop {st1} prf rel next) | BEq x y =?forward_rhs_2_rhs_3
          forward st st' (E_WhileLoop {st1} prf rel next) | BLe x y = ?forward_rhs_2_rhs_4
          forward st st' (E_WhileLoop {st1} prf rel next) | BNot x = ?forward_rhs_2_rhs_5
          forward st st' (E_WhileLoop {st1} prf rel next) | BAnd x y = ?forward_rhs_2_rhs_6
      backward :
        (st, st' : State) ->
        ((EquivProgramTransformations.fold_constants_com (CWhile b c))
         / st \\ st') ->
        ((CWhile b c) / st \\ st')
      backward st st' rel = ?backward_rhs
