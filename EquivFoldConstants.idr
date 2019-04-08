module EquivFoldConstants

import Equiv
import Logic
import Imp
import Maps

%access public export

%default total

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
    (BTrue, e2) => e2
    (BFalse, _) => BFalse
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

fold_constants_aexp_sound : ATransSound EquivFoldConstants.fold_constants_aexp
fold_constants_aexp_sound (ANum _) _ = Refl
fold_constants_aexp_sound (AId _) _ = Refl
fold_constants_aexp_sound (APlus a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (APlus a1 a2) st | ANum _
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (APlus a1 a2) st | ANum _ | ANum _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum _ | AId _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum _ | APlus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum _ | AMinus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (APlus a1 a2) st | ANum _ | AMult _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AId _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | APlus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AMinus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (APlus a1 a2) st | AMult _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_aexp_sound (AMinus a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (AMinus a1 a2) st | ANum _
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum _ | ANum _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum _ | AId _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum _ | APlus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum _ | AMinus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMinus a1 a2) st | ANum _ | AMult _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AId _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | APlus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AMinus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMinus a1 a2) st | AMult _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
fold_constants_aexp_sound (AMult a1 a2) st
  with (fold_constants_aexp a1) proof a1prf
    fold_constants_aexp_sound (AMult a1 a2) st | ANum _
      with (fold_constants_aexp a2) proof a2prf
        fold_constants_aexp_sound (AMult a1 a2) st | ANum _ | ANum _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum _ | AId _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum _ | APlus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum _ | AMinus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_aexp_sound (AMult a1 a2) st | ANum _ | AMult _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AId _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | APlus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AMinus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_aexp_sound (AMult a1 a2) st | AMult _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl

fold_constants_bexp_sound : BTransSound EquivFoldConstants.fold_constants_bexp
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
        fold_constants_bexp_sound (BEq a1 a2) st | ANum _ | AId _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum _ | APlus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum _ | AMinus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BEq a1 a2) st | ANum _ | AMult _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AId _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | APlus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AMinus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BEq a1 a2) st | AMult _ _ =
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
        fold_constants_bexp_sound (BLe a1 a2) st | ANum _ | AId _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum _ | APlus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum _ | AMinus _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        fold_constants_bexp_sound (BLe a1 a2) st | ANum _ | AMult _ _ =
          rewrite fold_constants_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite fold_constants_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AId _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | APlus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AMinus _ _ =
      rewrite fold_constants_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite fold_constants_aexp_sound a2 st
      in Refl
    fold_constants_bexp_sound (BLe a1 a2) st | AMult _ _ =
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
    fold_constants_bexp_sound (BNot b) st | BEq _ _ =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BLe _ _ =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BNot _ =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
    fold_constants_bexp_sound (BNot b) st | BAnd _ _ =
      rewrite fold_constants_bexp_sound b st
      in rewrite sym bprf
      in Refl
fold_constants_bexp_sound (BAnd b1 b2) st
  with (fold_constants_bexp b1) proof b1prf
    fold_constants_bexp_sound (BAnd b1 b2) st | BTrue =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in fold_constants_bexp_sound b2 st
    fold_constants_bexp_sound (BAnd b1 b2) st | BFalse =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BEq _ _ =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BLe _ _ =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BNot _ =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl
    fold_constants_bexp_sound (BAnd b1 b2) st | BAnd _ _ =
      rewrite fold_constants_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite fold_constants_bexp_sound b2 st
      in Refl

fold_constants_com_sound : CTransSound EquivFoldConstants.fold_constants_com
fold_constants_com_sound CSkip st st' = refl_cequiv {c=CSkip} st st'
fold_constants_com_sound (CAss x e) st st' =
  let c_equiv = cAss_congruence (fold_constants_aexp_sound e)
  in c_equiv st st'
fold_constants_com_sound (CSeq c1 c2) st st' =
  let c_equiv = cSeq_congruence (fold_constants_com_sound c1)
                                (fold_constants_com_sound c2)
  in c_equiv st st'
fold_constants_com_sound (CIf b ct cf) st st'
  with (fold_constants_bexp b) proof bprf
    fold_constants_com_sound (CIf b ct cf) st st' | BTrue =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                              (sym bprf) (fold_constants_bexp_sound b st1)
      in trans_cequiv (if_true b_equiv) (fold_constants_com_sound ct) st st'
    fold_constants_com_sound (CIf b ct cf) st st' | BFalse =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                              (sym bprf) (fold_constants_bexp_sound b st1)
      in trans_cequiv (if_false b_equiv) (fold_constants_com_sound cf) st st'
    fold_constants_com_sound (CIf b ct cf) st st' | BEq _ _ =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                        (sym bprf) (fold_constants_bexp_sound b st1)
          ct_equiv = fold_constants_com_sound ct
          cf_equiv = fold_constants_com_sound cf
          cif_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in cif_equiv st st'
    fold_constants_com_sound (CIf b ct cf) st st' | BLe _ _ =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                        (sym bprf) (fold_constants_bexp_sound b st1)
          ct_equiv = fold_constants_com_sound ct
          cf_equiv = fold_constants_com_sound cf
          cif_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in cif_equiv st st'
    fold_constants_com_sound (CIf b ct cf) st st' | BNot _ =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                        (sym bprf) (fold_constants_bexp_sound b st1)
          ct_equiv = fold_constants_com_sound ct
          cf_equiv = fold_constants_com_sound cf
          cif_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in cif_equiv st st'
    fold_constants_com_sound (CIf b ct cf) st st' | BAnd _ _ =
      let b_equiv = \st1 =>
                      replace {P=\x => beval st1 b = beval st1 x}
                        (sym bprf) (fold_constants_bexp_sound b st1)
          ct_equiv = fold_constants_com_sound ct
          cf_equiv = fold_constants_com_sound cf
          cif_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in cif_equiv st st'
fold_constants_com_sound (CWhile b c) st st'
  with (fold_constants_bexp b) proof bprf
    fold_constants_cwhile_sound (CWhile b c) st st' | BTrue =
      let b_equiv = \st1 =>
            replace (sym bprf) (fold_constants_bexp_sound b st1)
              {P=\x => beval st1 b = beval st1 x}
      in while_true b_equiv st st'
    fold_constants_cwhile_sound (CWhile b c) st st' | BFalse =
      let b_equiv = \st1 =>
            replace (sym bprf) (fold_constants_bexp_sound b st1)
              {P=\x => beval st1 b = beval st1 x}
      in while_false b_equiv st st'
    fold_constants_cwhile_sound (CWhile b c) st st' | BEq _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (fold_constants_bexp_sound b st1)
          c_equiv = fold_constants_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    fold_constants_cwhile_sound (CWhile b c) st st' | BLe _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (fold_constants_bexp_sound b st1)
          c_equiv = fold_constants_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    fold_constants_cwhile_sound (CWhile b c) st st' | BNot _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (fold_constants_bexp_sound b st1)
          c_equiv = fold_constants_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    fold_constants_cwhile_sound (CWhile b c) st st' | BAnd _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (fold_constants_bexp_sound b st1)
          c_equiv = fold_constants_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
