module EquivOptimize0Plus

import Equiv
import Logic
import Imp
import Maps

%access public export

%default total

optimize_0plus_aexp : AExp -> AExp
optimize_0plus_aexp (ANum n) = ANum n
optimize_0plus_aexp (AId x) = AId x
optimize_0plus_aexp (APlus (ANum Z) y) = optimize_0plus_aexp y
optimize_0plus_aexp (APlus x y) = APlus (optimize_0plus_aexp x)
                                        (optimize_0plus_aexp y)
optimize_0plus_aexp (AMinus x y) = AMinus (optimize_0plus_aexp x)
                                          (optimize_0plus_aexp y)
optimize_0plus_aexp (AMult x y) = AMult (optimize_0plus_aexp x)
                                        (optimize_0plus_aexp y)

optimize_0plus_bexp : BExp -> BExp
optimize_0plus_bexp BTrue = BTrue
optimize_0plus_bexp BFalse = BFalse
optimize_0plus_bexp (BEq a1 a2) =
  case (optimize_0plus_aexp a1, optimize_0plus_aexp a2) of
    (ANum n1, ANum n2) => if n1 == n2
                             then BTrue
                             else BFalse
    (e1, e2) => BEq e1 e2
optimize_0plus_bexp (BLe a1 a2) =
  case (optimize_0plus_aexp a1, optimize_0plus_aexp a2) of
    (ANum n1, ANum n2) => if lte n1 n2
                             then BTrue
                             else BFalse
    (e1, e2) => BLe e1 e2
optimize_0plus_bexp (BNot b) = case optimize_0plus_bexp b of
  BTrue => BFalse
  BFalse => BTrue
  e => BNot e
optimize_0plus_bexp (BAnd b1 b2) =
  case (optimize_0plus_bexp b1, optimize_0plus_bexp b2) of
    (BTrue, e2) => e2
    (BFalse, _) => BFalse
    (e1, e2) => BAnd e1 e2

optimize_0plus_com : Com -> Com
optimize_0plus_com CSkip = CSkip
optimize_0plus_com (CAss x e) = CAss x (optimize_0plus_aexp e)
optimize_0plus_com (CSeq c1 c2) = CSeq (optimize_0plus_com c1)
                                       (optimize_0plus_com c2)
optimize_0plus_com (CIf b ct cf) = case optimize_0plus_bexp b of
  BTrue => optimize_0plus_com ct
  BFalse => optimize_0plus_com cf
  e => CIf e (optimize_0plus_com ct) (optimize_0plus_com cf)
optimize_0plus_com (CWhile b c) = case optimize_0plus_bexp b of
  BTrue => CWhile BTrue CSkip
  BFalse => CSkip
  e => CWhile e (optimize_0plus_com c)

optimize_0plus_aexp_sound : ATransSound EquivOptimize0Plus.optimize_0plus_aexp
optimize_0plus_aexp_sound {a = ANum _} _ = Refl
optimize_0plus_aexp_sound {a = AId _} _ = Refl
optimize_0plus_aexp_sound {a = APlus (ANum Z) a2} st =
  optimize_0plus_aexp_sound a2 st
optimize_0plus_aexp_sound {a = APlus (ANum (S _)) a2} st =
  rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = APlus (AId _) a2} st =
  rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = APlus a1@(APlus _ _) a2} st =
  rewrite optimize_0plus_aexp_sound a1 st
  in rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = APlus a1@(AMinus _ _) a2} st =
  rewrite optimize_0plus_aexp_sound a1 st
  in rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = APlus a1@(AMult _ _) a2} st =
  rewrite optimize_0plus_aexp_sound a1 st
  in rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = AMinus a1 a2} st =
  rewrite optimize_0plus_aexp_sound a1 st
  in rewrite optimize_0plus_aexp_sound a2 st
  in Refl
optimize_0plus_aexp_sound {a = AMult a1 a2} st =
  rewrite optimize_0plus_aexp_sound a1 st
  in rewrite optimize_0plus_aexp_sound a2 st
  in Refl

optimize_0plus_bexp_sound : BTransSound EquivOptimize0Plus.optimize_0plus_bexp
optimize_0plus_bexp_sound {b = BTrue} _ = Refl
optimize_0plus_bexp_sound {b = BFalse} _ = Refl
optimize_0plus_bexp_sound {b = BEq a1 a2} st
  with (optimize_0plus_aexp a1) proof a1prf
    optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum k
      with (optimize_0plus_aexp a2) proof a2prf
        optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum k | ANum j
          with (k == j) proof eprf
            optimize_0plus_bexp_sound {b = BEq a1 a2} st
            | ANum k | ANum j | False =
              rewrite optimize_0plus_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite optimize_0plus_aexp_sound a2 st
              in rewrite sym a2prf
              in sym eprf
            optimize_0plus_bexp_sound {b = BEq a1 a2} st
            | ANum k | ANum j | True =
              rewrite optimize_0plus_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite optimize_0plus_aexp_sound a2 st
              in rewrite sym a2prf
              in sym eprf
        optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum _ | AId _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum _ | APlus _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum _ | AMinus _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BEq a1 a2} st | ANum _ | AMult _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    optimize_0plus_bexp_sound {b = BEq a1 a2} st | AId _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BEq a1 a2} st | APlus _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BEq a1 a2} st | AMinus _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BEq a1 a2} st | AMult _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
optimize_0plus_bexp_sound {b = BLe a1 a2} st
  with (optimize_0plus_aexp a1) proof a1prf
    optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum k
      with (optimize_0plus_aexp a2) proof a2prf
        optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum k | ANum j
          with (lte k j) proof eprf
            optimize_0plus_bexp_sound {b = BLe a1 a2} st
            | ANum k | ANum j | False =
              rewrite optimize_0plus_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite optimize_0plus_aexp_sound a2 st
              in rewrite sym a2prf
              in sym eprf
            optimize_0plus_bexp_sound {b = BLe a1 a2} st
            | ANum k | ANum j | True =
              rewrite optimize_0plus_aexp_sound a1 st
              in rewrite sym a1prf
              in rewrite optimize_0plus_aexp_sound a2 st
              in rewrite sym a2prf
              in sym eprf
        optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum _ | AId _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum _ | APlus _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum _ | AMinus _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
        optimize_0plus_bexp_sound {b = BLe a1 a2} st | ANum _ | AMult _ _ =
          rewrite optimize_0plus_aexp_sound a1 st
          in rewrite sym a1prf
          in rewrite optimize_0plus_aexp_sound a2 st
          in rewrite sym a2prf
          in Refl
    optimize_0plus_bexp_sound {b = BLe a1 a2} st | AId _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BLe a1 a2} st | APlus _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BLe a1 a2} st | AMinus _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
    optimize_0plus_bexp_sound {b = BLe a1 a2} st | AMult _ _ =
      rewrite optimize_0plus_aexp_sound a1 st
      in rewrite sym a1prf
      in rewrite optimize_0plus_aexp_sound a2 st
      in Refl
optimize_0plus_bexp_sound {b = BNot b} st
  with (optimize_0plus_bexp b) proof bprf
    optimize_0plus_bexp_sound {b = BNot b} st | BTrue =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
    optimize_0plus_bexp_sound {b = BNot b} st | BFalse =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
    optimize_0plus_bexp_sound {b = BNot b} st | BEq _ _ =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
    optimize_0plus_bexp_sound {b = BNot b} st | BLe _ _ =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
    optimize_0plus_bexp_sound {b = BNot b} st | BNot _ =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
    optimize_0plus_bexp_sound {b = BNot b} st | BAnd _ _ =
      rewrite optimize_0plus_bexp_sound b st
      in rewrite sym bprf
      in Refl
optimize_0plus_bexp_sound {b = BAnd b1 b2} st
  with (optimize_0plus_bexp b1) proof b1prf
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BTrue =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite optimize_0plus_bexp_sound b2 st
      in Refl
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BFalse =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in Refl
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BEq _ _ =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite optimize_0plus_bexp_sound b2 st
      in Refl
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BLe _ _ =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite optimize_0plus_bexp_sound b2 st
      in Refl
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BNot _ =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite optimize_0plus_bexp_sound b2 st
      in Refl
    optimize_0plus_bexp_sound {b = BAnd b1 b2} st | BAnd _ _ =
      rewrite optimize_0plus_bexp_sound b1 st
      in rewrite sym b1prf
      in rewrite optimize_0plus_bexp_sound b2 st
      in Refl

optimize_0plus_com_sound : CTransSound EquivOptimize0Plus.optimize_0plus_com
optimize_0plus_com_sound {c = CSkip} _ _ = (id, id)
optimize_0plus_com_sound {c = (CAss _ e)} st st' =
  let c_equiv = cAss_congruence (optimize_0plus_aexp_sound e)
  in c_equiv st st'
optimize_0plus_com_sound {c = (CSeq c1 c2)} st st' =
  let c_equiv = cSeq_congruence (optimize_0plus_com_sound c1)
                                (optimize_0plus_com_sound c2)
  in c_equiv st st'
optimize_0plus_com_sound {c = (CIf b ct cf)} st st'
  with (optimize_0plus_bexp b) proof bprf
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BTrue =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          ct_equiv = optimize_0plus_com_sound ct
      in trans_cequiv (if_true b_equiv) (optimize_0plus_com_sound ct) st st'
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BFalse =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          cf_equiv = optimize_0plus_com_sound cf
      in trans_cequiv (if_false b_equiv) (optimize_0plus_com_sound cf) st st'
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BEq _ _ =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          ct_equiv = optimize_0plus_com_sound ct
          cf_equiv = optimize_0plus_com_sound cf
          if_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in if_equiv st st'
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BLe _ _ =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          ct_equiv = optimize_0plus_com_sound ct
          cf_equiv = optimize_0plus_com_sound cf
          if_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in if_equiv st st'
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BNot _ =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          ct_equiv = optimize_0plus_com_sound ct
          cf_equiv = optimize_0plus_com_sound cf
          if_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in if_equiv st st'
    optimize_0plus_com_sound {c = (CIf b ct cf)} st st' | BAnd _ _ =
      let b_equiv = \st1 =>
            replace {P=\x => beval st1 b = beval st1 x}
                    (sym bprf) (optimize_0plus_bexp_sound b st1)
          ct_equiv = optimize_0plus_com_sound ct
          cf_equiv = optimize_0plus_com_sound cf
          if_equiv = cIf_congruence b_equiv ct_equiv cf_equiv
      in if_equiv st st'
optimize_0plus_com_sound {c = (CWhile b c)} st st'
  with (optimize_0plus_bexp b) proof bprf
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BTrue =
      let b_equiv = \st1 =>
            replace (sym bprf) (optimize_0plus_bexp_sound b st1)
              {P=\x => beval st1 b = beval st1 x}
      in while_true b_equiv st st'
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BFalse =
      let b_equiv = \st1 =>
            replace (sym bprf) (optimize_0plus_bexp_sound b st1)
              {P=\x => beval st1 b = beval st1 x}
      in while_false b_equiv st st'
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BEq _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (optimize_0plus_bexp_sound b st1)
          c_equiv = optimize_0plus_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BLe _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (optimize_0plus_bexp_sound b st1)
          c_equiv = optimize_0plus_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BNot _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (optimize_0plus_bexp_sound b st1)
          c_equiv = optimize_0plus_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
    optimize_0plus_com_sound {c = (CWhile b c)} st st' | BAnd _ _ =
      let b_equiv = \st1 =>
                         replace {P=\x => beval st1 b = beval st1 x}
                                 (sym bprf) (optimize_0plus_bexp_sound b st1)
          c_equiv = optimize_0plus_com_sound c
          while_equiv = cWhile_congruence b_equiv c_equiv
      in while_equiv st st'
