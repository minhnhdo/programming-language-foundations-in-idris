module Dimp

import Data.Vect

import Assn
import Expr
import Hoare
import Imp
import Maps

-- %hide Assn.(->>)

%access public export

%default total

data DCom : Type where
  DCSkip : Assertion -> DCom
  DCSeq : DCom -> DCom -> DCom
  DCAss : Id -> AExp -> Assertion -> DCom
  DCIf : BExp -> Assertion -> DCom -> Assertion -> DCom -> Assertion -> DCom
  DCWhile : BExp -> Assertion -> DCom -> Assertion -> DCom
  DCPre : Assertion -> DCom -> DCom
  DCPost : DCom -> Assertion -> DCom

data Decorated : Type where
  Decorate : Assertion -> DCom -> Decorated

SKIP : Vect 1 Assertion -> DCom
SKIP [p] = DCSkip p

syntax [x] "::=" [a] "[" [p] "]" = DCAss x a p

syntax IF [b] THEN "[" [pThen] "]" [dt] ELSE "[" [pElse] "]" [df] END "[" [pIf] "]" = DCIf b pThen dt pElse df pIf

syntax WHILE [b] DO "[" [pBody] "]" [d] END "[" [pPost] "]" = DCWhile b pBody d pPost

syntax "->>" "[" [p] "]" [d] = DCPre p d

(->>) : DCom -> Vect 1 Assertion -> DCom
d ->> [p] = DCPost d p

(>>=) : DCom -> (() -> DCom) -> DCom
(>>=) c f = DCSeq c (f ())

syntax "[" [p] "]" [d] = Decorate p d

dec0 : DCom
dec0 = SKIP [const ()]

dec1 : DCom
dec1 = WHILE BTrue DO [const ()] SKIP [const ()] END [const ()]

dec_while : Decorated
dec_while =
  ([const ()]
   WHILE not (X == 0) DO
     [\st => ((), Not (st X = 0))]
     DCAss X (X - 1)
     (const ())
   END
   [\st => ((), st X = 0)] ->>
   [\st => st X = 0])

extract : DCom -> Com
extract (DCSkip _) = CSkip
extract (DCSeq d1 d2) = CSeq (extract d1) (extract d2)
extract (DCAss x e _) = CAss x e
extract (DCIf b _ dt _ df _) = CIf b (extract dt) (extract df)
extract (DCWhile b _ d _) = CWhile b (extract d)
extract (DCPre _ d) = extract d
extract (DCPost d _) = extract d

extract_dec : Decorated -> Com
extract_dec (Decorate _ d) = extract d

post : DCom -> Assertion
post (DCSkip p) = p
post (DCSeq _ d2) = post d2
post (DCAss _ _ p) = p
post (DCIf _ _ _ _ _ p) = p
post (DCWhile _ _ _ p) = p
post (DCPre _ d) = post d
post (DCPost _ p) = p

pre_dec : Decorated -> Assertion
pre_dec (Decorate p _) = p

post_dec : Decorated -> Assertion
post_dec (Decorate _ d) = post d

DecCorrect : (dec : Decorated) -> Type
DecCorrect dec = HoareTriple (pre_dec dec) (extract_dec dec) (post_dec dec)

VerificationConditions : (p : Assertion) -> (d : DCom) -> Type
VerificationConditions p (DCSkip q) = p ->> q
VerificationConditions p (DCSeq d1 d2) =
  ( VerificationConditions p d1
  , VerificationConditions (post d1) d2 )
VerificationConditions p (DCAss x a q) = p ->> AssignSub x a q
VerificationConditions p (DCIf b pt dt pf df q) =
  ( (\st => (p st, BAssn b st)) ->> pt
  , (\st => (p st, Not (BAssn b st))) ->> pf
  , post dt ->> q, post df ->> q
  , VerificationConditions pt dt
  , VerificationConditions pf df )
VerificationConditions p (DCWhile b pBody d q) =
  ( p ->> post d
  , (\st => (post d st, BAssn b st)) ->> pBody
  , (\st => (post d st, Not (BAssn b st))) ->> q
  , VerificationConditions pBody d )
VerificationConditions p (DCPre p' d) = (p ->> p', VerificationConditions p' d)
VerificationConditions p (DCPost d q) =
  (VerificationConditions p d, post d ->> q)

verification_correct : (d : DCom) -> (p : Assertion) ->
                       VerificationConditions p d ->
                       HoareTriple p (extract d) (post d)
verification_correct (DCSkip q) p vc st _ E_Skip p_st = vc st p_st
verification_correct (DCSeq d1 d2) p (vc1, vc2) st st' (E_Seq {st2} c1 c2) p_st =
  let post_d1_st2 = verification_correct d1 p vc1 st st2 c1 p_st
  in verification_correct d2 (post d1) vc2 st2 st' c2 post_d1_st2
verification_correct (DCAss x e q) p vc st _ (E_Ass prf) p_st =
  rewrite sym prf in vc st p_st
verification_correct (DCIf b pt dt pf df q) p
                     (p_pt_imp, p_pf_imp, pt_q_imp, pf_q_imp, vc_pt_dt, vc_pf_df)
                     st st' (E_IfTrue prf ct) p_st =
  let pt_st = p_pt_imp st (p_st, prf)
      post_dt_st' = verification_correct dt pt vc_pt_dt st st' ct pt_st
  in pt_q_imp st' post_dt_st'
verification_correct (DCIf b pt dt pf df q) p
                     (p_pt_imp, p_pf_imp, pt_q_imp, pf_q_imp, vc_pt_dt, vc_pf_df)
                     st st' (E_IfFalse prf cf) p_st =
  let pf_st = p_pf_imp st (p_st, bexp_eval_false b st prf)
      post_df_st' = verification_correct df pf vc_pf_df st st' cf pf_st
  in pf_q_imp st' post_df_st'
verification_correct (DCWhile b pd d q) p (p_d_imp, d_pd_imp, d_q_imp, vc_pd_d)
                     st _ (E_WhileEnd prf) p_st =
  d_q_imp st (p_d_imp st p_st, bexp_eval_false b st prf)
verification_correct w@(DCWhile b pd d q) p (p_d_imp, d_pd_imp, d_q_imp, vc_pd_d)
                     st st' (E_WhileLoop {st1} prf cbody cnext) p_st =
  let pd_st = d_pd_imp st (p_d_imp st p_st, prf)
      d_st1 = verification_correct d pd vc_pd_d st st1 cbody pd_st
  in verification_correct
       w
       (post d)
       (\_, d_st2 => d_st2, d_pd_imp, d_q_imp, vc_pd_d)
       st1
       st'
       cnext
       d_st1
verification_correct (DCPre p' d) p (imp, vc) st st' rel p_st =
  verification_correct d p' vc st st' rel (imp st p_st)
verification_correct (DCPost d q) p (vc, imp) st st' rel p_st =
  imp st' (verification_correct d p vc st st' rel p_st)

VerificationConditionsDec : Decorated -> Type
VerificationConditionsDec (Decorate p d) = VerificationConditions p d

verification_correct_dec : (dec : Decorated) -> VerificationConditionsDec dec ->
                           DecCorrect dec
verification_correct_dec (Decorate p d) vc = verification_correct d p vc
