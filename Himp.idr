module Himp

import Imp
import Logic
import Maps

%access public export

%default total

data HCom : Type where
  HCSkip : HCom
  HCAss : (x : Id) -> (a : AExp) -> HCom
  HCSeq : (c1 : HCom) -> (c2 : HCom) -> HCom
  HCIf : (b : BExp) -> (ct : HCom) -> (cf : HCom) -> HCom
  HCWhile : (b : BExp) -> (c : HCom) -> HCom
  HCHavoc : (x : Id) -> HCom

SKIP : HCom
SKIP = HCSkip

(::=) : Id -> AExp -> HCom
(::=) = HCAss

(>>=) : HCom -> (() -> HCom) -> HCom
(>>=) c f = HCSeq c (f ())

WHILE : BExp -> HCom -> HCom
WHILE = HCWhile

syntax IFB [b] THEN [ct] ELSE [cf] FI = HCIf b ct cf

HAVOC : Id -> HCom
HAVOC = HCHavoc

data HCEval : HCom -> State -> State -> Type where
  E_Skip : HCEval HCSkip st st
  E_Ass : aeval st a1 = n -> HCEval (HCAss x a1) st (t_update x n st)
  E_Seq : HCEval c1 st1 st2 -> HCEval c2 st2 st3 ->
          HCEval (HCSeq c1 c2) st1 st3
  E_IfTrue : beval st b = True -> HCEval c1 st st1 ->
             HCEval (HCIf b c1 c2) st st1
  E_IfFalse : beval st b = False -> HCEval c2 st st1 ->
              HCEval (HCIf b c1 c2) st st1
  E_WhileEnd : beval st b = False -> HCEval (HCWhile b c) st st
  E_WhileLoop : beval st b = True ->
                HCEval c st st1 -> HCEval (HCWhile b c) st1 st2 ->
                HCEval (HCWhile b c) st st2
  E_Havoc : (n : Nat) -> HCEval (HCHavoc x) st (t_update x n st)

syntax [c1] "/" [st1] "\\\\" [st2] = HCEval c1 st1 st2

havoc_example_1 : (HAVOC X) / Imp.empty_state \\ (t_update X 0 Imp.empty_state)
havoc_example_1 = E_Havoc 0

havoc_example_2 : (do SKIP; HAVOC Z)
                  / Imp.empty_state \\ (t_update Z 42 Imp.empty_state)
havoc_example_2 = E_Seq E_Skip (E_Havoc 42)

HCEquiv : (c1, c2 : HCom) -> Type
HCEquiv c1 c2 = (st, st' : State) -> ((c1 / st \\ st') ↔ (c2 / st \\ st'))

havoc_property : Not (x = y) -> st x = n -> ((HAVOC y) / st \\ st') -> st' x = n
havoc_property contra prf (E_Havoc _) =
  rewrite snd beq_id_false_iff $ neqSym contra
  in prf

pXY : HCom
pXY = do HAVOC X
         HAVOC Y

pYX : HCom
pYX = do HAVOC Y
         HAVOC X

x_neq_y : Not (Imp.X = Imp.Y)
x_neq_y Refl impossible

pXY_equiv_pYX : Either (HCEquiv Himp.pXY Himp.pYX)
                       (Not (HCEquiv Himp.pXY Himp.pYX))
pXY_equiv_pYX = Left $ \st, st' =>
  (forward st st', backward st st')
where forward : (st, st' : State) ->
                (Himp.pXY / st \\ st') -> (Himp.pYX / st \\ st')
      forward st _ (E_Seq (E_Havoc n) (E_Havoc m)) =
        rewrite t_update_permute {x1=Y} {v1=m} {x2=X} {v2=n} {m=st}
                                 x_neq_y
        in E_Seq (E_Havoc m) (E_Havoc n)
      backward : (st, st' : State) ->
                 (Himp.pYX / st \\ st') -> (Himp.pXY / st \\ st')
      backward st _ (E_Seq (E_Havoc n) (E_Havoc m)) =
        rewrite t_update_permute {x1=X} {v1=m} {x2=Y} {v2=n} {m=st}
                                 (neqSym x_neq_y)
        in E_Seq (E_Havoc m) (E_Havoc n)

ptwice : HCom
ptwice = do HAVOC X
            HAVOC Y

pcopy : HCom
pcopy = do HAVOC X
           Y ::= X

ptwice_inequiv_pcopy : Either (HCEquiv Himp.ptwice Himp.pcopy)
                              (Not (HCEquiv Himp.ptwice Himp.pcopy))
ptwice_inequiv_pcopy = Right $ \equiv =>
  let st' = t_update Y 1 $ t_update X 0 empty_state
  in case fst (equiv empty_state st') (E_Seq (E_Havoc 0) (E_Havoc 1)) of
       E_Seq _ E_Skip impossible
       E_Seq _ (E_Ass _) impossible
       E_Seq _ (E_Seq _ _) impossible
       E_Seq _ (E_IfTrue _ _) impossible
       E_Seq _ (E_IfFalse _ _) impossible
       E_Seq _ (E_WhileEnd _) impossible
       E_Seq _ (E_WhileLoop _ _ _) impossible
       E_Seq _ (E_Havoc _) impossible

p1 : HCom
p1 = WHILE (not (X == 0)) $ do
       HAVOC Y
       X ::= X + 1

p2 : HCom
p2 = WHILE (not (X == 0)) $
       SKIP

p1_may_diverge : Not (st X = 0) -> Not (Himp.p1 / st \\ st')
p1_may_diverge {st'} contra (E_WhileEnd prf) with (st' X)
  p1_may_diverge {st'} contra (E_WhileEnd prf) | Z = contra Refl
  p1_may_diverge {st'} contra (E_WhileEnd prf) | S _ = absurd prf
p1_may_diverge contra (E_WhileLoop _ (E_Seq {st2} _ (E_Ass prf)) next) =
  let h_prf = sym $ trans (plusCommutative 1 (st2 X)) prf
  in p1_may_diverge {st=t_update Imp.X _ _}
                    (n_eq_succ__n_neq_0 {k=st2 X} h_prf) next

p2_may_diverge : Not (st X = 0) -> Not (Himp.p2 / st \\ st')
p2_may_diverge {st'} contra (E_WhileEnd prf) =
  let st_X_beq_0 = trans (sym (notInvolutive (st' X == 0)))
                         (cong {f=Bool.not} prf)
  in contra (fst (nat_beq_iff {n=st' X} {m=0}) st_X_beq_0)
p2_may_diverge contra (E_WhileLoop _ E_Skip next) = p2_may_diverge contra next

p1_p2_equiv : HCEquiv Himp.p1 Himp.p2
p1_p2_equiv st st' = (forward, backward)
where forward : (Himp.p1 / st \\ st') -> (Himp.p2 / st \\ st')
      forward rel = case rel of
        E_WhileEnd prf => E_WhileEnd prf
        E_WhileLoop prf _ _ =>
          let st_X_neq_0 = fst (nat_nbeq_iff {n=st X} {m=0})
                               (trans (sym (notInvolutive (st X == 0)))
                                      (cong {f=Bool.not} prf))
          in absurd $ p1_may_diverge st_X_neq_0 rel
      backward : (Himp.p2 / st \\ st') -> (Himp.p1 / st \\ st')
      backward rel = case rel of
        E_WhileEnd prf => E_WhileEnd prf
        E_WhileLoop prf _ _ =>
          let st_X_neq_0 = fst (nat_nbeq_iff {n=st X} {m=0})
                               (trans (sym (notInvolutive (st X == 0)))
                                      (cong {f=Bool.not} prf))
          in absurd $ p2_may_diverge st_X_neq_0 rel

p3 : HCom
p3 = do Z ::= 1
        WHILE (not (X == 0)) $ do
          HAVOC X
          HAVOC Z

p4 : HCom
p4 = do X ::= 0
        Z ::= 1

p3_p4_inequiv : Not (HCEquiv Himp.p3 Himp.p4)
p3_p4_inequiv equiv =
  let st = t_update X 1 empty_state
      st' = t_update Z 2 $ t_update X 0 $ t_update Z 1 st
  in case fst (equiv st st')
              (E_Seq (E_Ass Refl)
                     (E_WhileLoop Refl
                                  (E_Seq (E_Havoc 0) (E_Havoc 2))
                                  (E_WhileEnd Refl))) of
       (E_Seq (E_Ass _) E_Skip) impossible
       (E_Seq (E_Ass _) (E_Ass _)) impossible
       (E_Seq (E_Ass _) (E_Seq _ _)) impossible
       (E_Seq (E_Ass _) (E_IfTrue _ _)) impossible
       (E_Seq (E_Ass _) (E_IfFalse _ _)) impossible
       (E_Seq (E_Ass _) (E_WhileEnd _)) impossible
       (E_Seq (E_Ass _) (E_WhileLoop _ _ _)) impossible
       (E_Seq (E_Ass _) (E_Havoc _)) impossible

p5 : HCom
p5 = WHILE (not (X == 1)) $
       HAVOC X

p6 : HCom
p6 = X ::= 1

overwriting_write : ((x ::= ANum n) / (t_update x v st) \\ st') ->
                    ((x ::= ANum n) / st \\ st')
overwriting_write {x} {n} {v} {st} (E_Ass prf) =
  rewrite sym prf
  in rewrite t_update_shadow {x=x} {v2=n} {v1=v} {m=st}
  in E_Ass {n=n} Refl

p5_p6_equiv : HCEquiv Himp.p5 Himp.p6
p5_p6_equiv st st' = (forward st st', backward st st')
where forward : (st, st' : State) ->
                (Himp.p5 / st \\ st') -> (Himp.p6 / st \\ st')
      forward st st' rel = case rel of
        E_WhileEnd prf =>
          let st_X_eq_1 = fst (nat_beq_iff {n=st X} {m=1}) $
                          trans (sym (notInvolutive (st X == 1)))
                                (cong {f=Bool.not} prf)
              st_prf = replace {P=\v => t_update X v st = st}
                               st_X_eq_1 (t_update_same {m=st} {x=X})
          in replace {P=\x => HCEval (HCAss X 1) st x}
                     st_prf (Himp.E_Ass Refl)
        E_WhileLoop {st1 = (t_update Imp.X n st)} _ (E_Havoc n) next =>
          overwriting_write $ forward (t_update X n st) st' next
      backward : (st, st' : State) ->
                 (Himp.p6 / st \\ st') -> (Himp.p5 / st \\ st')
      backward st st' rel with (st X) proof st_X_prf
        backward st st' rel | Z = case rel of
          E_Ass prf => let pf = cong {f=Bool.not . (==1)} $ sym st_X_prf
                       in rewrite sym prf
                       in E_WhileLoop pf (E_Havoc 1) (E_WhileEnd Refl)
        backward st st' rel | S Z = case rel of
          E_Ass prf => let pf = cong {f=Bool.not . (==1)} $ sym st_X_prf
                       in rewrite sym prf
                       in rewrite st_X_prf
                       in rewrite t_update_same {m=st} {x=X}
                       in rewrite sym st_X_prf
                       in E_WhileEnd pf
        backward st st' rel | S (S k) = case rel of
          E_Ass prf => let pf = cong {f=Bool.not . (== 1)} $ sym st_X_prf
                       in rewrite sym prf
                       in E_WhileLoop pf (E_Havoc 1) (E_WhileEnd Refl)
