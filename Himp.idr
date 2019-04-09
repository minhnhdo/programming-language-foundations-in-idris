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

pXY : HCom
pXY = do HAVOC X
         HAVOC Y

pYX : HCom
pYX = do HAVOC Y
         HAVOC X


pXY_equiv_pYX : Either (HCEquiv Himp.pXY Himp.pYX)
                       (Not (HCEquiv Himp.pXY Himp.pYX))
pXY_equiv_pYX = Left $ \st, st' =>
  (forward st st', backward st st')
where x_neq_y : Not (X = Y)
      x_neq_y Refl impossible
      forward : (st, st' : State) ->
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
           Y ::= AId X

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
