module ConcurrentImp

import Expr
import Logic
import Maps
import SmallStepExpr

%access public export

%default total

data Com : Type where
  CSkip : Com
  CAss : Id -> AExp -> Com
  CSeq : Com -> Com -> Com
  CIf : BExp -> Com -> Com -> Com
  CWhile : BExp -> Com -> Com
  CPar : Com -> Com -> Com

SKIP : Com
SKIP = CSkip

infix 5 ::=

(::=) : Id -> AExp -> Com
(::=) = CAss

(>>=) : Com -> (() -> Com) -> Com
(>>=) c f = CSeq c (f ())

WHILE : BExp -> Com -> Com
WHILE = CWhile

syntax IFB [b] THEN [c1] ELSE [c2] FI = CIf b c1 c2

syntax PAR [c1] WITH [c2] END = CPar c1 c2

data CStep : (Com, State) -> (Com, State) -> Type where
  CS_AssStep : AStep st a a' -> CStep (i ::= a, st) (i ::= a', st)
  CS_Ass : CStep (i ::= ANum n, st) (SKIP, t_update i n st)
  CS_SeqStep : CStep (c1, st) (c1', st') ->
               CStep ((do c1; c2), st) ((do c1'; c2), st')
  CS_SeqFinish : CStep ((do SKIP; c2), st) (c2, st)
  CS_IfStep : BStep st b b' -> CStep (CIf b c1 c2, st) (CIf b' c1 c2, st)
  CS_IfTrue : CStep (CIf BTrue c1 c2, st) (c1, st)
  CS_IfFalse : CStep (CIf BFalse c1 c2, st) (c2, st)
  CS_While : CStep (WHILE b c, st) (CIf b (do c; WHILE b c) SKIP, st)
  CS_Par1 : CStep (c1, st) (c1', st') ->
            CStep (CPar c1 c2, st) (CPar c1' c2, st')
  CS_Par2 : CStep (c2, st) (c2', st') ->
            CStep (CPar c1 c2, st) (CPar c1 c2', st')
  CS_ParDone : CStep (CPar SKIP SKIP, st) (SKIP, st)

CMultiStep : Relation (Com, State)
CMultiStep = Multi CStep

syntax [t] "/" [st] "-+>*" [t'] "/" [st'] = Multi CStep (t, st) (t', st')

par_loop : Com
par_loop =
  PAR
    Y ::= 1
  WITH
    WHILE (Y == 0) $ do
      X ::= X + 1
  END

par_loop_example_0 : (st' : State ** ( ConcurrentImp.par_loop / Expr.empty_state
                                       -+>* SKIP / st'
                                     , st' X = 2 ))
par_loop_example_0 = (updatedState ** (execution, Refl))
where updatedState : State
      updatedState = t_update Y 1 $
                     t_update X 2 $
                     t_update X 1 $
                     empty_state
      execution : CMultiStep (ConcurrentImp.par_loop, Expr.empty_state)
                             (SKIP, updatedState)
      execution = MultiStep (CS_Par2 CS_While) $
                  MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
                  MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
                  MultiStep (CS_Par2 CS_IfTrue) $
                  MultiStep (CS_Par2
                              (CS_SeqStep (CS_AssStep (AS_Plus1 AS_Id)))) $
                  MultiStep (CS_Par2 (CS_SeqStep (CS_AssStep AS_Plus))) $
                  MultiStep (CS_Par2 (CS_SeqStep CS_Ass)) $
                  MultiStep (CS_Par2 CS_SeqFinish) $
                  MultiStep (CS_Par2 CS_While) $
                  MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
                  MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
                  MultiStep (CS_Par2 CS_IfTrue) $
                  MultiStep (CS_Par2
                              (CS_SeqStep (CS_AssStep (AS_Plus1 AS_Id)))) $
                  MultiStep (CS_Par2 (CS_SeqStep (CS_AssStep AS_Plus))) $
                  MultiStep (CS_Par2 (CS_SeqStep CS_Ass)) $
                  MultiStep (CS_Par2 CS_SeqFinish) $
                  MultiStep (CS_Par1 CS_Ass) $
                  MultiStep (CS_Par2 CS_While) $
                  MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
                  MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
                  MultiStep (CS_Par2 CS_IfFalse) $
                  MultiStep CS_ParDone $
                  MultiRefl

par_body_n__Sn : (n : Nat) -> (st : State) -> (st X = n, st Y = 0) ->
                 ConcurrentImp.par_loop / st -+>*
                 ConcurrentImp.par_loop / (t_update X (S n) st)
par_body_n__Sn n st (x_prf, y_prf) =
  MultiStep (CS_Par2 CS_While) $
  MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
  rewrite y_prf in
  MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
  MultiStep (CS_Par2 CS_IfTrue) $
  MultiStep (CS_Par2
              (CS_SeqStep (CS_AssStep (AS_Plus1 AS_Id)))) $
  MultiStep (CS_Par2 (CS_SeqStep (CS_AssStep AS_Plus))) $
  MultiStep (CS_Par2 (CS_SeqStep CS_Ass)) $
  MultiStep (CS_Par2 CS_SeqFinish) $
  rewrite plusCommutative (st X) 1 in
  rewrite x_prf in
  MultiRefl

par_body_any_X_helper : (n : Nat) ->
                        (  st' : State
                        ** ( ConcurrentImp.par_loop / Expr.empty_state
                             -+>* ConcurrentImp.par_loop / st'
                           , st' X = n
                           , st' Y = 0 ))
par_body_any_X_helper Z = (empty_state ** (MultiRefl, Refl, Refl))
par_body_any_X_helper (S k) =
  let (st ** (s, x_prf, y_prf)) = par_body_any_X_helper k
  in (  t_update X (S k) st
     ** ( multi_trans s $
          MultiStep (CS_Par2 CS_While) $
          MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
          MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
          rewrite y_prf in
          MultiStep (CS_Par2 CS_IfTrue) $
          MultiStep (CS_Par2
                      (CS_SeqStep (CS_AssStep (AS_Plus1 AS_Id)))) $
          MultiStep (CS_Par2 (CS_SeqStep (CS_AssStep AS_Plus))) $
          MultiStep (CS_Par2 (CS_SeqStep CS_Ass)) $
          MultiStep (CS_Par2 CS_SeqFinish) $
          rewrite plusCommutative (st X) 1 in
          rewrite x_prf in
          MultiRefl
        , Refl
        , y_prf ))

par_body_any_X : (n : Nat) ->
                 (st' : State ** ( ConcurrentImp.par_loop / Expr.empty_state
                                   -+>* SKIP / st'
                                 , st' X = n ))
par_body_any_X n =
  let (st ** (s, x_prf, _)) = par_body_any_X_helper n
  in (t_update Y 1 st ** ( multi_trans s $
                           MultiStep (CS_Par1 CS_Ass) $
                           MultiStep (CS_Par2 CS_While) $
                           MultiStep (CS_Par2 (CS_IfStep (BS_Eq1 AS_Id))) $
                           MultiStep (CS_Par2 (CS_IfStep BS_Eq)) $
                           MultiStep (CS_Par2 CS_IfFalse) $
                           MultiStep CS_ParDone $
                           MultiRefl
                         , x_prf ))
