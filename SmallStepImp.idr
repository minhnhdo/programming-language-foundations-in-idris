module SmallStepImp

import Expr
import Imp
import Maps
import SmallStepExpr

%access public export

%default total

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

syntax [t] "/" [st] "-+>" [t'] "/" [st'] = CStep (t, st) (t', st')
