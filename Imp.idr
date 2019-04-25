module Imp

import Expr
import Logic
import Maps

%access public export

%default total

data Com : Type where
  CSkip : Com
  CAss : Id -> AExp -> Com
  CSeq : Com -> Com -> Com
  CIf : BExp -> Com -> Com -> Com
  CIf1 : BExp -> Com -> Com
  CWhile : BExp -> Com -> Com
  CFor : Com -> BExp -> Com -> Com -> Com
  CRepeat : Com -> BExp -> Com

infix 5 ::=

SKIP : Com
SKIP = CSkip

(::=) : Id -> AExp -> Com
(::=) = CAss

(>>=) : Com -> (() -> Com) -> Com
(>>=) c f = CSeq c (f ())

WHILE : BExp -> Com -> Com
WHILE = CWhile

syntax IFB [b] THEN [c1] ELSE [c2] FI = CIf b c1 c2

syntax IF1 [b] THEN [c] FI = CIf1 b c

syntax FOR [init] ";" [cond] ";" [updt] DO [body] DONE = CFor init cond updt body

syntax REPEAT [c] UNTIL [b] END = CRepeat c b

data CEval : Com -> State -> State -> Type where
  E_Skip : CEval CSkip st st
  E_Ass : aeval st a1 = n -> CEval (CAss x a1) st (t_update x n st)
  E_Seq : CEval c1 st1 st2 -> CEval c2 st2 st3 ->
          CEval (CSeq c1 c2) st1 st3
  E_IfTrue : beval st b = True -> CEval c1 st st1 ->
             CEval (CIf b c1 c2) st st1
  E_IfFalse : beval st b = False -> CEval c2 st st1 ->
              CEval (CIf b c1 c2) st st1
  E_If1True : beval st b = True -> CEval c st st1 ->
              CEval (CIf1 b c) st st1
  E_If1False : beval st b = False -> CEval (CIf1 b c) st st
  E_WhileEnd : beval st b = False -> CEval (CWhile b c) st st
  E_WhileLoop : beval st b = True ->
                CEval c st st1 -> CEval (CWhile b c) st1 st2 ->
                CEval (CWhile b c) st st2
  E_For : CEval init st1 st2 ->
          CEval (CWhile cond (CSeq body updt)) st2 st3 ->
          CEval (CFor init cond updt body) st1 st3
  E_Repeat : CEval c st st1 ->
             CEval (CWhile (not b) c) st1 st2 ->
             CEval (CRepeat c b) st st2

syntax [c1] "/" [st1] "\\\\" [st2] = CEval c1 st1 st2

repeat_example_1 : CEval (REPEAT do
                            X ::= 1
                            Y ::= Y + 1
                          UNTIL X == 1 END)
                         Expr.empty_state
                         (t_update Y 1 (t_update X 1 Expr.empty_state))
repeat_example_1 = E_Repeat (E_Seq (E_Ass Refl)
                                   (E_Ass Refl))
                            (E_WhileEnd Refl)

ceval_deterministic : (c / st \\ st1) -> (c / st \\ st2) -> st1 = st2
ceval_deterministic E_Skip E_Skip = Refl
ceval_deterministic (E_Ass aev1) (E_Ass aev2) =
  rewrite sym aev1
  in rewrite sym aev2
  in Refl
ceval_deterministic {st2} (E_Seq cev11 cev12) (E_Seq {c2} cev21 cev22) =
  let ih = ceval_deterministic cev11 cev21
      cev22' = replace (sym ih) cev22 {P=\x=>CEval c2 x st2}
  in ceval_deterministic cev12 cev22'
ceval_deterministic (E_IfTrue _ cev1) (E_IfTrue _ cev2) =
  ceval_deterministic cev1 cev2
ceval_deterministic (E_IfTrue prf1 _) (E_IfFalse prf2 _) =
  absurd $ replace prf1 prf2 {P=\x=>x=False}
ceval_deterministic (E_IfFalse prf1 _) (E_IfTrue prf2 _) =
  absurd $ replace prf2 prf1 {P=\x=>x=False}
ceval_deterministic (E_IfFalse _ cev1) (E_IfFalse _ cev2) =
  ceval_deterministic cev1 cev2
ceval_deterministic (E_If1True _ cc1) (E_If1True _ cc2) =
  ceval_deterministic cc1 cc2
ceval_deterministic (E_If1True prf1 _) (E_If1False prf2) =
  absurd $ trans (sym prf1) prf2
ceval_deterministic (E_If1False prf1) (E_If1True prf2 _) =
  absurd $ trans (sym prf1) prf2
ceval_deterministic (E_If1False _) (E_If1False _) = Refl
ceval_deterministic (E_WhileEnd _) (E_WhileEnd _) = Refl
ceval_deterministic (E_WhileEnd prf1) (E_WhileLoop prf2 _ _) =
  absurd $ replace prf2 prf1 {P=\x=>x=False}
ceval_deterministic (E_WhileLoop prf1 _ _) (E_WhileEnd prf2) =
  absurd $ replace prf1 prf2 {P=\x=>x=False}
ceval_deterministic {st2} (E_WhileLoop _ cev11 cev12)
                          (E_WhileLoop {b} {c} _ cev21 cev22) =
  let ih = ceval_deterministic cev11 cev21
      cev22' = replace (sym ih) cev22 {P=\x=>CEval (CWhile b c) x st2}
  in ceval_deterministic cev12 cev22'
ceval_deterministic {st2}
                    (E_For cinit1 cwhile1)
                    (E_For {cond} {body} {updt} cinit2 cwhile2) =
  let ih = ceval_deterministic cinit1 cinit2
      cwhile2' = replace {P=\x => CEval (CWhile cond (CSeq body updt)) x st2}
                         (sym ih) cwhile2
  in ceval_deterministic cwhile1 cwhile2'
ceval_deterministic (E_Repeat cc1 cwhile1) (E_Repeat {b} {c} {st2} cc2 cwhile2) =
  let ih = ceval_deterministic cc1 cc2
      cwhile2' = replace {P=\x => CEval (CWhile (not b) c) x st2}
                         (sym ih) cwhile2
  in ceval_deterministic cwhile1 cwhile2'
