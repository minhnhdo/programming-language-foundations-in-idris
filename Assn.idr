module Assn

import Expr
import Maps

%access public export

%default total

Assertion : Type
Assertion = State -> Type

namespace ExAssertions
  as1 : Assertion
  as1 = \st => st X = 3

  as2 : Assertion
  as2 = \st => LTE (st X) (st Y)

  as3 : Assertion
  as3 = \st => Either (st X = 3) (LTE (st X) (st Y))

  as4 : Assertion
  as4 = \st => (LTE (st Z * st Z) (st X), Not (LTE (S (st Z) * S (st Z)) (st X)))

  as5 : Assertion
  as5 = \st => ()

  as6 : Assertion
  as6 = \st => Void

AssertImplies : (p, q : Assertion) -> Type
AssertImplies p q = (st : State) -> p st -> q st

infixr 8 ->>

(->>) : (p, q : Assertion) -> Type
(->>) = AssertImplies

assertImpliesRefl : p ->> p
assertImpliesRefl _ p_st = p_st

assertImpliesTrans : p ->> q -> q ->> r -> p ->> r
assertImpliesTrans p_imp_q q_imp_r = \st, p_st =>
  q_imp_r st (p_imp_q st p_st)

infix 8 <<->>

(<<->>) : (p, q : Assertion) -> Type
(<<->>) p q = (AssertImplies p q, AssertImplies q p)

assertEquivRefl : p <<->> p
assertEquivRefl = (assertImpliesRefl, assertImpliesRefl)

assertEquivTrans : p <<->> q -> q <<->> r -> p <<->> r
assertEquivTrans (p_imp_q, q_imp_p) (q_imp_r, r_imp_q) =
  (assertImpliesTrans p_imp_q q_imp_r, assertImpliesTrans r_imp_q q_imp_p)

AssignSub : (x : Id) -> (a : AExp) -> (p : Assertion) -> Assertion
AssignSub x a p = \st => p (t_update x (aeval st a) st)

BAssn : (b : BExp) -> Assertion
BAssn b = \st => beval st b = True

bexp_eval_true : (b : BExp) -> (st : State) ->
                 beval st b = True -> BAssn b st
bexp_eval_true _ _ prf = prf

bexp_eval_false : (b : BExp) -> (st : State) ->
                  beval st b = False -> Not (BAssn b st)
bexp_eval_false _ _ bfalse btrue = absurd $ trans (sym bfalse) btrue
