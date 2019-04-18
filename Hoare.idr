module Hoare

import Imp
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

AssertImplies : (p, q : Assertion) -> Assertion
AssertImplies p q = \st => p st -> q st

infixr 8 ->>

(->>) : (p, q : Assertion) -> Assertion
(->>) = AssertImplies

infix 8 <<->>

(<<->>) : (p, q : Assertion) -> Assertion
(<<->>) p q = \st => (AssertImplies p q st, AssertImplies q p st)

HoareTriple : (p : Assertion) -> (c : Com) -> (q : Assertion) -> Type
HoareTriple p c q = (st, st' : State) -> (c / st \\ st') -> p st -> q st'

hoare_post_true : (p, q : Assertion) ->
                  (c : Com) ->
                  ((st : State) -> q st) ->
                  HoareTriple p c q
hoare_post_true _ _ _ f _ st' _ _ = f st'

hoare_pre_false : (p, q : Assertion) ->
                  (c : Com) ->
                  ((st : State) -> Not (p st)) ->
                  HoareTriple p c q
hoare_pre_false p q c f st st' rel p_st = absurd $ f st p_st

AssignSub : (x : Id) -> (a : AExp) -> (p : Assertion) -> Assertion
AssignSub x a p = \st => p (t_update x (aeval st a) st)

hoare_assign : (q : Assertion) -> (x : Id) -> (a : AExp) ->
               HoareTriple (AssignSub x a q) (x ::= a) q
hoare_assign q x a st st' rel q_st = case rel of
  E_Ass prf => rewrite sym prf in q_st

assn_sub_example : HoareTriple (AssignSub X (X + 1) (\st => LT (st X) 5))
                               (X ::= X + 1)
                               (\st => LT (st X) 5)
assn_sub_example st st' rel lte_prf =
  hoare_assign (\st => LT (st X) 5) X (X + 1) st st' rel lte_prf
