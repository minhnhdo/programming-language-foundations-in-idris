module Hoare

import Imp
import Logic
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

infix 8 <<->>

(<<->>) : (p, q : Assertion) -> Type
(<<->>) p q = (AssertImplies p q, AssertImplies q p)

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
assn_sub_example = hoare_assign (\st => LT (st X) 5) X (X + 1)

hoare_assign_fwd : (m : Nat) -> (a : AExp) -> (p : Assertion) ->
                   HoareTriple (\st => (p st, st X = m))
                               (X ::= a)
                               (\st => ( p (t_update X m st)
                                       , st X = aeval (t_update X m st) a ))
hoare_assign_fwd m a p st _ (E_Ass {n} prf1) (p_st, prf2) =
  rewrite sym prf2
  in rewrite trans (t_update_shadow {x=X} {v2=st X} {v1=n} {m=st})
                   (t_update_same {x=X} {m=st})
  in (p_st, sym prf1)

hoare_assign_fwd_exists : (a : AExp) -> (p : Assertion) ->
                          HoareTriple
                            (\st => p st)
                            (X ::= a)
                            (\st => (m ** ( p (t_update X m st)
                                          , st X = aeval (t_update X m st) a )))
hoare_assign_fwd_exists a p st st' rel p_st with (st X) proof prf2
  hoare_assign_fwd_exists a p st st' rel p_st | m =
    (m ** hoare_assign_fwd m a p st st' rel (p_st, sym prf2))

hoare_consequence_pre : (p, p', q : Assertion) -> (c : Com) ->
                        HoareTriple p' c q ->
                        (p ->> p') ->
                        HoareTriple p c q
hoare_consequence_pre p p' q c ht imp st st' rel p_st =
  ht st st' rel (imp st p_st)

hoare_consequence_post : (p, q, q' : Assertion) -> (c : Com) ->
                         HoareTriple p c q' ->
                         (q' ->> q) ->
                         HoareTriple p c q
hoare_consequence_post p q q' c ht imp st st' rel p_st =
  imp st' (ht st st' rel p_st)

hoare_assign_example_1 : HoareTriple (const ()) (X ::= 1) (\st => st X = 1)
hoare_assign_example_1 =
  hoare_consequence_post (const ())
                         (\st => st X = 1)
                         (\st => (m : Nat ** ((), st X = 1)))
                         (X ::= 1)
                         (hoare_assign_fwd_exists 1 (const ()))
                         (\_, (_ ** (_, prf)) => prf)

hoare_assign_example_2 : HoareTriple (\st => LT (st X) 4)
                                     (X ::= X + 1)
                                     (\st => LT (st X) 5)
hoare_assign_example_2 =
  hoare_consequence_pre (\st => LT (st X) 4)
                        (\st => LT (st X + 1) 5)
                        (\st => LT (st X) 5)
                        (X ::= X + 1)
                        (hoare_assign (\st => LT (st X) 5) X (X + 1))
                        (\st, p_st => replace {P=\x => LT x 5}
                                              (sym (plusCommutative (st X) 1))
                                              (LTESucc p_st))

hoare_consequence : (p, p', q, q' : Assertion) -> (c : Com) ->
                    HoareTriple p' c q' ->
                    p ->> p' ->
                    q' ->> q ->
                    HoareTriple p c q
hoare_consequence p p' q q' c ht p_imp_p' q'_imp_q =
  let ht' = hoare_consequence_pre p p' q' c ht p_imp_p'
  in hoare_consequence_post p q q' c ht' q'_imp_q

hoare_assign_example_5 : HoareTriple (\st => LTE (st X + 1) 5)
                                     (X ::= X + 1)
                                     (\st => LTE (st X) 5)
hoare_assign_example_5 = hoare_assign (\st => LTE (st X) 5) X (X + 1)

hoare_assign_example_6 : HoareTriple (\st => (LTE 0 3, LTE 3 5))
                                     (X ::= 3)
                                     (\st => (LTE 0 (st X), LTE (st X) 5))
hoare_assign_example_6 = hoare_assign (\st => (LTE 0 (st X), LTE (st X) 5)) X 3

hoare_skip : (p : Assertion) -> HoareTriple p SKIP p
hoare_skip _ _ _ E_Skip p_st = p_st

hoare_seq : (p, q, r : Assertion) -> (c1, c2 : Com) ->
            HoareTriple q c2 r ->
            HoareTriple p c1 q ->
            HoareTriple p (do c1; c2) r
hoare_seq p q r c1 c2 ht2 ht1 st st' (E_Seq {st2} cc1 cc2) p_st =
  let q_st2 = ht1 st st2 cc1 p_st
  in ht2 st2 st' cc2 q_st2

hoare_assign_example_3 : (a : AExp) -> (n : Nat) ->
                         HoareTriple (\st => aeval st a = n)
                                     (do X ::= a; SKIP)
                                     (\st => st X = n)
hoare_assign_example_3 a n =
  let hta = hoare_assign_fwd_exists a (\st => aeval st a = n)
      hta' = hoare_consequence_post
               (\st => aeval st a = n)
               (\st => st X = n)
               (\st => (m : Nat ** ( aeval (t_update X m st) a = n
                                   , st X = aeval (t_update X m st) a )))
               (X ::= a)
               hta
               (\_, (_ ** (aeval_eq_n, st_X_eq_aeval)) =>
                  trans st_X_eq_aeval aeval_eq_n)
      hts = hoare_skip (\st => st X = n)
  in hoare_seq (\st => aeval st a = n)
               (\st => st X = n)
               (\st => st X = n)
               (X ::= a)
               SKIP
               hts
               hta'

hoare_assign_example_4 : HoareTriple (const ())
                                     (do X ::= 1; Y ::= 2)
                                     (\st => (st X = 1, st Y = 2))
hoare_assign_example_4 =
  let htx = hoare_consequence_post
              (const ())
              (\st => st X = 1)
              (\st => (m : Nat ** ((), st X = 1)))
              (X ::= 1)
              (hoare_assign_fwd_exists 1 (const ()))
              (\_, (_ ** (_, q_st)) => q_st)
      hty = hoare_consequence_pre
              (\st => st X = 1)
              (AssignSub Y 2 (\st => (st X = 1, st Y = 2)))
              (\st => (st X = 1, st Y = 2))
              (Y ::= 2)
              (hoare_assign (\st => (st X = 1, st Y = 2)) Y 2)
              (\_, p_st => (p_st, Refl))
  in hoare_seq (const ())
               (\st => st X = 1)
               (\st => (st X = 1, st Y = 2))
               (X ::= 1)
               (Y ::= 2)
               hty
               htx

swap_program : Com
swap_program = do Z ::= X
                  X ::= Y
                  Y ::= Z

swap_exercise : HoareTriple (\st => LTE (st X) (st Y))
                            Hoare.swap_program
                            (\st => LTE (st Y) (st X))
swap_exercise =
  let htz = hoare_consequence_pre
              (\st => LTE (st X) (st Y))
              (AssignSub Z X (\st => LTE (st Z) (st Y)))
              (\st => LTE (st Z) (st Y))
              (Z ::= X)
              (hoare_assign (\st => LTE (st Z) (st Y)) Z X)
              (\_, p_st => p_st)
      htx = hoare_consequence_pre (\st => LTE (st Z) (st Y))
                                  (AssignSub X Y (\st => LTE (st Z) (st X)))
                                  (\st => LTE (st Z) (st X))
                                  (X ::= Y)
                                  (hoare_assign (\st => LTE (st Z) (st X)) X Y)
                                  (\_, p_st => p_st)
      hty = hoare_consequence_pre (\st => LTE (st Z) (st X))
                                  (AssignSub Y Z (\st => LTE (st Y) (st X)))
                                  (\st => LTE (st Y) (st X))
                                  (Y ::= Z)
                                  (hoare_assign (\st => LTE (st Y) (st X)) Y Z)
                                  (\_, p_st => p_st)
      htxy = hoare_seq (\st => LTE (st Z) (st Y))
                       (\st => LTE (st Z) (st X))
                       (\st => LTE (st Y) (st X))
                       (X ::= Y)
                       (Y ::= Z)
                       hty
                       htx
  in hoare_seq (\st => LTE (st X) (st Y))
               (\st => LTE (st Z) (st Y))
               (\st => LTE (st Y) (st X))
               (Z ::= X)
               (do X ::= Y; Y ::= Z)
               htxy
               htz

BAssn : (b : BExp) -> Assertion
BAssn b = \st => beval st b = True

bexp_eval_true : (b : BExp) -> (st : State) ->
                 beval st b = True -> BAssn b st
bexp_eval_true _ _ prf = prf

bexp_eval_false : (b : BExp) -> (st : State) ->
                  beval st b = False ->
                  Not (BAssn b st)
bexp_eval_false _ _ bfalse btrue = absurd $ trans (sym bfalse) btrue

hoare_if : (p, q : Assertion) -> (b : BExp) -> (c1, c2 : Com) ->
           HoareTriple (\st => (p st, BAssn b st)) c1 q ->
           HoareTriple (\st => (p st, Not (BAssn b st))) c2 q ->
           HoareTriple p (CIf b c1 c2) q
hoare_if p q b c1 c2 ht1 ht2 st st' (E_IfTrue prf cc1) p_st =
  ht1 st st' cc1 (p_st, prf)
hoare_if p q b c1 c2 ht1 ht2 st st' (E_IfFalse prf cc2) p_st =
  ht2 st st' cc2 (p_st, bexp_eval_false b st prf)

if_example : HoareTriple (const ())
                         (CIf (X == 0) (Y ::= 2) (Y ::= X + 1))
                         (\st => LTE (st X) (st Y))
if_example =
  let htt = hoare_consequence
              (\st => ((), BAssn (X == 0) st))
              (AssignSub Y 2 (\st => (LTE (st X) (st Y), BAssn (X == 0) st)))
              (\st => LTE (st X) (st Y))
              (\st => (LTE (st X) (st Y), BAssn (X == 0) st))
              (Y ::= 2)
              (hoare_assign (\st => (LTE (st X) (st Y), BAssn (X == 0) st)) Y 2)
              (\st, (_, p_st) => ( replace {P=\x => LTE x 2}
                                           (sym (fst (nat_beq_iff {n=st X} {m=0})
                                                p_st))
                                           LTEZero
                                 , p_st ))
              (\_, (q_st, _) => q_st)
      htf = hoare_consequence
              (\st => ((), Not (BAssn (X == 0) st)))
              (AssignSub Y (X + 1) (\st => ( LTE (st X) (st Y)
                                           , Not (BAssn (X == 0) st) )))
              (\st => LTE (st X) (st Y))
              (\st => (LTE (st X) (st Y), Not (BAssn (X == 0) st)))
              (Y ::= X + 1)
              (hoare_assign (\st => ( LTE (st X) (st Y)
                                    , Not (BAssn (X == 0) st) ))
                            Y
                            (X + 1))
              (\st, (_, p_st) => (lteAddRight (st X), p_st))
              (\_, (q_st, _) => q_st)
  in hoare_if (const ())
              (\st => LTE (st X) (st Y))
              (X == 0)
              (Y ::= 2)
              (Y ::= X + 1)
              htt
              htf

if_minus_plus : HoareTriple (const ())
                            (CIf (X <= Y) (Z ::= Y - X) (Y ::= X + Z))
                            (\st => st Y = st X + st Z)
if_minus_plus =
  let htt = hoare_consequence
              (\st => ((), BAssn (X <= Y) st))
              (AssignSub Z (Y - X) (\st => ( st Y = st X + st Z
                                           , BAssn (X <= Y) st )))
              (\st => st Y = st X + st Z)
              (\st => (st Y = st X + st Z, BAssn (X <= Y) st))
              (Z ::= Y - X)
              (hoare_assign (\st => (st Y = st X + st Z, BAssn (X <= Y) st))
                                 Z
                            (Y - X))
              (\st, (_, p_st) =>
                 ( sym (lte_plus_minus (fst (lte_beq_iff (st X) (st Y)) p_st))
                 , p_st ))
              (\_, (q_st, _) => q_st)
      htf = hoare_consequence_pre
              (\st => ((), Not (BAssn (X <= Y) st)))
              (AssignSub Y (X + Z) (\st => st Y = st X + st Z))
              (\st => st Y = st X + st Z)
              (Y ::= X + Z)
              (hoare_assign (\st => st Y = st X + st Z) Y (X + Z))
              (\_, _ => Refl)
  in hoare_if (const ())
              (\st => st Y = st X + st Z)
              (X <= Y)
              (Z ::= Y - X)
              (Y ::= X + Z)
              htt
              htf

hoare_while : (p : Assertion) -> (b : BExp) -> (c : Com) ->
              HoareTriple (\st => (p st, BAssn b st)) c p ->
              HoareTriple p (WHILE b c) (\st => (p st, Not (BAssn b st)))
hoare_while p b c ht st _ (E_WhileEnd prf) p_st =
  (p_st, snd not_true_iff_false prf)
hoare_while p b c ht st st' (E_WhileLoop {st1} prf cbody cnext) p_st =
  hoare_while p b c ht st1 st' cnext (ht st st1 cbody (p_st, prf))

while_example : HoareTriple (\st => LTE (st X) 3)
                            (CWhile (X <= 2) (X ::= X + 1))
                            (\st => st X = 3)
while_example st st' rel lte_prf =
  let htc =  hoare_assign (\st => LTE (st X) 3) X (X + 1)
      htc' = hoare_consequence_pre
               (\st => (LTE (st X) 3, beval st (X <= 2) = True))
               (\st => LTE (st X + 1) 3)
               (\st => LTE (st X) 3)
               (X ::= X + 1)
               htc
               (\st, p_st => replace {P=\x => LTE x 3}
                                     (sym (plusCommutative (st X) 1))
                                     (LTESucc (fst (lte_beq_iff (st X) 2)
                                                   (snd p_st))))
      htw = hoare_while (\st => LTE (st X) 3) (X <= 2) (X ::= X + 1) htc'
      (below, contra) = htw st st' rel lte_prf
  in bounded__eq below (fst (lte_false_lt_iff (st' X) 2)
                            (fst not_true_iff_false contra))

always_loop_hoare : (p, q : Assertion) -> HoareTriple p (WHILE BTrue SKIP) q
always_loop_hoare p q =
  let htc = hoare_consequence_pre
              (\st => (p st, BAssn BTrue st))
              p
              p
              SKIP
              (hoare_skip p)
              (\st, (p_st, _) => p_st)
      htw = hoare_while p BTrue SKIP htc
  in hoare_consequence_post
           p
           q
           (\st => (p st, Not (BAssn BTrue st)))
           (WHILE BTrue SKIP)
           htw
           (\st, (_, contra) => absurd (contra Refl))
