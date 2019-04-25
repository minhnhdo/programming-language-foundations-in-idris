module EquivExercises

import Equiv
import Expr
import Imp
import Inequiv
import Logic
import Maps

%access public export

%default total

noninterfering_update : Not (l1 = l2) ->
                        VarNotUsedInAExp l1 a2 ->
                        VarNotUsedInAExp l2 a1 ->
                        aeval st a1 = n1 ->
                        ((aeval (t_update l1 n1 st) a2 = n2) ↔ aeval st a2 = n2)
noninterfering_update _ (VNUNum _) _ _ = (id, id)
noninterfering_update _ (VNUId y contra) _ _ =
  rewrite snd (beq_id_false_iff {x=l1} {y=y}) contra
  in (id, id)
noninterfering_update {st} contra (VNUPlus _ _ l1nua3 l1nua4) l2nua1 prf1 =
  let ih1 = noninterfering_update {st=st} contra l1nua3 l2nua1 prf1
      ih2 = noninterfering_update {st=st} contra l1nua4 l2nua1 prf1
  in ( \prf2 => rewrite fst ih1 Refl
                in rewrite fst ih2 Refl
                in prf2
     , \prf2 => rewrite sym $ fst ih1 Refl
                in rewrite sym $ fst ih2 Refl
                in prf2 )
noninterfering_update {st} contra (VNUMinus _ _ l1nua3 l1nua4) l2nua1 prf1 =
  let ih1 = noninterfering_update {st=st} contra l1nua3 l2nua1 prf1
      ih2 = noninterfering_update {st=st} contra l1nua4 l2nua1 prf1
  in ( \prf2 => rewrite fst ih1 Refl
                in rewrite fst ih2 Refl
                in prf2
     , \prf2 => rewrite sym $ fst ih1 Refl
                in rewrite sym $ fst ih2 Refl
                in prf2 )
noninterfering_update {st} contra (VNUMult _ _ l1nua3 l1nua4) l2nua1 prf1 =
  let ih1 = noninterfering_update {st=st} contra l1nua3 l2nua1 prf1
      ih2 = noninterfering_update {st=st} contra l1nua4 l2nua1 prf1
  in ( \prf2 => rewrite fst ih1 Refl
                in rewrite fst ih2 Refl
                in prf2
     , \prf2 => rewrite sym $ fst ih1 Refl
                in rewrite sym $ fst ih2 Refl
                in prf2 )

swap_noninterfering_assignments : Not (l1 = l2) ->
                                  VarNotUsedInAExp l1 a2 ->
                                  VarNotUsedInAExp l2 a1 ->
                                  CEquiv (do l1 ::= a1; l2 ::= a2)
                                         (do l2 ::= a2; l1 ::= a1)
swap_noninterfering_assignments {l1} {l2} {a1} {a2} contra l1nua2 l2nua1 st st' =
  (forward, backward)
where forward : ((do l1 ::= a1; l2 ::= a2) / st \\ st') ->
                ((do l2 ::= a2; l1 ::= a1) / st \\ st')
      forward rel = case rel of
        E_Seq (E_Ass {n=n1} prf1) (E_Ass {n=n2} prf2) =>
          let pf1 = fst (noninterfering_update {st=st} contra l1nua2 l2nua1 prf1)
                        prf2
              pf2 = snd (noninterfering_update {st=st}
                                               (neqSym contra) l2nua1 l1nua2 pf1)
                        prf1
          in rewrite t_update_permute contra {v1=n2} {v2=n1} {m=st}
          in E_Seq (E_Ass pf1) (E_Ass pf2)
      backward : ((do l2 ::= a2; l1 ::= a1) / st \\ st') ->
                 ((do l1 ::= a1; l2 ::= a2) / st \\ st')
      backward rel = case rel of
        E_Seq (E_Ass {n=n1} prf1) (E_Ass {n=n2} prf2) =>
          let pf1 = fst (noninterfering_update
                           {st=st} (neqSym contra) l2nua1 l1nua2 prf1)
                        prf2
              pf2 = snd (noninterfering_update {st=st} contra l1nua2 l2nua1 pf1)
                        prf1
          in rewrite sym $ t_update_permute contra {v1=n1} {v2=n2} {m=st}
          in E_Seq (E_Ass pf1) (E_Ass pf2)

CApprox : (c1, c2 : Com) -> Type
CApprox c1 c2 = (st, st' : State) -> (c1 / st \\ st') -> (c2 / st \\ st')

c1 : Com
c1 = WHILE (not (X == 1)) $
       X ::= X - 1

c2 : Com
c2 = X ::= 1

c3 : Com
c3 = c2

c4 : Com
c4 = X ::= 2

c3_c4_different : ( Not (CApprox EquivExercises.c3 EquivExercises.c4)
                  , Not (CApprox EquivExercises.c4 EquivExercises.c3) )
c3_c4_different = (forward, backward)
where forward : Not ((st, st' : State) ->
                     (EquivExercises.c3 / st \\ st') ->
                     (EquivExercises.c4 / st \\ st'))
      forward f = case f empty_state (t_update X 1 empty_state) (E_Ass Refl) of
        E_Skip impossible
        (E_Ass _) impossible
        (E_Seq _ _) impossible
        (E_IfTrue _ _) impossible
        (E_IfFalse _ _) impossible
        (E_WhileEnd _) impossible
        (E_WhileLoop _ _ _) impossible
      backward : Not ((st, st' : State) ->
                      (EquivExercises.c4 / st \\ st') ->
                      (EquivExercises.c3 / st \\ st'))
      backward f = case f empty_state (t_update X 2 empty_state) (E_Ass Refl) of
        E_Skip impossible
        (E_Ass _) impossible
        (E_Seq _ _) impossible
        (E_IfTrue _ _) impossible
        (E_IfFalse _ _) impossible
        (E_WhileEnd _) impossible
        (E_WhileLoop _ _ _) impossible

cmin : Com
cmin = WHILE BTrue SKIP

cmin_minimal : (c : Com) -> CApprox EquivExercises.cmin c
cmin_minimal _ _ _ rel = absurd $ while_true_nonterm btrue_is_true rel
