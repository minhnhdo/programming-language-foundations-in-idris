module HoareAsLogic

import Assn
import Expr
import Hoare
import Imp
import Maps

%access public export

%default total

data HoareProof : Assertion -> Com -> Assertion -> Type where
  H_Skip : HoareProof p SKIP p
  H_Ass : HoareProof (AssignSub x a q) (x ::= a) q
  H_Seq : HoareProof p c q -> HoareProof q d r ->
          HoareProof p (do c; d) r
  H_If : HoareProof (\st => (p st, BAssn b st)) c1 q ->
         HoareProof (\st => (p st, Not (BAssn b st))) c2 q ->
         HoareProof p (CIf b c1 c2) q
  H_While : HoareProof (\st => (p st, BAssn b st)) c p ->
            HoareProof p (CWhile b c) (\st => (p st, Not (BAssn b st)))
  H_Consequence : HoareProof p' c q' -> (p ->> p') -> (q' ->> q) ->
                  HoareProof p c q

h_consequence_pre : HoareProof p' c q -> (p ->> p') -> HoareProof p c q
h_consequence_pre hp imp = H_Consequence hp imp assertImpliesRefl

h_consequence_post : HoareProof p c q' -> (q' ->> q) -> HoareProof p c q
h_consequence_post hp imp = H_Consequence hp assertImpliesRefl imp

sample_proof : HoareProof
                 (AssignSub X (X + 1) (AssignSub X (X + 2) (\st => st X = 3)))
                 (do X ::= X + 1; X ::= X + 2)
                 (\st => st X = 3)
sample_proof = H_Seq H_Ass H_Ass

hoare_proof_sound : HoareProof p c q -> HoareTriple p c q
hoare_proof_sound {q} H_Skip = hoare_skip q
hoare_proof_sound (H_Ass {x} {a} {q}) = hoare_assign q x a
hoare_proof_sound (H_Seq {p} {q} {r} {c} {d} hp1 hp2) =
  hoare_seq p q r c d (hoare_proof_sound hp2) (hoare_proof_sound hp1)
hoare_proof_sound (H_If {p} {q} {b} {c1} {c2} hpt hpf) =
  hoare_if p q b c1 c2 (hoare_proof_sound hpt) (hoare_proof_sound hpf)
hoare_proof_sound (H_While {p} {b} {c} hp) =
  hoare_while p b c (hoare_proof_sound hp)
hoare_proof_sound (H_Consequence {p} {c} {q} {p'} {q'} hp p_imp q_imp) =
  hoare_consequence p p' q q' c (hoare_proof_sound hp) p_imp q_imp
