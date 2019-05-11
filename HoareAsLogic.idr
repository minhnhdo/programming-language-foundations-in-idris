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
  H_If1 : HoareProof (\st => (p st, BAssn b st)) c q ->
          (\st => (p st, Not (BAssn b st))) ->> q ->
          HoareProof p (CIf1 b c) q
  H_While : HoareProof (\st => (p st, BAssn b st)) c p ->
            HoareProof p (CWhile b c) (\st => (p st, Not (BAssn b st)))
  H_For : HoareProof p init q ->
          HoareProof (\st => (q st, BAssn cond st)) (do body; updt) q ->
          HoareProof p (CFor init cond updt body)
                       (\st => (q st, Not (BAssn cond st)))
  H_Repeat : HoareProof p c q -> (\st => (q st, Not (BAssn b st))) ->> p ->
             HoareProof p (CRepeat c b) (\st => (q st, BAssn b st))
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
hoare_proof_sound (H_If1 {p} {q} {b} {c} hp imp) =
  hoare_if1 p q b c (hoare_proof_sound hp) imp
hoare_proof_sound (H_While {p} {b} {c} hp) =
  hoare_while p b c (hoare_proof_sound hp)
hoare_proof_sound (H_For {p} {q} {init} {cond} {updt} {body}
                         hp_init hp_body_updt) =
  hoare_for p q init cond updt body
            (hoare_proof_sound hp_init) (hoare_proof_sound hp_body_updt)
hoare_proof_sound (H_Repeat {p} {q} {c} {b} hp imp) =
  hoare_repeat p q c b (hoare_proof_sound hp) imp
hoare_proof_sound (H_Consequence {p} {c} {q} {p'} {q'} hp p_imp q_imp) =
  hoare_consequence p p' q q' c (hoare_proof_sound hp) p_imp q_imp

h_post_true_deriv : HoareProof p c (const ())
h_post_true_deriv {c = CSkip} = h_consequence_pre H_Skip (\_, _ => ())
h_post_true_deriv {c = (CAss _ _)} = h_consequence_pre H_Ass (\_, _ => ())
h_post_true_deriv {p} {c = (CSeq c1 c2)} =
  H_Seq (h_post_true_deriv {p=p} {c=c1}) (h_post_true_deriv {c=c2})
h_post_true_deriv {c = (CIf _ c1 c2)} =
  H_If (h_post_true_deriv {c=c1}) (h_post_true_deriv {c=c2})
h_post_true_deriv {c = (CIf1 _ c)} =
  H_If1 (h_post_true_deriv {c=c}) (\_, _ => ())
h_post_true_deriv {c = (CWhile _ c)} =
  H_Consequence (H_While {p=const ()} (h_post_true_deriv {c=c}))
                (\_, _ => ())
                (\_, _ => ())
h_post_true_deriv {p} {c = f@(CFor init _ updt body)} =
  h_consequence_post
    (H_For (h_post_true_deriv {p=p} {c=init})
           (h_post_true_deriv {c=assert_smaller f (do body; updt)}))
    (\_, _ => ())
h_post_true_deriv {c = (CRepeat c _)} =
  H_Consequence (H_Repeat (h_post_true_deriv {c=c}) (\_, _ => ()))
                (\_, _ => ())
                (\_, _ => ())
