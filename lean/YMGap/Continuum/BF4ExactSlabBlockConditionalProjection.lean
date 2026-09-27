/-
# The actual finite-block conditional projection on the original completion

The constructed N_p/D outputs reproduce their original-action pairings.
That identity gives sharp nonexpansiveness, hence the existing constructive
dense extension acts on every vector of the SAME full-action completion.
Self-adjointness and idempotence follow from dense pairing identities.

This is an ordinary weighted-L2 conditional projection, not an OS transfer
operator. No signed inter-block estimate, strict global contraction or physical
scaling/mass-gap claim follows from the non-strict projection norm bound.
-/

import YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
import YMGap.Continuum.GNSPairingNormBound
import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.BF4ExactSlabBlockConditionalProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "Q" => conditionalUpdate hw0 hw1 K extent hK links hl

theorem conditionalUpdate_self_pairing (p : (F).V) :
    (F).cinnerCompl (Q p) (Q p) = (F).cinnerCompl (Q p) (embedV F p) :=
  conditionalUpdate_pairing hw0 hw1 K extent hK links hl p p

theorem conditionalUpdate_residual_orthogonal (p : (F).V) :
    (F).cinnerCompl (Q p) ((F).cSub (embedV F p) (Q p)) = CReal.RCzero :=
  GNSPairingNormBound.residual_orthogonal F (Q p) (embedV F p)
    (conditionalUpdate_self_pairing hw0 hw1 K extent hK links hl p)

/-- The norm ceiling is exactly one; this is NOT a strict gap. -/
theorem conditionalUpdate_norm (p : (F).V) :
    CReal.RCle ((F).cinnerCompl (Q p) (Q p))
      ((F).cinnerCompl (embedV F p) (embedV F p)) :=
  GNSPairingNormBound.norm_le_of_self_pairing F (Q p) (embedV F p)
    (conditionalUpdate_self_pairing hw0 hw1 K extent hK links hl p)

private theorem inner_sub_right (D : GNSData) (x y z : GNSCompletionSpace D) :
    D.cinnerCompl x (D.cSub y z) = CReal.RCsub (D.cinnerCompl x y) (D.cinnerCompl x z) := by
  rw [D.cinnerCompl_comm x (D.cSub y z), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm y x, D.cinnerCompl_comm z x]

/-- The actual dense output map contracts distances in the original norm. -/
theorem conditionalUpdate_nonexpansive (p q : (F).V) :
    CReal.RCle
      ((F).cinnerCompl ((F).cSub (Q p) (Q q)) ((F).cSub (Q p) (Q q)))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' ((F).distSqQ p q))) := by
  have hpairs (a b : (F).V) :
      (F).cinnerCompl (Q a) (Q b) = (F).cinnerCompl (Q a) (embedV F b) :=
    conditionalUpdate_pairing hw0 hw1 K extent hK links hl a b
  have hself : (F).cinnerCompl ((F).cSub (Q p) (Q q)) ((F).cSub (Q p) (Q q)) =
      (F).cinnerCompl ((F).cSub (Q p) (Q q)) ((F).cSub (embedV F p) (embedV F q)) := by
    simp only [(F).cinnerCompl_cSub_left, inner_sub_right, hpairs]
  have hnorm := GNSPairingNormBound.norm_le_of_self_pairing F
    ((F).cSub (Q p) (Q q)) ((F).cSub (embedV F p) (embedV F q)) hself
  have he : (F).cinnerCompl ((F).cSub (embedV F p) (embedV F q))
      ((F).cSub (embedV F p) (embedV F q)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' ((F).distSqQ p q)) := by
    apply Quotient.sound
    exact CReal.Equiv_of_approx_eq (fun _ => rfl)
  rw [he] at hnorm
  exact hnorm

/-- Actual output representatives with their sharp original-norm bound. -/
def conditionalDenseMap : DenseMap F where
  toRep := conditionalRep hw0 hw1 K extent hK links hl
  nonexpansive := conditionalUpdate_nonexpansive hw0 hw1 K extent hK links hl

/-- A constructed operator on EVERY vector of the original completion. -/
def conditionalProjection : GNSCompletionSpace F → GNSCompletionSpace F :=
  (conditionalDenseMap hw0 hw1 K extent hK links hl).completionMap

local notation "C" => conditionalProjection hw0 hw1 K extent hK links hl

theorem conditionalProjection_embed (p : (F).V) : C (embedV F p) = Q p :=
  (conditionalDenseMap hw0 hw1 K extent hK links hl).completionMap_embed p

theorem conditionalProjection_nonexpansive (x y : GNSCompletionSpace F) :
    CReal.RCle ((F).cinnerCompl ((F).cSub (C x) (C y)) ((F).cSub (C x) (C y)))
      ((F).cinnerCompl ((F).cSub x y) ((F).cSub x y)) :=
  GNSDenseCompletionLaws.completionMap_nonexpansive
    (conditionalDenseMap hw0 hw1 K extent hK links hl) x y

theorem conditionalProjection_selfAdjoint (x y : GNSCompletionSpace F) :
    (F).cinnerCompl (C x) y = (F).cinnerCompl x (C y) := by
  apply GNSDenseCompletionLaws.completionMap_selfAdjoint
    (conditionalDenseMap hw0 hw1 K extent hK links hl) _ x y
  intro p q
  change (F).cinnerCompl (Q p) (embedV F q) = (F).cinnerCompl (embedV F p) (Q q)
  have hpq := conditionalUpdate_pairing hw0 hw1 K extent hK links hl p q
  have hqp := conditionalUpdate_pairing hw0 hw1 K extent hK links hl q p
  exact hpq.symm.trans (((F).cinnerCompl_comm (Q p) (Q q)).trans
    (hqp.trans ((F).cinnerCompl_comm (Q q) (embedV F p))))

/-- The dense conditional outputs lie in the fixed space of the actual map. -/
theorem conditionalProjection_fix_update (p : (F).V) : C (Q p) = Q p := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro q
  rw [conditionalProjection_selfAdjoint, conditionalProjection_embed]
  exact conditionalUpdate_pairing hw0 hw1 K extent hK links hl p q

/-- Every explicitly exterior Cauchy representative is fixed. Independence
is a hypothesis on each term, not asserted for an arbitrary background class. -/
theorem conditionalProjection_fix_exterior
    (X : CauchyGNS (backgroundData hw0 hw1 K extent hK links))
    (hX : ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i (X.seq n).val) :
    C (toFullCompletion hw0 hw1 K extent hK links hl
      (Quotient.mk (cauchySetoid (backgroundData hw0 hw1 K extent hK links)) X)) =
      toFullCompletion hw0 hw1 K extent hK links hl
        (Quotient.mk (cauchySetoid (backgroundData hw0 hw1 K extent hK links)) X) := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro p
  rw [conditionalProjection_selfAdjoint, conditionalProjection_embed]
  exact conditionalUpdate_pairing_exterior hw0 hw1 K extent hK links hl X hX p

theorem conditionalProjection_fix_exterior_polynomial (p : (F).V)
    (hp : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i p.val) :
    C (embedV F p) = embedV F p := by
  let G := backgroundData hw0 hw1 K extent hK links
  have h := conditionalProjection_fix_exterior hw0 hw1 K extent hK links hl
    (constCauchy G p) (fun _ => hp)
  have he : toFullCompletion hw0 hw1 K extent hK links hl (embedV G p) = embedV F p :=
    toFullCompletion_embed hw0 hw1 K extent hK links hl p
  change C (toFullCompletion hw0 hw1 K extent hK links hl (embedV G p)) =
    toFullCompletion hw0 hw1 K extent hK links hl (embedV G p) at h
  rw [he] at h
  exact h

theorem conditionalProjection_idempotent (x : GNSCompletionSpace F) : C (C x) = C x := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro p
  rw [conditionalProjection_selfAdjoint, conditionalProjection_embed,
    conditionalProjection_selfAdjoint, conditionalProjection_fix_update]
  exact ((conditionalProjection_selfAdjoint hw0 hw1 K extent hK links hl x (embedV F p)).trans
    (congrArg ((F).cinnerCompl x) (conditionalProjection_embed hw0 hw1 K extent hK links hl p))).symm

theorem conditionalProjection_norm (x : GNSCompletionSpace F) :
    CReal.RCle ((F).cinnerCompl (C x) (C x)) ((F).cinnerCompl x x) := by
  apply GNSPairingNormBound.norm_le_of_self_pairing
  rw [conditionalProjection_selfAdjoint, conditionalProjection_idempotent]
  exact (F).cinnerCompl_comm x (C x)

/-- Positivity is Hilbert-form positivity, not a Markov-order claim. -/
theorem conditionalProjection_positive (x : GNSCompletionSpace F) :
    CReal.RCnonneg ((F).cinnerCompl (C x) x) := by
  have he : (F).cinnerCompl (C x) (C x) = (F).cinnerCompl (C x) x := by
    rw [conditionalProjection_selfAdjoint, conditionalProjection_idempotent]
    exact (F).cinnerCompl_comm x (C x)
  rw [← he]
  exact (F).cinner_self_nonneg (C x)

theorem conditionalProjection_residual_orthogonal (x y : GNSCompletionSpace F) :
    (F).cinnerCompl ((F).cSub x (C x)) (C y) = CReal.RCzero := by
  rw [(F).cinnerCompl_cSub_left, conditionalProjection_selfAdjoint,
    conditionalProjection_idempotent]
  generalize (F).cinnerCompl x (C y) = a
  refine Quotient.inductionOn a ?_
  intro aRep
  exact Quotient.sound (CReal.sub_self_eqv_zero aRep)

#print axioms conditionalUpdate_self_pairing
#print axioms conditionalUpdate_residual_orthogonal
#print axioms conditionalUpdate_norm
#print axioms conditionalUpdate_nonexpansive
#print axioms conditionalDenseMap
#print axioms conditionalProjection
#print axioms conditionalProjection_embed
#print axioms conditionalProjection_nonexpansive
#print axioms conditionalProjection_selfAdjoint
#print axioms conditionalProjection_fix_update
#print axioms conditionalProjection_fix_exterior
#print axioms conditionalProjection_fix_exterior_polynomial
#print axioms conditionalProjection_idempotent
#print axioms conditionalProjection_norm
#print axioms conditionalProjection_positive
#print axioms conditionalProjection_residual_orthogonal

end YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
