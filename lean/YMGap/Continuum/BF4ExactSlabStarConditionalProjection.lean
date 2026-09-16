/-
# Original-law realization of the local conditional vector

The actual exterior probe is extended into the original full-action
weighted completion, retaining its explicit bound and null moduli.
Its completed pairings preserve the finite action identities. Combining
those identities with the constructed normalizer preimage realizes the
original conditional vector and reproduces its pairing against EVERY
completed exterior test, not just fixed polynomial tests.

All spaces here are ordinary weighted L2 spaces, not an OS quotient.
Spatial influence bounds, physical scaling and the Clay gap remain open.
-/

import YMGap.Continuum.BF4ExactSlabStarFullActionProbe
import YMGap.Continuum.BF4ExactSlabStarCompletedInverse
import YMGap.Continuum.GNSPairingNormBound
import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.BF4ExactSlabStarConditionalProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "F" => fullData hw0 hw1 K extent hK
local notation "J" => probeMap hw0 hw1 K extent hK link hl
local notation "N" => numeratorMap hw0 hw1 K extent hK link hl

/-- The actual exterior lift is bounded in original full-law distance. -/
theorem probe_distance_bound (a b : (G).V) :
    (F).distSqQ (J a) (J b) ≤ upperFactor w * (G).distSqQ a b := by
  have he := (F).B_diag_congr (probeMap_sub hw0 hw1 K extent hK link hl a b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (probeMap_norm hw0 hw1 K extent hK link hl ((G).sub a b))

private def probeTolerance (w epsilon : Q') : Q' :=
  epsilon * ExpUBInstance.oneOver1p (upperFactor w)

private theorem probeTolerance_pos {w epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < probeTolerance w epsilon := Q'.mul_pos h (oneOver1p_pos _)

include hw0 in
private theorem probe_budget {epsilon : Q'} (h : (0 : Q') < epsilon) :
    upperFactor w * probeTolerance w epsilon ≤ epsilon :=
  key_bound _ _ (Q'.le_of_lt (upperFactor_positive hw0)) (Q'.le_of_lt h)

/-- A pointwise lift into the ORIGINAL full-action form, with its input
modulus explicitly rescaled by the actual local cap U. -/
def probeCauchy (X : CauchyGNS G) : CauchyGNS F where
  seq := fun n => J (X.seq n)
  modulus := fun epsilon => X.modulus (probeTolerance w epsilon)
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _ (probe_distance_bound hw0 hw1 K extent hK link hl _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (X.isCauchy _ (probeTolerance_pos hepsilon) p q hp hq)
        (Q'.le_of_lt (upperFactor_positive hw0))) (probe_budget hw0 hepsilon))

def probeNullModulus {X Y : CauchyGNS G} (h : CauchyNullModulus G X Y) :
    CauchyNullModulus F (probeCauchy hw0 hw1 K extent hK link hl X)
      (probeCauchy hw0 hw1 K extent hK link hl Y) where
  modulus := fun epsilon => h.modulus (probeTolerance w epsilon)
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (probe_distance_bound hw0 hw1 K extent hK link hl _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h.close _ (probeTolerance_pos hepsilon) n hn)
        (Q'.le_of_lt (upperFactor_positive hw0))) (probe_budget hw0 hepsilon))

private theorem probeCauchy_null {X Y : CauchyGNS G} (h : CauchyNull G X Y) :
    CauchyNull F (probeCauchy hw0 hw1 K extent hK link hl X)
      (probeCauchy hw0 hw1 K extent hK link hl Y) := by
  intro epsilon hepsilon
  obtain ⟨index, hindex⟩ := h (probeTolerance w epsilon) (probeTolerance_pos hepsilon)
  refine ⟨index, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (probe_distance_bound hw0 hw1 K extent hK link hl _ _)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hindex n hn)
      (Q'.le_of_lt (upperFactor_positive hw0))) (probe_budget hw0 hepsilon))

/-- The completed exterior probe between the actual two weighted spaces. -/
def probeCompletion : GNSCompletionSpace G → GNSCompletionSpace F :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid F) (probeCauchy hw0 hw1 K extent hK link hl X))
    (fun _ _ h => Quotient.sound (probeCauchy_null hw0 hw1 K extent hK link hl h))

local notation "JC" => probeCompletion hw0 hw1 K extent hK link hl

theorem probeCompletion_embed (r : (G).V) : JC (embedV G r) = embedV F (J r) := by
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv ((F).rad_refl (J r))) (Q'.le_of_lt hepsilon)⟩

/-- The original marginal D*B is retained in ALL completed probe pairings.
Separate Cauchy diagonals are compared by limit uniqueness, not identified. -/
theorem probeCompletion_pair (x y : GNSCompletionSpace G) :
    (F).cinnerCompl (JC x) (JC y) =
      (G).cinnerCompl x (normalizerCompletion hw0 hw1 K extent hK link hl y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv (probeMap_pair hw0 hw1 K extent hK link hl (X.seq n) (Y.seq n))

/-- The finite original-law test identity survives the actual weighted lift. -/
theorem probeCompletion_test (x : GNSCompletionSpace G) (p : (F).V) :
    (F).cinnerCompl (JC x) (embedV F p) = (G).cinnerCompl x (embedV G (N p)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv (probeMap_test hw0 hw1 K extent hK link hl (X.seq n) p)

/-- The original-law conditional vector for a supported polynomial input. -/
def conditionalUpdate (p : (F).V) : GNSCompletionSpace F :=
  JC (inverseState hw0 hw1 K extent hK link hl (N p))

local notation "Q" => conditionalUpdate hw0 hw1 K extent hK link hl

/-- Reproduction against EVERY completed exterior test, including the
constructed conditional vector itself. No fixed-observable limit swap. -/
theorem conditionalUpdate_pairing (x : GNSCompletionSpace G) (p : (F).V) :
    (F).cinnerCompl (JC x) (Q p) = (F).cinnerCompl (JC x) (embedV F p) := by
  change (F).cinnerCompl (JC x) (JC (inverseState hw0 hw1 K extent hK link hl (N p))) = _
  rw [probeCompletion_pair, normalizer_inverseState]
  exact (probeCompletion_test hw0 hw1 K extent hK link hl x p).symm

theorem conditionalUpdate_self_pairing (p : (F).V) :
    (F).cinnerCompl (Q p) (Q p) = (F).cinnerCompl (Q p) (embedV F p) :=
  conditionalUpdate_pairing hw0 hw1 K extent hK link hl
    (inverseState hw0 hw1 K extent hK link hl (N p)) p

/-- The input-minus-output is orthogonal to the ENTIRE completed exterior
range, not just to one polynomial test or to the output vector. -/
theorem conditionalUpdate_orthogonal (x : GNSCompletionSpace G) (p : (F).V) :
    (F).cinnerCompl ((F).cSub (embedV F p) (Q p)) (JC x) = CReal.RCzero := by
  rw [(F).cinnerCompl_cSub_left, (F).cinnerCompl_comm (embedV F p) (JC x),
    (F).cinnerCompl_comm (Q p) (JC x), conditionalUpdate_pairing]
  generalize (F).cinnerCompl (JC x) (embedV F p) = a
  refine Quotient.inductionOn a ?_
  intro aRep
  exact Quotient.sound (CReal.sub_self_eqv_zero aRep)

/-- Orthogonality to the constructed output, in the original full-law space. -/
theorem conditionalUpdate_residual_orthogonal (p : (F).V) :
    (F).cinnerCompl (Q p) ((F).cSub (embedV F p) (Q p)) = CReal.RCzero :=
  GNSPairingNormBound.residual_orthogonal F (Q p) (embedV F p)
    (conditionalUpdate_self_pairing hw0 hw1 K extent hK link hl p)

/-- Sharp NON-STRICT contraction in the original full-action L2 norm.
The unit constant is a projection bound, not a strict mixing or mass-gap rate. -/
theorem conditionalUpdate_norm (p : (F).V) :
    CReal.RCle ((F).cinnerCompl (Q p) (Q p)) ((F).cinnerCompl (embedV F p) (embedV F p)) :=
  GNSPairingNormBound.norm_le_of_self_pairing F (Q p) (embedV F p)
    (conditionalUpdate_self_pairing hw0 hw1 K extent hK link hl p)

private theorem inner_sub_right (D : GNSData) (x y z : GNSCompletionSpace D) :
    D.cinnerCompl x (D.cSub y z) = CReal.RCsub (D.cinnerCompl x y) (D.cinnerCompl x z) := by
  rw [D.cinnerCompl_comm x (D.cSub y z), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm y x, D.cinnerCompl_comm z x]

/-- The original-law conditional construction contracts differences as
well as norms. This is the dense input needed for a full-space extension. -/
theorem conditionalUpdate_nonexpansive (p q : (F).V) :
    CReal.RCle
      ((F).cinnerCompl ((F).cSub (Q p) (Q q)) ((F).cSub (Q p) (Q q)))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' ((F).distSqQ p q))) := by
  have hpairs (a b : (F).V) : (F).cinnerCompl (Q a) (Q b) = (F).cinnerCompl (Q a) (embedV F b) :=
    conditionalUpdate_pairing hw0 hw1 K extent hK link hl
      (inverseState hw0 hw1 K extent hK link hl (N a)) b
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

/-- Original full-action null classes give exactly the same conditional vector. -/
theorem conditionalUpdate_rad {p q : (F).V} (h : (F).rad p q) : Q p = Q q := by
  exact congrArg JC (inverseState_rad hw0 hw1 K extent hK link hl
    (numerator_rad hw0 hw1 K extent hK link hl p q h))

/-- The actual dense conditional outputs carry their already-constructed
Cauchy representatives and the sharp two-input bound. -/
def conditionalDenseMap : DenseMap F where
  toRep := fun p => probeCauchy hw0 hw1 K extent hK link hl
    (inverseCauchy hw0 hw1 K extent hK link hl (N p))
  nonexpansive := conditionalUpdate_nonexpansive hw0 hw1 K extent hK link hl

/-- The conditional operator acts on the ENTIRE original full-action
completion, using the existing constructive diagonal extension. -/
def conditionalProjection : GNSCompletionSpace F → GNSCompletionSpace F :=
  (conditionalDenseMap hw0 hw1 K extent hK link hl).completionMap

local notation "C" => conditionalProjection hw0 hw1 K extent hK link hl

theorem conditionalProjection_embed (p : (F).V) : C (embedV F p) = Q p :=
  (conditionalDenseMap hw0 hw1 K extent hK link hl).completionMap_embed p

theorem conditionalProjection_nonexpansive (x y : GNSCompletionSpace F) :
    CReal.RCle ((F).cinnerCompl ((F).cSub (C x) (C y)) ((F).cSub (C x) (C y)))
      ((F).cinnerCompl ((F).cSub x y) ((F).cSub x y)) :=
  GNSDenseCompletionLaws.completionMap_nonexpansive
    (conditionalDenseMap hw0 hw1 K extent hK link hl) x y

theorem conditionalProjection_selfAdjoint (x y : GNSCompletionSpace F) :
    (F).cinnerCompl (C x) y = (F).cinnerCompl x (C y) := by
  apply GNSDenseCompletionLaws.completionMap_selfAdjoint
    (conditionalDenseMap hw0 hw1 K extent hK link hl) _ x y
  intro p q
  change (F).cinnerCompl (Q p) (embedV F q) = (F).cinnerCompl (embedV F p) (Q q)
  have hpq := conditionalUpdate_pairing hw0 hw1 K extent hK link hl
    (inverseState hw0 hw1 K extent hK link hl (N p)) q
  have hqp := conditionalUpdate_pairing hw0 hw1 K extent hK link hl
    (inverseState hw0 hw1 K extent hK link hl (N q)) p
  exact hpq.symm.trans (((F).cinnerCompl_comm (Q p) (Q q)).trans
    (hqp.trans ((F).cinnerCompl_comm (Q q) (embedV F p))))

/-- Positive as a Hilbert-space form; NOT an order-preserving/Markov claim. -/
theorem conditionalProjection_positive (x : GNSCompletionSpace F) :
    CReal.RCnonneg ((F).cinnerCompl (C x) x) := by
  apply GNSDenseCompletionLaws.completionMap_positive
    (conditionalDenseMap hw0 hw1 K extent hK link hl) _ x
  intro p
  change CReal.RCnonneg ((F).cinnerCompl (Q p) (embedV F p))
  rw [← conditionalUpdate_self_pairing]
  exact (F).cinner_self_nonneg (Q p)

/-- Every completed exterior probe is fixed by the actual projection. -/
theorem conditionalProjection_fix_exterior (x : GNSCompletionSpace G) : C (JC x) = JC x := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro p
  rw [conditionalProjection_selfAdjoint, conditionalProjection_embed]
  exact conditionalUpdate_pairing hw0 hw1 K extent hK link hl x p

/-- Idempotence on ALL original completion vectors follows from dense
pairings, self-adjointness and the actual exterior-output construction. -/
theorem conditionalProjection_idempotent (x : GNSCompletionSpace F) : C (C x) = C x := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro p
  rw [conditionalProjection_selfAdjoint, conditionalProjection_embed, conditionalProjection_selfAdjoint]
  have hfix : C (Q p) = Q p :=
    conditionalProjection_fix_exterior hw0 hw1 K extent hK link hl
      (inverseState hw0 hw1 K extent hK link hl (N p))
  rw [hfix]
  exact ((conditionalProjection_selfAdjoint hw0 hw1 K extent hK link hl x (embedV F p)).trans
    (congrArg ((F).cinnerCompl x) (conditionalProjection_embed hw0 hw1 K extent hK link hl p))).symm

theorem conditionalProjection_norm (x : GNSCompletionSpace F) :
    CReal.RCle ((F).cinnerCompl (C x) (C x)) ((F).cinnerCompl x x) := by
  apply GNSPairingNormBound.norm_le_of_self_pairing
  rw [conditionalProjection_selfAdjoint, conditionalProjection_idempotent]
  exact (F).cinnerCompl_comm x (C x)

/-- Original full-space residuals are orthogonal to every exterior probe. -/
theorem conditionalProjection_orthogonal (x : GNSCompletionSpace F) (y : GNSCompletionSpace G) :
    (F).cinnerCompl ((F).cSub x (C x)) (JC y) = CReal.RCzero := by
  rw [(F).cinnerCompl_cSub_left, conditionalProjection_selfAdjoint, conditionalProjection_fix_exterior]
  generalize (F).cinnerCompl x (JC y) = a
  refine Quotient.inductionOn a ?_
  intro aRep
  exact Quotient.sound (CReal.sub_self_eqv_zero aRep)

end YMGap.Continuum.BF4ExactSlabStarConditionalProjection

#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probe_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeNullModulus
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeCompletion
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeCompletion_embed
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeCompletion_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.probeCompletion_test
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_pairing
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_self_pairing
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_residual_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_nonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalUpdate_rad
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalDenseMap
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_embed
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_nonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_positive
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_fix_exterior
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalProjection.conditionalProjection_orthogonal
