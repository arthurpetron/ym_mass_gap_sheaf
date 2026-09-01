/-
# Projective producer for the growing-reference boundary posterior floor

The coarse growing repair is now equivalent to a pointwise lower bound on
the posterior probability of the selected low-spin reference state.  The
repository's normalized-projective theorem supplies the same-volume half of
such a bound: if an unnormalized boundary-amplitude column and its physical
row marginal have squared projective spread at most `65/64`, normalization
gives

  marginal(state) <= (65/64) * posterior(state | boundary).

The repair, however, starts from a fixed-half marginal.  This module keeps
that mismatch honest: it combines the projective window with a separately
named fixed-to-growing marginal comparison, then compiles the two factors
through the posterior, positive-boundary, completion-column, and coarse-
repair interfaces.  The existing matched physical half-amplitude projective
package supplies only the second factor; the first is precisely the earlier
tail-sensitive growing-ray domination input.  No new comparison or
projective bound is inhabited here.  No cofinal gap, continuum limit, or
Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior
import YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Pointwise normalized-projective window -/

/-- A raw projective bound between one half-amplitude column and the exact
physical marginal gives the normalized pointwise posterior window. -/
theorem centralPhysicalRowMarginal_le_anchoredProjectiveCeiling_mul_targetGivenBoundary_of_rawProjective
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {boundary target : EdgeLabelling}
    (htotal :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
    (htarget :
      target ∈ centralPositiveHalfStates w hw K half)
    (spread : Q')
    (hspread :
      spread * spread ≤ anchoredProjectiveCeiling)
    (rawProjective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread
        (centralPositiveHalfStates w hw K half)
        (fun state =>
          centralHalfAmplitude w K half state boundary)
        (centralPhysicalRowMarginal w hw K half)) :
    centralPhysicalRowMarginal w hw K half target ≤
      anchoredProjectiveCeiling *
        centralTargetGivenBoundary
          w hw K half boundary htotal target := by
  let states := centralPositiveHalfStates w hw K half
  let posterior := centralTargetGivenBoundary
    w hw K half boundary htotal
  let marginal := centralPhysicalRowMarginal w hw K half
  let data : NormalizedProjectivePair states posterior marginal := {
    spread := spread
    left_nonnegative := by
      intro state _
      unfold posterior
      exact centralTargetGivenBoundary_nonnegative
        hw K half boundary htotal state
    right_nonnegative := by
      intro state _
      unfold marginal
      exact centralPhysicalRowMarginal_nonnegative
        hw K half state
    left_total_one := by
      unfold states posterior
      exact centralTargetGivenBoundary_total_one htotal
    right_total_one := by
      unfold states marginal
      exact centralPositiveRowMarginal_total_one
        w hw K half
    spreadSquare_le := hspread
    projective := by
      intro left left_mem right right_mem
      have hraw := rawProjective
        left left_mem right right_mem
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
        hraw
        (Q'.le_of_lt
          (Q'.recipPos_pos
            (centralPositiveBoundaryTotalHalfAmplitude
              w hw K half boundary)
            htotal))
      unfold posterior marginal centralTargetGivenBoundary
        finiteStateGivenChannel Q'.divPos
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
      · q_ring
      · q_ring
  }
  exact data.right_upper target (by
    unfold states
    exact htarget)

/-! ## 2. Honest two-factor finite compiler -/

private theorem one_le_mul_anchoredProjectiveCeiling
    {ceiling : Q'} (hone : (1 : Q') ≤ ceiling) :
    (1 : Q') ≤ ceiling * anchoredProjectiveCeiling := by
  have hceilingNonnegative : (0 : Q') ≤ ceiling :=
    Q'.le_trans' _ _ _ Q'.zero_le_one hone
  have hanchor : (1 : Q') ≤ anchoredProjectiveCeiling := by
    decide
  have hscaled : ceiling * 1 ≤
      ceiling * anchoredProjectiveCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ ceiling
      hanchor hceilingNonnegative
  exact Q'.le_trans' _ ceiling _ hone
    (Q'.le_trans' _ (ceiling * 1) _
      (Q'.ge_of_eqv (Q'.mul_one_eqv ceiling)) hscaled)

/-- A projective posterior factor does not compare reflection volumes.  The
fixed-to-growing marginal comparison is therefore retained as an explicit,
separate field. -/
structure CoarseGrowingReferenceBoundaryProjectiveFactorBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (marginalCeiling : Q') : Type where
  one_le_marginal_ceiling : (1 : Q') ≤ marginalCeiling
  fixed_marginal_le_growing_reference :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0
        (centralLowerSpinCubeState 1) ≤
      marginalCeiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume)
  boundary_spread : EdgeLabelling → Q'
  boundary_spread_square_le : ∀ boundary,
    boundary ∈ centralBoundaryChannels K (volume + 1) →
      boundary_spread boundary * boundary_spread boundary ≤
        anchoredProjectiveCeiling
  target_raw_projective : ∀ boundary,
    boundary ∈ centralBoundaryChannels K (volume + 1) →
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        (boundary_spread boundary)
        (centralPositiveHalfStates
          w (Q'.le_of_lt hw) K (volume + 1))
        (fun target =>
          centralHalfAmplitude
            w K (volume + 1) target boundary)
        (centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1))

theorem CoarseGrowingReferenceBoundaryProjectiveFactorBound.referencePosteriorFloorAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {marginalCeiling : Q'}
    (bound : CoarseGrowingReferenceBoundaryProjectiveFactorBound
      w hw K hK volume marginalCeiling)
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K (volume + 1))
    (htotal :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w (Q'.le_of_lt hw) K (volume + 1) boundary) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0
        (centralLowerSpinCubeState 1) ≤
      (marginalCeiling * anchoredProjectiveCeiling) *
        centralTargetGivenBoundary
          w (Q'.le_of_lt hw) K (volume + 1)
          boundary htotal (lowSpinCentralReferenceState volume) := by
  let growingMarginal := centralPhysicalRowMarginal
    w (Q'.le_of_lt hw) K (volume + 1)
      (lowSpinCentralReferenceState volume)
  let posterior := centralTargetGivenBoundary
    w (Q'.le_of_lt hw) K (volume + 1)
      boundary htotal (lowSpinCentralReferenceState volume)
  have href :
      lowSpinCentralReferenceState volume ∈
        centralPositiveHalfStates
          w (Q'.le_of_lt hw) K (volume + 1) := by
    unfold lowSpinCentralReferenceState
    exact mem_centralPositiveHalfStates_of_le
      (Q'.le_of_lt hw) hK
      (lowSpinCentralLowerState_mem_positive hw
        (lowSpinCentralReferenceIndex volume))
  have hprojective :
      growingMarginal ≤ anchoredProjectiveCeiling * posterior := by
    unfold growingMarginal posterior
    exact
      centralPhysicalRowMarginal_le_anchoredProjectiveCeiling_mul_targetGivenBoundary_of_rawProjective
        (w := w) (K := K) (half := volume + 1)
        (boundary := boundary)
        (target := lowSpinCentralReferenceState volume)
        (Q'.le_of_lt hw) htotal href
        (bound.boundary_spread boundary)
        (bound.boundary_spread_square_le boundary hboundary)
        (bound.target_raw_projective boundary hboundary)
  have hmarginalCeilingNonnegative : (0 : Q') ≤ marginalCeiling :=
    Q'.le_trans' _ _ _ Q'.zero_le_one
      bound.one_le_marginal_ceiling
  have hscaled :
      marginalCeiling * growingMarginal ≤
        marginalCeiling *
          (anchoredProjectiveCeiling * posterior) :=
    Q'.mul_le_mul_of_nonneg_left _ _ marginalCeiling
      hprojective hmarginalCeilingNonnegative
  exact Q'.le_trans' _ _ _
    bound.fixed_marginal_le_growing_reference
    (Q'.le_trans' _ _ _ hscaled
      (Q'.ge_of_eqv
        (Q'.mul_assoc_eqv marginalCeiling
          anchoredProjectiveCeiling posterior)))

def CoarseGrowingReferenceBoundaryProjectiveFactorBound.toReferenceBoundaryPosteriorFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {marginalCeiling : Q'}
    (bound : CoarseGrowingReferenceBoundaryProjectiveFactorBound
      w hw K hK volume marginalCeiling) :
    CoarseGrowingReferenceBoundaryPosteriorFloor
      w hw K hK volume
        (marginalCeiling * anchoredProjectiveCeiling) where
  one_le_ceiling :=
    one_le_mul_anchoredProjectiveCeiling
      bound.one_le_marginal_ceiling
  reference_posterior_floor := fun boundary hboundary htotal =>
    bound.referencePosteriorFloorAt boundary hboundary htotal

def CoarseGrowingReferenceBoundaryProjectiveFactorBound.toCompletionColumnCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {marginalCeiling : Q'}
    (bound : CoarseGrowingReferenceBoundaryProjectiveFactorBound
      w hw K hK volume marginalCeiling) :
    CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume
        (marginalCeiling * anchoredProjectiveCeiling) :=
  bound.toReferenceBoundaryPosteriorFloor
    |>.toPositiveBoundaryHalfAmplitudeCrossBound
    |>.toCompletionColumnCrossBound

/-! ## 3. Matched trajectory and the tail-sensitive factor -/

structure MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  marginalCeiling : Q'
  one_le_marginal_ceiling : (1 : Q') ≤ marginalCeiling
  factorBound : ∀ scale,
    CoarseGrowingReferenceBoundaryProjectiveFactorBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale marginalCeiling

def MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound.toReferenceBoundaryPosteriorFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound
        bridge) :
    MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor bridge where
  ceiling := bound.marginalCeiling * anchoredProjectiveCeiling
  one_le_ceiling := one_le_mul_anchoredProjectiveCeiling
    bound.one_le_marginal_ceiling
  posteriorFloor := fun scale =>
    CoarseGrowingReferenceBoundaryProjectiveFactorBound.toReferenceBoundaryPosteriorFloor
      (bound.factorBound scale)

def MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound.toCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound
        bridge) :
    MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge :=
  bound.toReferenceBoundaryPosteriorFloor.toCompletionColumnCrossBound

/-- The existing matched half-amplitude projective field closes the boundary
factor only after the earlier fixed-to-growing ray domination is supplied.
The latter already carries the matched tail-zero cost. -/
def MatchedHalfAmplitudeProjectiveRows.withGrowingRayDominationToProjectiveFactorBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {diagonalOrder : Nat → Nat}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (data :
      MatchedHalfAmplitudeProjectiveRows
        family law spacing coupling
        (fun scale => scale + 1) diagonalOrder)
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge) :
    MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound
      bridge where
  marginalCeiling := 1 + comparison.ceiling
  one_le_marginal_ceiling :=
    Q'.add_le_self_of_nonneg 1 comparison.ceiling
      (Q'.le_of_lt comparison.ceiling_pos)
  factorBound := by
    intro scale
    refine {
      one_le_marginal_ceiling :=
        Q'.add_le_self_of_nonneg 1 comparison.ceiling
          (Q'.le_of_lt comparison.ceiling_pos)
      fixed_marginal_le_growing_reference := ?_
      boundary_spread := fun _boundary => data.spread scale
      boundary_spread_square_le := ?_
      target_raw_projective := ?_
    }
    · let growingMarginal := centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale)
        (scale + 1) (lowSpinCentralReferenceState scale)
      have hbase :=
        comparison.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
          scale
      have hceilingLe : comparison.ceiling ≤
          1 + comparison.ceiling := by
        have hstep := Q'.add_le_self_of_nonneg
          comparison.ceiling 1 Q'.zero_le_one
        exact Q'.le_trans' _ _ _ hstep
          (Q'.le_of_eqv
            (Q'.add_comm_eqv comparison.ceiling 1))
      have hgrowingNonnegative : (0 : Q') ≤ growingMarginal := by
        unfold growingMarginal
        exact centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1) (lowSpinCentralReferenceState scale)
      have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
        hceilingLe hgrowingNonnegative
      exact Q'.le_trans' _ _ _ hbase (by
        simpa only [growingMarginal] using hscale)
    · intro _boundary _hboundary
      exact data.spread_square_le scale
    · intro boundary hboundary
      exact centralHalfAmplitude_targetRawProjective
        (data.spread scale)
        (data.half_amplitude_cross_ratio scale)
        boundary hboundary

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective.centralPhysicalRowMarginal_le_anchoredProjectiveCeiling_mul_targetGivenBoundary_of_rawProjective
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective.CoarseGrowingReferenceBoundaryProjectiveFactorBound.toReferenceBoundaryPosteriorFloor
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective.CoarseGrowingReferenceBoundaryProjectiveFactorBound.toCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective.MatchedDyadicCoarseGrowingReferenceBoundaryProjectiveFactorBound.toCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosteriorProjective.MatchedHalfAmplitudeProjectiveRows.withGrowingRayDominationToProjectiveFactorBound
