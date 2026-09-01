/-
# Boundary-posterior form of the coarse growing repair producer

The positive-boundary amplitude cross-bound isolated for the coarse repair
has an exact probabilistic form.  At every boundary channel whose positive
half-amplitude total is nonzero, it says that the fixed slice-zero spin-one
marginal is bounded by a common ceiling times the posterior probability of
the growing low-spin reference state conditioned on that boundary.

This module proves both translations when the ceiling is at least one.  The
reverse translation also handles zero-total boundary channels constructively:
their left cross-product vanishes, while the right cross-product is
nonnegative.  Thus the remaining producer is now stated entirely as a
uniform boundary-posterior floor.  No such floor is inhabited here, and no
cofinal gap, continuum limit, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
import YMGap.Continuum.BF4PhysicalBoundaryPosterior

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabQuadraticRemainder

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum => hnot (CReal.pos_of_num_pos hnum))

private theorem centralPositiveBoundaryTotalHalfAmplitude_nonnegative_local
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro state _
  exact centralHalfAmplitude_nonnegative
    hw K half state boundary

private theorem fixedHalfSpinOneMarginal_eqv_raw_divPos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≈
      Q'.divPos
        (fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K)
        (fixedHalfPhysicalPartition w K)
        (slabParametricKPhysicalPartition_pos
          (Q'.le_of_lt hw) K (centralExtent 0)) := by
  have hrow :=
    centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := Q'.le_of_lt hw) (K := K) (half := 0)
      (source := centralLowerSpinCubeState 1)
      (centralLowerSpinCubeState_mem_centralHalfStates hK)
  simpa only [fixedHalfSpinOneRawRow, fixedHalfPhysicalPartition,
    centralPhysicalPositiveRawRowMass,
    centralPhysicalFiniteVacuumSectorPartitionReciprocal,
    Q'.divPos] using hrow

private theorem ceiling_mul_reference_posterior_eqv_divPos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} {volume : Nat}
    (ceiling : Q') (boundary : EdgeLabelling)
    (htotal :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w (Q'.le_of_lt hw) K (volume + 1) boundary) :
    ceiling *
        centralTargetGivenBoundary
          w (Q'.le_of_lt hw) K (volume + 1)
          boundary htotal (lowSpinCentralReferenceState volume) ≈
      Q'.divPos
        (ceiling *
          centralHalfAmplitude w K (volume + 1)
            (lowSpinCentralReferenceState volume) boundary)
        (centralPositiveBoundaryTotalHalfAmplitude
          w (Q'.le_of_lt hw) K (volume + 1) boundary)
        htotal := by
  unfold centralTargetGivenBoundary finiteStateGivenChannel Q'.divPos
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv ceiling
      (centralHalfAmplitude w K (volume + 1)
        (lowSpinCentralReferenceState volume) boundary)
      (Q'.recipPos
        (centralPositiveBoundaryTotalHalfAmplitude
          w (Q'.le_of_lt hw) K (volume + 1) boundary)
        htotal))

/-! ## 1. The exact posterior producer -/

/-- A uniform lower bound on the posterior probability of the growing
low-spin reference state, measured against the fixed slice-zero spin-one
marginal.  The ceiling is required to be at least one so zero-total boundary
channels can be restored when translating back to the division-free cross
bound. -/
structure CoarseGrowingReferenceBoundaryPosteriorFloor
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  one_le_ceiling : (1 : Q') ≤ ceiling
  reference_posterior_floor : ∀ boundary,
    boundary ∈ centralBoundaryChannels K (volume + 1) →
      ∀ htotal :
        (0 : Q') <
          centralPositiveBoundaryTotalHalfAmplitude
            w (Q'.le_of_lt hw) K (volume + 1) boundary,
        centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K 0
            (centralLowerSpinCubeState 1) ≤
          ceiling *
            centralTargetGivenBoundary
              w (Q'.le_of_lt hw) K (volume + 1)
              boundary htotal
              (lowSpinCentralReferenceState volume)

/-- The posterior floor cross-multiplies to the retained positive-boundary
amplitude producer, including boundary channels with zero positive total. -/
def CoarseGrowingReferenceBoundaryPosteriorFloor.toPositiveBoundaryHalfAmplitudeCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingReferenceBoundaryPosteriorFloor
      w hw K hK volume ceiling) :
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
      w hw K hK volume ceiling := by
  refine {
    weighted_positive_boundary_cross := ?_
  }
  intro boundary hboundary
  let hw0 := Q'.le_of_lt hw
  let fixedRaw := fixedHalfSpinOneRawRow w hw0 K
  let fixedPartition := fixedHalfPhysicalPartition w K
  let total := centralPositiveBoundaryTotalHalfAmplitude
    w hw0 K (volume + 1) boundary
  let referenceAmplitude := centralHalfAmplitude
    w K (volume + 1) (lowSpinCentralReferenceState volume) boundary
  have hfixedPartition : (0 : Q') < fixedPartition := by
    unfold fixedPartition fixedHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      hw0 K (centralExtent 0)
  by_cases htotal : (0 : Q') < total
  · have hposterior :=
      bound.reference_posterior_floor boundary hboundary htotal
    have hfixed :
        centralPhysicalRowMarginal
            w hw0 K 0 (centralLowerSpinCubeState 1) ≈
          Q'.divPos fixedRaw fixedPartition hfixedPartition := by
      simpa only [hw0, fixedRaw, fixedPartition] using
        (fixedHalfSpinOneMarginal_eqv_raw_divPos hw hK)
    have hscaled :
        ceiling *
            centralTargetGivenBoundary
              w hw0 K (volume + 1) boundary htotal
              (lowSpinCentralReferenceState volume) ≈
          Q'.divPos (ceiling * referenceAmplitude) total htotal := by
      simpa only [hw0, total, referenceAmplitude] using
        (ceiling_mul_reference_posterior_eqv_divPos
          hw ceiling boundary htotal)
    have hquotient :
        Q'.divPos fixedRaw fixedPartition hfixedPartition ≤
          Q'.divPos (ceiling * referenceAmplitude) total htotal :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hfixed)
        (Q'.le_trans' _ _ _ hposterior (Q'.le_of_eqv hscaled))
    have hcross :=
      (divPos_le_divPos_iff_cross
        fixedRaw fixedPartition (ceiling * referenceAmplitude) total
        hfixedPartition htotal).mp hquotient
    exact Q'.le_trans' _ _ _ hcross
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv ceiling referenceAmplitude fixedPartition))
  · have htotalNonnegative : (0 : Q') ≤ total := by
      unfold total
      exact centralPositiveBoundaryTotalHalfAmplitude_nonnegative_local
        hw0 K (volume + 1) boundary
    have htotalNonpositive : total ≤ 0 :=
      q_nonpos_of_not_pos_local htotal
    have htotalZero : total ≈ 0 :=
      Q'.eqv_of_le_le htotalNonpositive htotalNonnegative
    have hleftZero : fixedRaw * total ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left fixedRaw total 0 htotalZero)
        (Q'.mul_zero_eqv fixedRaw)
    have hceilingNonnegative : (0 : Q') ≤ ceiling :=
      Q'.le_trans' _ _ _ Q'.zero_le_one bound.one_le_ceiling
    have hreferenceNonnegative : (0 : Q') ≤ referenceAmplitude := by
      unfold referenceAmplitude
      exact centralHalfAmplitude_nonnegative
        hw0 K (volume + 1)
          (lowSpinCentralReferenceState volume) boundary
    have hfixedPartitionNonnegative : (0 : Q') ≤ fixedPartition :=
      Q'.le_of_lt hfixedPartition
    have hrightNonnegative :
        (0 : Q') ≤ ceiling * (referenceAmplitude * fixedPartition) :=
      Q'.mul_nonneg _ _ hceilingNonnegative
        (Q'.mul_nonneg _ _ hreferenceNonnegative
          hfixedPartitionNonnegative)
    exact Q'.le_trans' _ 0 _
      (Q'.le_of_eqv hleftZero) hrightNonnegative

/-- Conversely, a positive-boundary amplitude cross-bound and the natural
`1 ≤ ceiling` normalization recover the posterior floor at every positive
boundary channel. -/
def CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toReferenceBoundaryPosteriorFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
      w hw K hK volume ceiling)
    (hone : (1 : Q') ≤ ceiling) :
    CoarseGrowingReferenceBoundaryPosteriorFloor
      w hw K hK volume ceiling := by
  refine {
    one_le_ceiling := hone
    reference_posterior_floor := ?_
  }
  intro boundary hboundary htotal
  let hw0 := Q'.le_of_lt hw
  let fixedRaw := fixedHalfSpinOneRawRow w hw0 K
  let fixedPartition := fixedHalfPhysicalPartition w K
  let total := centralPositiveBoundaryTotalHalfAmplitude
    w hw0 K (volume + 1) boundary
  let referenceAmplitude := centralHalfAmplitude
    w K (volume + 1) (lowSpinCentralReferenceState volume) boundary
  have hfixedPartition : (0 : Q') < fixedPartition := by
    unfold fixedPartition fixedHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      hw0 K (centralExtent 0)
  have hfixed :
      centralPhysicalRowMarginal
          w hw0 K 0 (centralLowerSpinCubeState 1) ≈
        Q'.divPos fixedRaw fixedPartition hfixedPartition := by
    simpa only [hw0, fixedRaw, fixedPartition] using
      (fixedHalfSpinOneMarginal_eqv_raw_divPos hw hK)
  have hscaled :
      ceiling *
          centralTargetGivenBoundary
            w hw0 K (volume + 1) boundary htotal
            (lowSpinCentralReferenceState volume) ≈
        Q'.divPos (ceiling * referenceAmplitude) total htotal := by
    simpa only [hw0, total, referenceAmplitude] using
      (ceiling_mul_reference_posterior_eqv_divPos
        hw ceiling boundary htotal)
  have hcrossBase :=
    bound.weighted_positive_boundary_cross boundary hboundary
  have hcross :
      fixedRaw * total ≤
        (ceiling * referenceAmplitude) * fixedPartition :=
    Q'.le_trans' _ _ _ hcrossBase
      (Q'.ge_of_eqv
        (Q'.mul_assoc_eqv ceiling referenceAmplitude fixedPartition))
  have hquotient :
      Q'.divPos fixedRaw fixedPartition hfixedPartition ≤
        Q'.divPos (ceiling * referenceAmplitude) total htotal :=
    (divPos_le_divPos_iff_cross
      fixedRaw fixedPartition (ceiling * referenceAmplitude) total
      hfixedPartition htotal).mpr hcross
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfixed)
    (Q'.le_trans' _ _ _ hquotient (Q'.ge_of_eqv hscaled))

/-! ## 2. Matched-diagonal translations -/

structure MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  posteriorFloor : ∀ scale,
    CoarseGrowingReferenceBoundaryPosteriorFloor
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

def MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor.toPositiveBoundaryHalfAmplitudeCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor bridge) :
    MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
      bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  positiveBoundaryBound := fun scale =>
    CoarseGrowingReferenceBoundaryPosteriorFloor.toPositiveBoundaryHalfAmplitudeCrossBound
      (bound.posteriorFloor scale)

def MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toReferenceBoundaryPosteriorFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
        bridge) :
    MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  posteriorFloor := fun scale =>
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toReferenceBoundaryPosteriorFloor
      (bound.positiveBoundaryBound scale) bound.one_le_ceiling

def MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor.toCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor bridge) :
    MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge :=
  bound.toPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior.CoarseGrowingReferenceBoundaryPosteriorFloor.toPositiveBoundaryHalfAmplitudeCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior.CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toReferenceBoundaryPosteriorFloor
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior.MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor.toPositiveBoundaryHalfAmplitudeCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior.MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor.toCompletionColumnCrossBound
