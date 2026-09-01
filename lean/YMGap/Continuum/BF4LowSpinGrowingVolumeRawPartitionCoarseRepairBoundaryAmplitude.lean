/-
# Boundary-amplitude producer for coarse completion columns

The coarse completion column has an exact Gram factorization.  At fixed
boundary and positive target it is the boundary weight times the total
half-amplitude over all lower states times the target half-amplitude.

Consequently, a target-independent comparison between that total amplitude
and the literal low-spin reference amplitude is sufficient for the full
pointwise completion-column Harnack estimate.  This module names that sharper
analytic interface and compiles it constructively, including on the matched
dyadic trajectory.

The boundary-amplitude comparison is not inhabited here.  No cofinal gap,
continuum limit, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem mul_column_scale_reorder_local
    (a b c d : Q') :
    (a * b) * (c * d) ≈ a * (c * (b * d)) := by
  show ((a * b) * (c * d)).num *
      ((a * (c * (b * d))).den : Int) =
    (a * (c * (b * d))).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

private theorem mul_column_target_reorder_local
    (a b c d e : Q') :
    (a * (b * c)) * (d * e) ≈
      a * ((d * (b * e)) * c) := by
  show ((a * (b * c)) * (d * e)).num *
      ((a * ((d * (b * e)) * c)).den : Int) =
    (a * ((d * (b * e)) * c)).num *
      (((a * (b * c)) * (d * e)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-! ## 1. Exact Gram factorization of one completion column -/

/-- Total unfiltered half-amplitude visible through one boundary channel. -/
def growingBoundaryTotalHalfAmplitude
    (w : Q') (K volume : Nat) (boundary : EdgeLabelling) : Q' :=
  listQSum
    (fun lower =>
      centralHalfAmplitude w K (volume + 1) lower boundary)
    (centralHalfStates K (volume + 1))

theorem growingBoundaryTotalHalfAmplitude_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    (boundary : EdgeLabelling) :
    (0 : Q') ≤
      growingBoundaryTotalHalfAmplitude w K volume boundary := by
  unfold growingBoundaryTotalHalfAmplitude
  apply listQSum_nonnegative_on
  intro lower _hlower
  exact centralHalfAmplitude_nonnegative
    hw K (volume + 1) lower boundary

/-- A literal completion column is one common Gram factor times the total
half-amplitude over its lower-state coordinate. -/
theorem growingCompletionColumnWeight_eqv_boundaryAmplitudeFactorization
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {target boundary : EdgeLabelling}
    (htarget : target ∈
      centralPositiveHalfStates w hw K (volume + 1))
    (hboundary : boundary ∈
      centralBoundaryChannels K (volume + 1)) :
    growingCompletionColumnWeight
        w K volume (target, boundary) ≈
      centralBoundaryWeight w K (volume + 1) boundary *
        (growingBoundaryTotalHalfAmplitude w K volume boundary *
          centralHalfAmplitude
            w K (volume + 1) target boundary) := by
  have htargetHalf :=
    (mem_centralPositiveHalfStates_iff.mp htarget).1
  have hterms :
      growingCompletionColumnWeight w K volume (target, boundary) ≈
        listQSum
          (fun lower =>
            centralBoundaryWeight w K (volume + 1) boundary *
              (centralHalfAmplitude
                  w K (volume + 1) lower boundary *
                centralHalfAmplitude
                  w K (volume + 1) target boundary))
          (centralHalfStates K (volume + 1)) := by
    unfold growingCompletionColumnWeight
      centralPositiveCompletionWeight
    apply listQSum_congr_on
    intro lower hlower
    exact centralPhysicalTerm_eq_gram_integrand
      w hlower hboundary htargetHalf
  exact Q'.eqv_trans _ _ _ hterms
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (centralBoundaryWeight w K (volume + 1) boundary)
        (fun lower =>
          centralHalfAmplitude w K (volume + 1) lower boundary *
            centralHalfAmplitude w K (volume + 1) target boundary)
        (centralHalfStates K (volume + 1)))
      (Q'.mul_eqv_congr_left
        (centralBoundaryWeight w K (volume + 1) boundary) _ _
        (Q'.eqv_trans _ _ _
          (listQSum_mul_right
            (fun lower =>
              centralHalfAmplitude w K (volume + 1) lower boundary)
            (centralHalfAmplitude w K (volume + 1) target boundary)
            (centralHalfStates K (volume + 1)))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _)))))

/-! ## 2. A target-independent sufficient analytic producer -/

/-- A boundary-channel comparison sufficient for the pointwise completion-
column Harnack estimate.  It compares the total lower-state amplitude with
the amplitude of the literal low-spin reference state. -/
structure CoarseGrowingBoundaryHalfAmplitudeCrossBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_boundary_cross : ∀ boundary,
    boundary ∈ centralBoundaryChannels K (volume + 1) →
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          growingBoundaryTotalHalfAmplitude w K volume boundary ≤
        ceiling *
          (centralHalfAmplitude w K (volume + 1)
              (lowSpinCentralReferenceState volume) boundary *
            fixedHalfPhysicalPartition w K)

/-- The target-independent boundary-amplitude comparison compiles to the
full pointwise completion-column Harnack producer. -/
def CoarseGrowingBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingBoundaryHalfAmplitudeCrossBound
      w hw K hK volume ceiling) :
    CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume ceiling where
  weighted_column_cross := by
    intro completion hcompletion
    let hw0 := Q'.le_of_lt hw
    have hparts := (mem_cartesian_iff
      (centralPositiveHalfStates w hw0 K (volume + 1))
      (centralBoundaryChannels K (volume + 1))
      completion).mp hcompletion
    let target := completion.1
    let boundary := completion.2
    let fixedRaw := fixedHalfSpinOneRawRow w hw0 K
    let fixedPartition := fixedHalfPhysicalPartition w K
    let total := growingBoundaryTotalHalfAmplitude w K volume boundary
    let boundaryWeight := centralBoundaryWeight w K (volume + 1) boundary
    let targetAmplitude :=
      centralHalfAmplitude w K (volume + 1) target boundary
    let referenceAmplitude :=
      centralHalfAmplitude w K (volume + 1)
        (lowSpinCentralReferenceState volume) boundary
    have hcolumn :=
      growingCompletionColumnWeight_eqv_boundaryAmplitudeFactorization
        hparts.1 hparts.2
    have hrefPositive :=
      (lowSpinCentralKPositiveRawReplication
        w hw K hK volume).reference_mem
    have hrefHalf :=
      (mem_centralPositiveHalfStates_iff.mp hrefPositive).1
    have href := centralPhysicalTerm_eq_gram_integrand
      w hrefHalf hparts.2
        (mem_centralPositiveHalfStates_iff.mp hparts.1).1
    have hcommon : (0 : Q') ≤ boundaryWeight * targetAmplitude :=
      Q'.mul_nonneg _ _
        (centralBoundaryWeight_nonnegative_on hw0 boundary hparts.2)
        (centralHalfAmplitude_nonnegative
          hw0 K (volume + 1) target boundary)
    have hboundary := bound.weighted_boundary_cross boundary hparts.2
    have hscaled :
        (fixedRaw * total) * (boundaryWeight * targetAmplitude) ≤
          (ceiling * (referenceAmplitude * fixedPartition)) *
            (boundaryWeight * targetAmplitude) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hboundary hcommon
    have hleft :
        fixedRaw *
            growingCompletionColumnWeight w K volume completion ≈
          (fixedRaw * total) *
            (boundaryWeight * targetAmplitude) := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left fixedRaw _ _ (by
          simpa only [target, boundary] using hcolumn))
        (Q'.eqv_symm
          (mul_column_scale_reorder_local
            fixedRaw total boundaryWeight targetAmplitude))
    have hright :
        (ceiling * (referenceAmplitude * fixedPartition)) *
            (boundaryWeight * targetAmplitude) ≈
          ceiling *
            (centralPositiveCompletionWeight w K (volume + 1)
                (lowSpinCentralReferenceState volume) completion *
              fixedPartition) := by
      refine Q'.eqv_trans _ _ _
        (mul_column_target_reorder_local
          ceiling referenceAmplitude fixedPartition
          boundaryWeight targetAmplitude) ?_
      exact Q'.mul_eqv_congr_left ceiling _ _
        (Q'.mul_eqv_congr_right _ _ fixedPartition
          (Q'.eqv_symm (by
            simpa only [target, boundary] using href)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-! ## 3. Matched-diagonal compiler -/

structure MatchedDyadicCoarseGrowingBoundaryHalfAmplitudeCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  boundaryBound : ∀ scale,
    CoarseGrowingBoundaryHalfAmplitudeCrossBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

def MatchedDyadicCoarseGrowingBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound : MatchedDyadicCoarseGrowingBoundaryHalfAmplitudeCrossBound bridge) :
    MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  columnBound := fun scale =>
    CoarseGrowingBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
      (bound.boundaryBound scale)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude.growingCompletionColumnWeight_eqv_boundaryAmplitudeFactorization
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude.CoarseGrowingBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude.MatchedDyadicCoarseGrowingBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
