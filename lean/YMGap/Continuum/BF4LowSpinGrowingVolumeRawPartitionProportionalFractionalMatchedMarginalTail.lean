/-
# Matched fixed-spin marginal tail from optimal fractional switching

A uniform bound on the optimal proportional fractional ceiling gives more
than a raw crossed inequality: after the already proved positive-partition
cross multiplication, it forces the matched fixed-half spin-one marginal to
vanish with an explicit located modulus.

This module also isolates the remaining complete-ray obligation.  A separate
uniform comparison of the whole excited spin-cube ray with its first spin-one
atom combines with the aggregate-ratio bound to inhabit the existing matched
ray-domination gate.  Only that additional comparison promotes the scalar
tail to ray-mass tail zero and its assigned-ratio no-go consequence.

No aggregate-ratio bound or complete-ray comparison is inhabited here.  No
cofinal contraction, operator gap, continuum limit, or Clay theorem is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact normalized scalar consequence -/

/-- At one finite datum, bounding the aggregate occurrence-total ratio is
exactly the crossed raw-row/partition inequality. -/
theorem fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_cross
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (ceiling : Q') (volume : Nat) :
    fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume ≤ ceiling ↔
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          growingHalfPhysicalPartition w K volume ≤
        (ceiling *
            growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K volume) *
          fixedHalfPhysicalPartition w K := by
  let sourceTotal :=
    listQSum
      (fixedGrowingRawPartitionSourceIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionSourceIndices
        w (Q'.le_of_lt hw) K volume)
  let targetTotal :=
    listQSum
      (fixedGrowingRawPartitionTargetIndexWeight
        w (Q'.le_of_lt hw) K volume)
      (fixedGrowingRawPartitionTargetIndices
        w (Q'.le_of_lt hw) K volume)
  let fixedCross :=
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
      growingHalfPhysicalPartition w K volume
  let growingCross :=
    growingHalfSpinOneRawRow w (Q'.le_of_lt hw) K volume *
      fixedHalfPhysicalPartition w K
  have hsource : sourceTotal ≈ fixedCross := by
    unfold sourceTotal fixedCross
    exact fixedGrowingRawPartitionSourceIndexSum_eqv_cross
      (Q'.le_of_lt hw) K volume
  have htarget : targetTotal ≈ growingCross := by
    unfold targetTotal growingCross
    exact fixedGrowingRawPartitionTargetIndexSum_eqv_cross
      (Q'.le_of_lt hw) K volume
  have htargetPos : (0 : Q') < targetTotal := by
    unfold targetTotal
    exact fixedGrowingRawPartitionTargetIndexTotal_pos hw hK volume
  have hratioCancel :
      fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume *
          targetTotal ≈
        sourceTotal := by
    unfold fixedGrowingRawPartitionCrossTotalRatio sourceTotal targetTotal
    exact Q'.divPos_mul_eqv _ _ _
  have hscaledTarget :
      ceiling * targetTotal ≈
        (ceiling *
            growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K volume) *
          fixedHalfPhysicalPartition w K := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ceiling targetTotal growingCross htarget)
      (by
        unfold growingCross
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv ceiling
            (growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K volume)
            (fixedHalfPhysicalPartition w K)))
  constructor
  · intro hratio
    have hscaled :=
      Q'.mul_le_mul_of_nonneg_right _ _ targetTotal hratio
        (Q'.le_of_lt htargetPos)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsource)
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv hratioCancel)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hscaledTarget)))
  · intro hcross
    apply Q'.divPos_le_of_le_mul sourceTotal targetTotal htargetPos
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsource)
      (Q'.le_trans' _ _ _ hcross (Q'.ge_of_eqv hscaledTarget))

/-- Consequently the aggregate ratio bound is pointwise equivalent to the
normalized fixed-half/growing-half spin-one comparison.  The fractional
allocation introduces no additional analytic slack. -/
theorem fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_marginal
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (ceiling : Q') (volume : Nat) :
    fixedGrowingRawPartitionCrossTotalRatio w hw K hK volume ≤ ceiling ↔
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
        ceiling *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K (volume + 1)
            (lowSpinCentralReferenceState volume) := by
  have hratio :=
    fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_cross
      hw hK ceiling volume
  have hnormalized :=
    fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
      hw hK ceiling volume
  constructor
  · intro h
    exact hnormalized.mpr (hratio.mp h)
  · intro h
    exact hratio.mpr (hnormalized.mp h)

/-- On the matched trajectory, the displayed aggregate-ratio sequence has no
hidden combinatorial slack: its pointwise ceiling condition is exactly the
normalized fixed/growing spin-one comparison. -/
theorem matchedCrossTotalRatio_le_ceiling_iff_fixedHalfSpinOneMarginal
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ceiling : Q') (scale : Nat) :
    matchedCrossTotalRatio bridge scale ≤ ceiling ↔
      centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale) 0
          (centralLowerSpinCubeState 1) ≤
        ceiling *
          centralPhysicalRowMarginal
            (matchedAllSpinWeight family coupling scale)
            (Q'.le_of_lt
              (matchedAllSpinWeight_pos family coupling scale))
            (matchedAllSpinCutoff family coupling scale)
            (scale + 1)
            (lowSpinCentralReferenceState scale) := by
  let w := matchedAllSpinWeight family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  have hw : (0 : Q') < w :=
    matchedAllSpinWeight_pos family coupling scale
  have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
  have hfinite :=
    fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_marginal
      hw hK ceiling scale
  simpa only [matchedCrossTotalRatio, w, K] using hfinite

namespace MatchedDyadicCrossTotalRatioBound

/-- The matched raw cross supplied by the optimal fractional kernel is
equivalent to the required normalized fixed-half/growing-half spin-one
comparison. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCrossTotalRatioBound bridge)
    (scale : Nat) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) 0
        (centralLowerSpinCubeState 1) ≤
      bound.ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale) := by
  let w := matchedAllSpinWeight family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  have hw : (0 : Q') < w :=
    matchedAllSpinWeight_pos family coupling scale
  have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
  have hcross :
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          growingHalfPhysicalPartition w K scale ≤
        (bound.ceiling *
            growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K scale) *
          fixedHalfPhysicalPartition w K := by
    simpa only [w, K] using bound.rawCross scale
  have hnormalized :=
    (fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
      hw hK bound.ceiling scale).mpr hcross
  simpa only [w, K] using hnormalized

end MatchedDyadicCrossTotalRatioBound

/-! ## 2. Located tail zero for the fixed spin-one atom -/

/-- Located epsilon/rate tail-zero data for only the matched fixed-half
spin-one marginal.  This is intentionally weaker than tail zero of the full
excited spin-cube ray. -/
structure MatchedDyadicFixedHalfSpinOneMarginalTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  rate : Q' → Nat
  marginal_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ scale, rate epsilon ≤ scale →
      centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale) 0
          (centralLowerSpinCubeState 1) ≤
        epsilon

namespace MatchedDyadicCrossTotalRatioBound

/-- A uniform optimal-fractional aggregate-ratio bound forces the fixed-half
spin-one marginal to zero with rate `den (epsilon / ceiling)`. -/
def toFixedHalfSpinOneMarginalTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCrossTotalRatioBound bridge) :
    MatchedDyadicFixedHalfSpinOneMarginalTailZero bridge where
  rate epsilon :=
    (Q'.divPos epsilon bound.ceiling
      (Q'.pos_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
        bound.one_le_ceiling)).den
  marginal_le := by
    intro epsilon hepsilon scale hscale
    let w := matchedAllSpinWeight family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    have hceiling : (0 : Q') < bound.ceiling :=
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
        bound.one_le_ceiling
    let delta := Q'.divPos epsilon bound.ceiling hceiling
    have hw : (0 : Q') < w :=
      matchedAllSpinWeight_pos family coupling scale
    have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
    have hdelta : (0 : Q') < delta := by
      unfold delta
      exact Q'.divPos_pos epsilon bound.ceiling hceiling hepsilon
    have hscale' : delta.den ≤ scale := by
      simpa only [delta, hceiling] using hscale
    have hgrowing := lowSpinCentralKReferenceMarginal_le_epsilon
      w hw K hK delta hdelta scale hscale'
    have hscaled :
        bound.ceiling *
            centralPhysicalRowMarginal
              w (Q'.le_of_lt hw) K (scale + 1)
                (lowSpinCentralReferenceState scale) ≤
          bound.ceiling * delta :=
      Q'.mul_le_mul_of_nonneg_left _ _ bound.ceiling hgrowing
        (Q'.le_of_lt hceiling)
    have hcollapse : bound.ceiling * delta ≈ epsilon := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv bound.ceiling delta)
        (by
          unfold delta
          exact Q'.divPos_mul_eqv epsilon bound.ceiling hceiling)
    exact Q'.le_trans' _ _ _
      (by
        simpa only [w, K] using
          (fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
            bound scale))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse))

end MatchedDyadicCrossTotalRatioBound

/-! ## 3. The exact remaining complete-ray bridge -/

/-- A uniform comparison of the complete matched excited spin-cube ray with
its first spin-one atom.  This is the remaining sum-compression input and is
intentionally uninhabited here. -/
structure MatchedDyadicExcitedSpinCubeRayAtomCompression
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  rayMass_le_ceiling_mul_fixedSpinOne : ∀ scale,
    centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) ≤
      ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale) 0
          (centralLowerSpinCubeState 1)

/-- The aggregate-ratio bound and complete-ray atom compression combine to
inhabit the existing growing-reference ray-domination gate. -/
def toMatchedDyadicLowSpinGrowingVolumeRayDomination
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCrossTotalRatioBound bridge)
    (compression :
      MatchedDyadicExcitedSpinCubeRayAtomCompression bridge) :
    MatchedDyadicLowSpinGrowingVolumeRayDomination bridge where
  ceiling := compression.ceiling * bound.ceiling
  ceiling_pos := Q'.mul_pos compression.ceiling_pos
    (Q'.pos_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
      bound.one_le_ceiling)
  rayMass_le_ceiling_mul_growingReference := by
    intro scale
    have hfixed :=
      MatchedDyadicCrossTotalRatioBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
        bound scale
    have hscaled :=
      Q'.mul_le_mul_of_nonneg_left _ _ compression.ceiling hfixed
        (Q'.le_of_lt compression.ceiling_pos)
    exact Q'.le_trans' _ _ _
      (compression.rayMass_le_ceiling_mul_fixedSpinOne scale)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.ge_of_eqv
          (Q'.mul_assoc_eqv compression.ceiling bound.ceiling
            (centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (Q'.le_of_lt
                (matchedAllSpinWeight_pos family coupling scale))
              (matchedAllSpinCutoff family coupling scale)
              (scale + 1)
              (lowSpinCentralReferenceState scale)))))

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.fixedGrowingRawPartitionCrossTotalRatio_le_ceiling_iff_marginal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.matchedCrossTotalRatio_le_ceiling_iff_fixedHalfSpinOneMarginal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.MatchedDyadicCrossTotalRatioBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.MatchedDyadicCrossTotalRatioBound.toFixedHalfSpinOneMarginalTailZero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedMarginalTail.toMatchedDyadicLowSpinGrowingVolumeRayDomination
