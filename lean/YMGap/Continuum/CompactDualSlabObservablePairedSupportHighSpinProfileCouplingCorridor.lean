/-
# Complete observable inverse fibers on a strong-coupling corridor

The exact residual-core payment is `2*w^3` per peeled copy.  Monotonicity in
the coupling proves that, throughout

  0 < w <= 1/400,

this coefficient is no larger than the production-anchor face coefficient
`1/32,000,000`.  Consequently every unit of both the high-spin exterior and
the low-spin core pays the same anchor factor.  The existing source-independent
global code has at most `20,480,000^mass` values, so the complete fixed-terminal,
fixed-total-mass fiber contracts at

  (20,480,000 / 32,000,000)^mass = (16/25)^mass.

This eliminates the finite-core prefactor on the whole explicit corridor,
without a core-coordinate sum.  It is a genuine arbitrary-cutoff and
arbitrary-finite-volume theorem for the stated coupling interval, not a
continuum or weak-coupling result.

Constructive contract: rational power monotonicity, the exact pointwise
coupling telescope, and the existing injective global entropy code only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact corridor endpoint -/

/-- Below the production coupling, the threshold-zero successor coefficient
is no larger than its exact production-anchor value. -/
theorem exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
    {w : Q'} (hw0 : (0 : Q') <= w) (hwAnchor : w <= anchorCoupling) :
    exteriorFaceCoefficient w 0 <= anchorFaceCoefficient := by
  have hpower : qpow w 3 <= qpow anchorCoupling 3 :=
    qpow_mono hw0 hwAnchor 3
  have hscaled :
      Q'.ofNat 2 * qpow w 3 <=
        Q'.ofNat 2 * qpow anchorCoupling 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower (zero_le_ofNat 2)
  have hendpoint :
      Q'.ofNat 2 * qpow anchorCoupling 3 <=
        anchorFaceCoefficient := by
    unfold anchorCoupling anchorFaceCoefficient
    decide
  unfold exteriorFaceCoefficient
  simpa only [Nat.zero_add] using Q'.le_trans' _ _ _ hscaled hendpoint

private theorem pow_le_pow_local {left right : Q'}
    (hleft : (0 : Q') <= left) (hle : left <= right) :
    forall exponent : Nat, left ^ exponent <= right ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hright : (0 : Q') <= right :=
        Q'.le_trans' _ _ _ hleft hle
      have hpower := pow_le_pow_local hleft hle exponent
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hle
          (Q'.pow_nonneg left hleft exponent))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hpower hright)

/-- Whenever the exact residual coefficient is no larger than the anchor
coefficient, exterior and core powers together are bounded by one anchor
power of their total multiplicity.  This is the low-level interface an RG or
coercivity theorem must supply; it does not assume how the coefficient bound
was obtained. -/
theorem highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
    {w : Q'} (hw0 : (0 : Q') <= w)
    (hzero : exteriorFaceCoefficient w 0 <= anchorFaceCoefficient)
    (exterior core : Nat) :
    anchorFaceCoefficient ^ exterior *
        exteriorFaceCoefficient w 0 ^ core <=
      anchorFaceCoefficient ^ (exterior + core) := by
  have hcore := pow_le_pow_local
    (exteriorFaceCoefficient_nonnegative hw0 0)
    hzero core
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hcore
    (Q'.pow_nonneg anchorFaceCoefficient (by decide) exterior)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.pow_add_eqv anchorFaceCoefficient exterior core)))

/-- Corridor specialization of the coefficient-level power comparison. -/
theorem highSpinProfileCoefficient_le_anchorPower
    {w : Q'} (hw0 : (0 : Q') <= w) (hwAnchor : w <= anchorCoupling)
    (exterior core : Nat) :
    anchorFaceCoefficient ^ exterior *
        exteriorFaceCoefficient w 0 ^ core <=
      anchorFaceCoefficient ^ (exterior + core) := by
  exact highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
    hw0 (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient hw0 hwAnchor)
      exterior core

/-! ## 2. Complete fixed-terminal, fixed-mass corridor fiber -/

/-- **Coefficient-level inverse-fiber theorem.**  Every duplicate-free
observable source family sharing one accepted terminal and one complete trace
mass has the same strict `(16/25)^mass` bound whenever its exact residual
coefficient is bounded by the anchor coefficient. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hmass : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 = mass) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        sources <=
      slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  unfold slabObservablePairedGlobalEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact
      slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_length_le
        D rootFaceId targetFaceId mass htarget terminal sources hsources
          hterminal hmass
  · unfold anchorFaceCoefficient
    decide
  · exact slabAcceptedTwoReplicaStateWeight_nonnegative D terminal
  · intro source hsource
    let result := slabObservablePairTargetSupportCanonicalHighSpinProfile
      D rootFaceId targetFaceId htarget source.1 source.2
    have hweight :=
      slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
        D hw0 hw1 rootFaceId targetFaceId htarget source.1 source.2
    dsimp only at hweight
    have hforget :=
      slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
        D rootFaceId targetFaceId htarget source.1 source.2
    have hterminalResult : result.1 = terminal := by
      exact (congrArg Prod.fst hforget).trans
        (hterminal source hsource)
    have htraceResult : result.2.1 =
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 :=
      congrArg Prod.snd hforget
    have hprofile := slabAcceptedPairCanonicalHighSpinProfile_traceMass
      D (anchorPaidExteriorThreshold D.coupling)
        (slabTwoReplicaTargetSupportComponent D.extent
          source.1.1.1.1 source.1.2.1.1 targetFaceId)
        (fun faceId hface =>
          slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
            D rootFaceId targetFaceId htarget source.1 source.2 faceId hface)
        (slabObservableTwoReplicaPairToAcceptedState source.1)
    have hprofileResult :
        slabAcceptedPairedPeelTraceMass result.2.1 =
          result.2.2.1 + result.2.2.2 := by
      simpa only [result,
        slabObservablePairTargetSupportCanonicalHighSpinProfile] using hprofile
    have hmassResult : result.2.2.1 + result.2.2.2 = mass := by
      rw [← hprofileResult]
      rw [htraceResult]
      exact hmass source hsource
    have hcoefficient :=
      highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
        (Q'.le_of_lt hw0) hzero result.2.2.1 result.2.2.2
    rw [hmassResult] at hcoefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcoefficient
      (slabAcceptedTwoReplicaStateWeight_nonnegative D result.1)
    rw [hterminalResult] at hweight hscaled
    exact Q'.le_trans' _ _ _ hweight hscaled

/-- **Corridor inverse-fiber theorem.**  Every duplicate-free observable
source family sharing one accepted terminal and one complete trace mass has
the same strict `(16/25)^mass` bound as at the production anchor, uniformly
for `0 < coupling <= 1/400`. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_corridor
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hmass : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 = mass) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        sources <=
      slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  exact
    slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_of_zeroCoefficient_le
      D hw0 hw1
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hw0) hwAnchor)
        rootFaceId targetFaceId mass htarget terminal sources hsources
          hterminal hmass

#print axioms exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
#print axioms highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
#print axioms highSpinProfileCoefficient_le_anchorPower
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_of_zeroCoefficient_le
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_corridor

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor
