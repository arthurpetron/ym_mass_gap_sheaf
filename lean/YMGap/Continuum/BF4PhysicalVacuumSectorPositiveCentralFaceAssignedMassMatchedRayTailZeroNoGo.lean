/-
# Tail-zero no-go for the matched assigned-spin ratio route

This module names an epsilon/rate statement saying that the displayed
matched excited spin-cube ray mass tends to zero.  It does not inhabit that
statement.  Instead it proves the exact branch consequence: such tail-zero
data are incompatible with any common matched assigned-ratio ceiling,
because the cofinal feasibility gate forces the same ray mass above a fixed
strictly positive reciprocal floor.

Thus a future proof of ray-mass tail zero will constructively close this
particular terminal-reference route as a no-go, rather than being mistaken
for a gap theorem.  No tail-zero estimate, congestion bound, finite gap,
physical normalization, continuum theory, or Clay conclusion is proved here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative

/-! ## 1. The missing asymptotic producer -/

/-- Located epsilon/rate tail-zero data for the exact matched excited
spin-cube ray mass.  This structure is intentionally uninhabited here. -/
structure MatchedDyadicExcitedSpinCubeRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  rate : Q' → Nat
  rayMass_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ scale, rate epsilon ≤ scale →
      centralLowerExcitedSpinCubeRayMass
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) ≤
        epsilon

private theorem q_half_mul_lt_self_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    HalfPow.half * value < value := by
  have hscaled :=
    YMGap.Continuum.ClusteringImpliesGap.mul_lt_mul_of_pos_right
      hvalue (show HalfPow.half < (1 : Q') by decide)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hscaled
    (Q'.le_of_eqv (Q'.one_mul_eqv value))

/-! ## 2. The two asymptotic branches are disjoint -/

/-- A proved matched ray-mass tail-zero estimate would rule out every common
cofinal assigned expectation/weight ratio bound on the same trajectory. -/
theorem tailZero_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (tailZero :
      MatchedDyadicExcitedSpinCubeRayMassTailZero bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) := by
  intro hratio
  obtain ⟨ratio⟩ := hratio
  let floor := Q'.divPos (Q'.mkPos 1 6 (by decide))
    ratio.ratioBound ratio.ratioBound_pos
  have hfloor : (0 : Q') < floor :=
    Q'.divPos_pos _ ratio.ratioBound ratio.ratioBound_pos
      (by decide)
  let epsilon := HalfPow.half * floor
  have hepsilon : (0 : Q') < epsilon :=
    ExpNeg.half_mul_pos floor hfloor
  let scale := max ratio.start (tailZero.rate epsilon)
  have hratioScale : ratio.start ≤ scale := by
    unfold scale
    exact Nat.le_max_left _ _
  have htailScale : tailZero.rate epsilon ≤ scale := by
    unfold scale
    exact Nat.le_max_right _ _
  have hlower := ratio.reciprocalRatioFloor_le_rayMass_tail
    scale hratioScale
  have hupper := tailZero.rayMass_le epsilon hepsilon scale htailScale
  have hcollapsed : floor ≤ epsilon :=
    Q'.le_trans' _ _ _ hlower hupper
  have hbad : floor < floor := Q'.lt_of_le_of_lt hcollapsed
    (q_half_mul_lt_self_local hfloor)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' floor hbad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo.tailZero_excludes_cofinalAssignedRatio
