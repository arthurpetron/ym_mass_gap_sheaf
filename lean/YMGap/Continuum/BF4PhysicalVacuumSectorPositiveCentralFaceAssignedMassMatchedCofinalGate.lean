/-
# Matched-cofinal feasibility gate for the assigned central-face ratio

The finite matched-tail gate proves that the sharp assigned-spin ratio
ceiling times the displayed spin-cube ray mass is at least `1/6`.  This module
states the actual same-action cofinal producer: one common ratio bound along
the varying matched weight and cutoff.  Any inhabitant forces the ray mass to
stay above the explicit reciprocal floor `(1/6) / ratioBound` at every late
matched scale.

This is a necessary condition, not an inhabitant of the producer and not a
ray-mass asymptotic estimate.  It proves no congestion bound, finite gap,
physical normalization, continuum theory, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. The same-action cofinal producer -/

/-- The precise assigned-mass comparison needed along the varying matched
same-action family: after one tail scale, every assigned central-face mean is
bounded by one common multiple of the corresponding spin-cube weight. -/
structure MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ratioBound : Q'
  ratioBound_nonnegative : (0 : Q') ≤ ratioBound
  start : Nat
  start_tail : 2 ≤ start
  assignedMean_le : ∀ scale, start ≤ scale →
    ∀ offset,
      (hoffset :
        offset < matchedAllSpinCutoff family coupling scale) →
      centralPhysicalStationaryMean
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (positiveCentralFaceAssignedUnitObservable
            (matchedAllSpinCutoff family coupling scale)
            (offset + 1)).value ≤
        ratioBound *
          centralPhysicalFiniteWeight
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (centralLowerExcitedSpinCubeIndex
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) offset)

namespace MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State → Q') (bound : Q')
    (hboundNonnegative : (0 : Q') ≤ bound) :
    ∀ states : List State,
      (∀ state, state ∈ states → value state ≤ bound) →
      listQMaxZero value states ≤ bound
  | [], _ => hboundNonnegative
  | head :: tail, hbound => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      exact ⟨hbound head List.mem_cons_self,
        listQMaxZero_le_of_member_bound_local value bound hboundNonnegative tail
          (fun state hstate =>
            hbound state (List.mem_cons_of_mem head hstate))⟩

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 2. Located finite ceilings below the common bound -/

/-- Every exact matched assigned expectation/weight ratio lies below the
common cofinal bound after the declared start scale. -/
theorem exactRatioAt_le_ratioBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge)
    (scale : Nat) (hscale : ratio.start ≤ scale)
    (offset : Nat)
    (hoffset : offset < matchedAllSpinCutoff family coupling scale) :
    positiveCentralFaceAssignedStationaryRatioAt
        (matchedAllSpinWeight_pos family coupling scale) hoffset ≤
      ratio.ratioBound := by
  let w := matchedAllSpinWeight family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let source := centralLowerExcitedSpinCubeIndex
    w (matchedAllSpinWeight_nonnegative family coupling scale) K offset
  let weight := centralPhysicalFiniteWeight
    w (matchedAllSpinWeight_nonnegative family coupling scale) K 0 source
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector
        (matchedAllSpinWeight_pos family coupling scale) (by omega))
  apply Q'.divPos_le_of_le_mul _ weight hweight
  exact ratio.assignedMean_le scale hscale offset hoffset

/-- Every sufficiently late sharp finite matched ratio maximum lies below
the same cofinal ratio bound. -/
theorem finiteCeiling_le_ratioBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge)
    (scale : Nat) (hscale : ratio.start ≤ scale) :
    positiveCentralFaceAssignedStationaryRatioFiniteCeiling
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale) ≤
      ratio.ratioBound := by
  unfold positiveCentralFaceAssignedStationaryRatioFiniteCeiling
  apply listQMaxZero_le_of_member_bound_local _ ratio.ratioBound
    ratio.ratioBound_nonnegative
  intro offset hoffsetMem
  have hoffset := List.mem_range.mp hoffsetMem
  rw [positiveCentralFaceAssignedStationaryRatioValue_eq
    (matchedAllSpinWeight_pos family coupling scale) hoffset]
  exact ratio.exactRatioAt_le_ratioBound scale hscale offset hoffset

/-! ## 3. The reciprocal ray-mass barrier -/

/-- A common matched cofinal ratio bound must keep its product with the
displayed ray mass above `1/6` at every late scale. -/
theorem oneSixth_le_ratioBound_mul_rayMass_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge)
    (scale : Nat) (hscale : ratio.start ≤ scale) :
    Q'.mkPos 1 6 (by decide) ≤
      ratio.ratioBound *
        centralLowerExcitedSpinCubeRayMass
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) := by
  let rayMass := centralLowerExcitedSpinCubeRayMass
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
  have hfinite :=
    oneSixth_le_matchedAssignedRatioFiniteCeiling_mul_rayMass_tail
      bridge (Nat.le_trans ratio.start_tail hscale)
  have hceiling := ratio.finiteCeiling_le_ratioBound scale hscale
  have hrayMass : (0 : Q') ≤ rayMass :=
    centralLowerExcitedSpinCubeRayMass_nonnegative
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ rayMass
    hceiling hrayMass
  exact Q'.le_trans' _ _ _ hfinite hmul

/-- The common ratio bound is forced to be strictly positive; this is derived
from the calibrated matched tail rather than added as a structure field. -/
theorem ratioBound_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge) :
    (0 : Q') < ratio.ratioBound := by
  let rayMass := centralLowerExcitedSpinCubeRayMass
    (matchedAllSpinWeight family coupling ratio.start)
    (matchedAllSpinWeight_nonnegative family coupling ratio.start)
    (matchedAllSpinCutoff family coupling ratio.start)
  have hfloor := ratio.oneSixth_le_ratioBound_mul_rayMass_tail
    ratio.start (Nat.le_refl ratio.start)
  have hproduct : (0 : Q') < ratio.ratioBound * rayMass :=
    Q'.pos_of_lt_of_le (by decide :
      (0 : Q') < Q'.mkPos 1 6 (by decide)) hfloor
  exact q_left_pos_of_mul_pos_local
    (centralLowerExcitedSpinCubeRayMass_nonnegative
      (matchedAllSpinWeight_pos family coupling ratio.start)
      (matchedAllSpinCutoff family coupling ratio.start)) hproduct

/-- The decisive necessary asymptotic condition: any common assigned-ratio
ceiling forces a uniform positive lower bound on the matched ray mass. -/
theorem reciprocalRatioFloor_le_rayMass_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge)
    (scale : Nat) (hscale : ratio.start ≤ scale) :
    Q'.divPos (Q'.mkPos 1 6 (by decide))
        ratio.ratioBound ratio.ratioBound_pos ≤
      centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) := by
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _
    (ratio.ratioBound *
      centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)) _
    (ratio.oneSixth_le_ratioBound_mul_rayMass_tail scale hscale)
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv ratio.ratioBound
        (centralLowerExcitedSpinCubeRayMass
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale))))

end MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate.MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio.exactRatioAt_le_ratioBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate.MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio.finiteCeiling_le_ratioBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate.MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio.oneSixth_le_ratioBound_mul_rayMass_tail
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate.MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio.ratioBound_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate.MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio.reciprocalRatioFloor_le_rayMass_tail
