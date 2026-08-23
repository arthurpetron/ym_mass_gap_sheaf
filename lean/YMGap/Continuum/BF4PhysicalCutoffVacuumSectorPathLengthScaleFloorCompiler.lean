/-
# A primitive scale/floor compiler for the BF4 polynomial path rate

The polynomial canonical-path estimate leaves one dimensionless obstruction:
the path-length scale must remain controlled relative to the persistent
positive edge floor.  This module exposes a concrete sufficient pair of
inputs.  One rational `scale` bounds every base-carrier path-length maximum,
and one positive rational `floor` lies below every corresponding persistent
edge floor.  Their explicit rate

  scale / (scale + floor)

then bounds every constructed fixed-base path-length Poincare rate and
contracts directly to the completed vacuum-sector operator estimate.

The two uniform inputs are deliberately not inhabited.  They are stronger
than the exact ratio frontier, but split it into a finite-graph upper-bound
problem and a physical-kernel lower-bound problem.  No thermodynamic or
continuum limit, QFT reconstruction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge
import YMGap.Continuum.FusionMarginMono

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum

local infix:50 " ≈ " => Q'.eqv

private theorem lt_add_of_pos_right_local (a b : Q')
    (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) <
      b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

private theorem divPos_lt_one_of_lt_local
    (numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : numerator < denominator) :
    Q'.divPos numerator denominator hdenominator < (1 : Q') := by
  unfold Q'.divPos
  have hreciprocal : (0 : Q') <
      Q'.recipPos denominator hdenominator :=
    Q'.recipPos_pos denominator hdenominator
  have hscaled :
      Q'.recipPos denominator hdenominator * numerator <
        Q'.recipPos denominator hdenominator * denominator :=
    Q'.mul_lt_mul_of_pos_left hreciprocal hnumerator
  have hleft :
      numerator * Q'.recipPos denominator hdenominator ≈
        Q'.recipPos denominator hdenominator * numerator :=
    Q'.mul_comm_eqv _ _
  have hright :
      Q'.recipPos denominator hdenominator * denominator ≈
        (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

/-! ## 1. The two primitive uniform inputs -/

structure FixedNomeUniformPathLengthScaleUpperBound
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (scale : Q') : Type 1 where
  scale_pos : (0 : Q') < scale
  pathLengthMaximum_le : ∀ base : Nat,
    centralPhysicalFiniteVacuumSectorPathLengthMaximum
      w hw base half ≤ scale

structure FixedNomeUniformPulledEdgeFloorLowerBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (floor : Q') : Type 1 where
  floor_pos : (0 : Q') < floor
  floor_le : ∀ base : Nat,
    floor ≤ (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half).floor

/-! ## 2. Their explicit common strict rate -/

namespace FixedNomeUniformPathLengthScaleUpperBound

def denominator
    (scale floor : Q') : Q' :=
  scale + floor

theorem denominator_pos
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) :
    (0 : Q') < denominator scale floor := by
  unfold denominator
  exact Q'.pos_add_nonneg upper.scale_pos
    (Q'.le_of_lt lowerFloor.floor_pos)

def rate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) : Q' :=
  Q'.divPos scale (denominator scale floor)
    (denominator_pos upper lowerFloor)

theorem rate_nonnegative
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) :
    (0 : Q') ≤ upper.rate lowerFloor :=
  Q'.le_of_lt
    (Q'.divPos_pos scale (denominator scale floor)
      (denominator_pos upper lowerFloor) upper.scale_pos)

theorem rate_lt_one
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) :
    upper.rate lowerFloor < (1 : Q') := by
  unfold rate
  apply divPos_lt_one_of_lt_local
  exact lt_add_of_pos_right_local scale floor lowerFloor.floor_pos

/-! ## 3. Cross-multiplication against every fixed-base rate -/

theorem pathLengthPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor)
    (base : Nat) :
    FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate
        (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤
      upper.rate lowerFloor := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let pathScale :=
    centralPhysicalFiniteVacuumSectorPathLengthMaximum
      w (Q'.le_of_lt hw0) base half
  have hpath0 : (0 : Q') ≤ pathScale :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorPathLengthMaximum_pos
        w (Q'.le_of_lt hw0) base half)
  have hscale0 : (0 : Q') ≤ scale := Q'.le_of_lt upper.scale_pos
  have hfloor0 : (0 : Q') ≤ floor := Q'.le_of_lt lowerFloor.floor_pos
  have hpathFloor : pathScale * floor ≤ scale * certificate.floor := by
    exact Q'.le_trans' _ (scale * floor) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (upper.pathLengthMaximum_le base) hfloor0)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (lowerFloor.floor_le base) hscale0)
  have hcross :
      pathScale * (scale + floor) ≤
        scale * (pathScale + certificate.floor) := by
    have hadd : pathScale * scale + pathScale * floor ≤
        pathScale * scale + scale * certificate.floor :=
      Q'.add_le_add_left _ _ _ hpathFloor
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv pathScale scale floor))
      (Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (scale * pathScale + scale * certificate.floor) _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv pathScale scale))
            (Q'.eqv_symm
              (Q'.mul_add_eqv scale pathScale certificate.floor)))))
  have hratio :=
    YMGap.Continuum.FusionMarginMono.divPos_le_divPos_of_cross
      pathScale (pathScale + certificate.floor)
      scale (scale + floor)
      (FixedBasePulledPositiveEdgeFloor.pathLengthPoincareScaleData
        certificate).denominator_pos
      (denominator_pos upper lowerFloor) hcross
  simpa [FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate,
    FixedBasePulledPositiveEdgeFloor.pathLengthPoincareScaleData,
    FixedBasePulledPoincareScaleData.rate,
    FixedBasePulledPoincareScaleData.denominator,
    FixedNomeUniformPathLengthScaleUpperBound.rate,
    FixedNomeUniformPathLengthScaleUpperBound.denominator,
    certificate, pathScale] using hratio

def toUniformPathLengthVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) :
    FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half (upper.rate lowerFloor) where
  rate_nonnegative := upper.rate_nonnegative lowerFloor
  rate_lt_one := upper.rate_lt_one lowerFloor
  pathLengthRate_le := upper.pathLengthPoincareRate_le lowerFloor

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {scale floor : Q'}
    (upper : FixedNomeUniformPathLengthScaleUpperBound
      w (Q'.le_of_lt hw0) half scale)
    (lowerFloor : FixedNomeUniformPulledEdgeFloorLowerBound
      w hw0 hw1 half floor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  FixedNomeUniformPathLengthVacuumSectorRateBound.toCompletedStrictContractionData
    (upper.toUniformPathLengthVacuumSectorRateBound lowerFloor)

end FixedNomeUniformPathLengthScaleUpperBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler.FixedNomeUniformPathLengthScaleUpperBound.rate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler.FixedNomeUniformPathLengthScaleUpperBound.pathLengthPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler.FixedNomeUniformPathLengthScaleUpperBound.toUniformPathLengthVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler.FixedNomeUniformPathLengthScaleUpperBound.toCompletedStrictContractionData
