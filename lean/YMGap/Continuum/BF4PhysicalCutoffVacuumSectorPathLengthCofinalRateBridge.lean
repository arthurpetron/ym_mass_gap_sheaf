/-
# The polynomial all-base BF4 path-length rate frontier

Every fixed base carrier now has the strict rate obtained from the maximum
square of its canonical path lengths and its persistent positive edge floor.
This module isolates one common ceiling on those sharper rates, gives the
equivalent denominator-cleared input, and contracts either witness to the
cofinal centered finite gap and the actual completed vacuum-sector operator
contraction.

The previous maximum-amplification all-base witness implies the new witness
at the same rate.  The new all-base witness is deliberately not inhabited.
No thermodynamic or continuum limit, QFT reconstruction, or Clay conclusion
is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum

/-! ## 1. One common ceiling on the polynomial fixed-base rates -/

structure FixedNomeUniformPathLengthVacuumSectorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  pathLengthRate_le : ∀ base : Nat,
    FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate
      (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q

namespace FixedNomeUniformPathLengthVacuumSectorRateBound

def selectedAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (_family : FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) : Nat :=
  max (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half).start threshold

theorem selectedAnchor_ge
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) :
    max base threshold ≤ family.selectedAnchor base threshold := by
  apply Nat.max_le.mpr
  exact
    ⟨Nat.le_trans
        (fixedBasePulledPositiveEdgeFloor
          hw0 hw1 base half).start_ge_base
        (Nat.le_max_left _ _),
      Nat.le_max_right _ _⟩

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.selectedAnchor
  anchor_ge := family.selectedAnchor_ge
  centeredGap := by
    intro base threshold coefficient
    let certificate := fixedBasePulledPositiveEdgeFloor
      hw0 hw1 base half
    let later := family.selectedAnchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    have hstart : certificate.start ≤ later := Nat.le_max_left _ _
    have hbaseLater : base ≤ later :=
      Nat.le_trans certificate.start_ge_base hstart
    have hgap :=
      FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_pathLengthPoincareRate
        certificate later hstart coefficient
    have hmatrixNonnegative := fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := Q'.le_of_lt hw0)
      base later half hbaseLater coefficient
    have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
      (w := w) (hw := Q'.le_of_lt hw0)
      base later half hbaseLater coefficient
    have hdiagonal : (0 : Q') ≤
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half moving :=
      Q'.le_trans' _ _ _ hmatrixNonnegative hmatrixDiagonal
    exact Q'.le_trans' _ _ _ hgap
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (family.pathLengthRate_le base) hdiagonal)

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap

end FixedNomeUniformPathLengthVacuumSectorRateBound

/-! ## 2. Exact denominator-cleared polynomial frontier -/

structure FixedNomeUniformPathLengthFloorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  pathLengthMaximum_le_rate_mul_denominator : ∀ base : Nat,
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    centralPhysicalFiniteVacuumSectorPathLengthMaximum
        w (Q'.le_of_lt hw0) base half ≤
      q *
        (centralPhysicalFiniteVacuumSectorPathLengthMaximum
            w (Q'.le_of_lt hw0) base half + certificate.floor)

namespace FixedNomeUniformPathLengthFloorRateBound

theorem pathLengthPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthFloorRateBound
      w hw0 hw1 half q)
    (base : Nat) :
    FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate
        (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let data := FixedBasePulledPositiveEdgeFloor.pathLengthPoincareScaleData
    certificate
  apply Q'.divPos_le_of_le_mul data.scale data.denominator
    data.denominator_pos
  exact family.pathLengthMaximum_le_rate_mul_denominator base

def toUniformPathLengthVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthFloorRateBound
      w hw0 hw1 half q) :
    FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  pathLengthRate_le := family.pathLengthPoincareRate_le

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformPathLengthFloorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  family.toUniformPathLengthVacuumSectorRateBound.toCompletedStrictContractionData

end FixedNomeUniformPathLengthFloorRateBound

/-! ## 3. The polynomial frontier is weaker than the former maximum frontier -/

namespace FixedNomeUniformMaximumVacuumSectorRateBound

def toUniformPathLengthVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeUniformPathLengthVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  pathLengthRate_le := by
    intro base
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    exact Q'.le_trans' _ _ _
      (FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate_le_maximumPoincareRate
        certificate)
      (family.maximumRate_le base)

end FixedNomeUniformMaximumVacuumSectorRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.FixedNomeUniformPathLengthVacuumSectorRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.FixedNomeUniformPathLengthVacuumSectorRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.FixedNomeUniformPathLengthFloorRateBound.pathLengthPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.FixedNomeUniformPathLengthFloorRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.FixedNomeUniformMaximumVacuumSectorRateBound.toUniformPathLengthVacuumSectorRateBound
