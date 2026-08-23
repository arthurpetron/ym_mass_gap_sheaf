/-
# The sharper all-base BF4 maximum-rate frontier

Every fixed base vacuum carrier now has the maximum-path rate

  pathMaximum / (pathMaximum + edgeFloor),

which is no larger than the earlier sum-ceiling rate.  This module isolates
one strict rational ceiling on those sharper rates, proves the equivalent
denominator-cleared sufficient data, and contracts either witness to the
cofinal centered finite gap and the actual completed sector operator gap.

The all-base witness is deliberately not inhabited.  No thermodynamic or
continuum limit, QFT reconstruction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

/-! ## 1. One common ceiling on the sharper constructed rates -/

/-- A strict rational upper bound on the maximum-path rate of every finite
base carrier at fixed nome and half-extent. -/
structure FixedNomeUniformMaximumVacuumSectorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  maximumRate_le : ∀ base : Nat,
    FixedBasePulledPositiveEdgeFloor.maximumPoincareRate
      (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q

namespace FixedNomeUniformMaximumVacuumSectorRateBound

/-- Select a cutoff beyond both the fixed-base persistence start and an
arbitrary Cauchy threshold. -/
def selectedAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (_family : FixedNomeUniformMaximumVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) : Nat :=
  max (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half).start threshold

theorem selectedAnchor_ge
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumVacuumSectorRateBound
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

/-- A common ceiling on the sharper rates supplies the exact cofinal
same-object centered-gap certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumVacuumSectorRateBound
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
      FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_maximumPoincareRate
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
        (family.maximumRate_le base) hdiagonal)

/-- Since completed Markov-form Cauchy--Schwarz is now unconditional, the
same all-base maximum-rate witness directly gives the actual completed-sector
strict contraction datum. -/
def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumVacuumSectorRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap

end FixedNomeUniformMaximumVacuumSectorRateBound

/-! ## 2. The maximum/floor denominator-cleared frontier -/

/-- One strict common rate together with the exact denominator-cleared
maximum-path inequality on every base carrier. -/
structure FixedNomeUniformMaximumFloorPathRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  maximum_le_rate_mul_denominator : ∀ base : Nat,
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    centralPhysicalFiniteVacuumSectorPathMaximum
        w (Q'.le_of_lt hw0) base half ≤
      q *
        (centralPhysicalFiniteVacuumSectorPathMaximum
            w (Q'.le_of_lt hw0) base half + certificate.floor)

namespace FixedNomeUniformMaximumFloorPathRateBound

theorem maximumPoincareRate_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumFloorPathRateBound
      w hw0 hw1 half q)
    (base : Nat) :
    FixedBasePulledPositiveEdgeFloor.maximumPoincareRate
        (fixedBasePulledPositiveEdgeFloor hw0 hw1 base half) ≤ q := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let data := FixedBasePulledPositiveEdgeFloor.maximumPoincareScaleData
    certificate
  apply Q'.divPos_le_of_le_mul data.scale data.denominator
    data.denominator_pos
  exact family.maximum_le_rate_mul_denominator base

def toUniformMaximumVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumFloorPathRateBound
      w hw0 hw1 half q) :
    FixedNomeUniformMaximumVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  maximumRate_le := family.maximumPoincareRate_le

def toCompletedStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformMaximumFloorPathRateBound
      w hw0 hw1 half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  family.toUniformMaximumVacuumSectorRateBound.toCompletedStrictContractionData

end FixedNomeUniformMaximumFloorPathRateBound

/-! ## 3. The new frontier is strictly no stronger than the old one -/

namespace FixedNomeUniformFloorPathRateBound

/-- Any witness for the previous sum-ceiling frontier gives a witness for the
maximum-rate frontier at the same `q`; the converse is not assumed. -/
def toUniformMaximumVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformFloorPathRateBound w hw0 hw1 half q) :
    FixedNomeUniformMaximumVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  maximumRate_le := by
    intro base
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    exact Q'.le_trans' _ _ _
      (FixedBasePulledPositiveEdgeFloor.maximumPoincareRate_le_uniformPoincareRate
        certificate)
      (family.uniformPoincareRate_le base)

end FixedNomeUniformFloorPathRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.FixedNomeUniformMaximumVacuumSectorRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.FixedNomeUniformMaximumVacuumSectorRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.FixedNomeUniformMaximumFloorPathRateBound.maximumPoincareRate_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.FixedNomeUniformMaximumFloorPathRateBound.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.FixedNomeUniformFloorPathRateBound.toUniformMaximumVacuumSectorRateBound
