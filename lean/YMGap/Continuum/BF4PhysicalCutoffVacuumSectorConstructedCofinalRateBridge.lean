/-
# The exact cross-carrier rate frontier for the BF4 vacuum sector

Every fixed finite BF4 vacuum carrier now has constructed same-object gap data,
but its rational rate may depend on the carrier.  The genuinely stronger input
needed for expansion is one rational `q < 1` bounding all those constructed
rates.  This module states exactly that input and proves that it compiles to the
existing cofinal moving-centered vacuum-sector certificate.

No inhabitant of the cross-carrier bound is asserted.  The result concerns the
canonical vacuum sector only; the reducible full carrier, vacuum-sector density
and completion, thermodynamic limit, continuum QFT, and Clay conclusion remain
open.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

/-- One strict rational upper bound for the already constructed gap rate on
every finite base carrier at a fixed nome and half-extent.  This is the exact
remaining quantitative uniformity input on the canonical vacuum sector. -/
structure FixedNomeUniformConstructedVacuumSectorRateBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  constructedRate_le : ∀ base : Nat,
    (fixedBaseConstructedUniformGapData hw0 hw1 base half).rate ≤ q

namespace FixedNomeUniformConstructedVacuumSectorRateBound

/-- Select a later cutoff beyond both the constructed fixed-base tail start
and an arbitrary Cauchy threshold. -/
def selectedAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (_family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) : Nat :=
  max (fixedBaseConstructedUniformGapData hw0 hw1 base half).start threshold

theorem selectedAnchor_ge
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q)
    (base threshold : Nat) :
    max base threshold ≤ family.selectedAnchor base threshold := by
  apply Nat.max_le.mpr
  exact
    ⟨Nat.le_trans
        (fixedBaseConstructedUniformGapData
          hw0 hw1 base half).start_ge_base
        (Nat.le_max_left _ _),
      Nat.le_max_right _ _⟩

/-- A carrier-independent upper bound on the constructed rates supplies the
existing cofinal moving-centered vacuum-sector strict-gap certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.selectedAnchor
  anchor_ge := family.selectedAnchor_ge
  centeredGap := by
    intro base threshold coefficient
    let data := fixedBaseConstructedUniformGapData hw0 hw1 base half
    let later := family.selectedAnchor base threshold
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    have hstart : data.start ≤ later := Nat.le_max_left _ _
    have hbaseLater : base ≤ later :=
      Nat.le_trans data.start_ge_base hstart
    have hgap := data.moving_abs_gap later hstart coefficient
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
        (family.constructedRate_le base) hdiagonal)

/-- Consequently the common rate controls the moving centered matrix and
diagonal Bishop-real limits for every finite base carrier. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap base coefficient

end FixedNomeUniformConstructedVacuumSectorRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.selectedAnchor_ge
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
