/-
# Grouped all-label Haar refresh arithmetic

The exact SU(2) central heat corridor has doubled-spin mode

    w^(C4 label),  C4(label) = label * (label + 2).

After `steps` Haar-convolution factors its heat coordinate is `w^steps`;
therefore every mode is exactly `w^(steps * C4 label)`.  This file proves
that all-label coefficient identity over the repository's constructive
rationals and pins the rational Haar-floor constant found by the BF4
all-label tail census:

    epsilon0 = 1055 / 2272.

A cover by `r` independently refreshed corridor coordinates has the
arithmetic packet mass `epsilon0^r`, which is strictly positive for every
finite `r`.  If a physical corrected-slab CP-order decomposition supplies
an additional domination coefficient `eta > 0`, the resulting physical
packet coefficient `eta * epsilon0^r` is strictly positive as well.

This module does not assert that the interacting corrected-slab map has
that CP-order decomposition.  Nor does it formalize the infinite character
tail proving the pointwise heat-kernel lower bound; that analytic statement
is presently certified in exact arithmetic by
`computations/grouped_all_label_haar_refresh.py`.  The purpose here is to
close the coefficient-semigroup and finite-cover arithmetic consumed by
the future physical constructor without introducing logarithms, limits,
choice, or classical reasoning.
-/

import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.BakryEmery
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.R1CornerAtoms

namespace YMGap.Continuum.GroupedAllLabelHaarRefresh

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AbelianFusionCLT

local infix:50 " ≈ " => Q'.eqv

/-- Exact heat coordinate after a finite Haar-convolution corridor. -/
def groupedHeatCoordinate (w : Q') (steps : Nat) : Q' :=
  qpow w steps

/-- The all-label multiplier of one grouped doubled-spin mode. -/
def groupedHeatMode (w : Q') (steps label : Nat) : Q' :=
  qpow (groupedHeatCoordinate w steps) (c4 label)

/-- Every label obeys the exact heat-semigroup exponent law. -/
theorem groupedHeatMode_semigroup
    (w : Q') (steps label : Nat) :
    groupedHeatMode w steps label ≈
      qpow w (steps * c4 label) := by
  unfold groupedHeatMode groupedHeatCoordinate
  exact Q'.eqv_symm
    (qpowR_exp_mul w steps (c4 label))

/-- Exact rational common-Haar floor obtained from the all-label tail:
`1 - 1/2 - 81/2272 = 1055/2272`. -/
def allLabelHaarFloor : Q' :=
  Q'.mkPos 1055 2272 (by decide)

/-- Exact complement of the common-Haar floor. -/
def allLabelHaarResidualRate : Q' :=
  Q'.mkPos 1217 2272 (by decide)

theorem allLabelHaarFloor_value :
    allLabelHaarFloor ≈ Q'.mkPos 1055 2272 (by decide) := by
  exact Q'.eqv_refl _

theorem allLabelHaarResidualRate_value :
    allLabelHaarResidualRate ≈ Q'.mkPos 1217 2272 (by decide) := by
  exact Q'.eqv_refl _

theorem allLabelHaarFloor_pos :
    (0 : Q') < allLabelHaarFloor := by
  decide

theorem allLabelHaarFloor_le_one :
    allLabelHaarFloor ≤ (1 : Q') := by
  decide

theorem allLabelHaarResidualRate_nonnegative :
    (0 : Q') ≤ allLabelHaarResidualRate := by
  decide

theorem allLabelHaarResidualRate_lt_one :
    allLabelHaarResidualRate < (1 : Q') := by
  decide

theorem floor_add_residual_eqv_one :
    allLabelHaarFloor + allLabelHaarResidualRate ≈ (1 : Q') := by
  decide

/-- Common packet mass for a finite cover by `corridorCount` independently
refreshed group coordinates. -/
def corridorPacketMass (corridorCount : Nat) : Q' :=
  qpow allLabelHaarFloor corridorCount

theorem corridorPacketMass_pos (corridorCount : Nat) :
    (0 : Q') < corridorPacketMass corridorCount := by
  unfold corridorPacketMass
  exact BondMovingScaledNorm.qpow_pos
    allLabelHaarFloor_pos corridorCount

/-! ## The cumulative-heat premise already contains gap-scale content -/

/-- Exact constants in the logarithm-free converse estimate. -/
def oneEighth : Q' := Q'.mkPos 1 8 (by decide)
def sevenEighths : Q' := Q'.mkPos 7 8 (by decide)

private theorem sevenEighths_le_one_sub_of_le_eighth
    {x : Q'} (hx : x ≤ oneEighth) :
    sevenEighths ≤ (1 : Q') - x := by
  have hneg : -oneEighth ≤ -x := Q'.neg_le_neg hx
  have hadd :
      (1 : Q') + -oneEighth ≤ (1 : Q') + -x :=
    Q'.add_le_add_left 1 (-oneEighth) (-x) hneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide :
      sevenEighths ≈ (1 : Q') + -oneEighth))
    hadd

/-- If a grouped fundamental separator is at most `1/8`, then the one-step
margin already obeys the exact gap-scale inequality

    7/8 <= steps * (1 - rho).

This is the constructive, logarithm-free converse showing that a uniformly
mixed fixed-distance corridor cannot be assumed independently of a
per-spacing gap estimate. -/
theorem grouped_eighth_implies_step_margin
    {rho : Q'} (hrho0 : (0 : Q') ≤ rho)
    (hrho1 : rho ≤ (1 : Q')) (steps : Nat)
    (hgrouped : qpow rho steps ≤ oneEighth) :
    sevenEighths ≤
      Q'.ofNat steps * ((1 : Q') - rho) := by
  have hleft :
      sevenEighths ≤ (1 : Q') - qpow rho steps :=
    sevenEighths_le_one_sub_of_le_eighth hgrouped
  have hbern :
      (1 : Q') - qpow rho steps ≤
        Q'.ofNat steps * ((1 : Q') - rho) :=
    R1CornerAtoms.oneSub_qpow_le hrho0 hrho1 steps
  exact Q'.le_trans' _ _ _ hleft hbern

/-- Arithmetic interface supplied by the missing physical CP-order corridor
domination theorem.  `eta` is the mass with which the actual corrected-slab
map contains the finite heat-corridor cover. -/
structure PhysicalCorridorDominationMass : Type where
  corridorCount : Nat
  eta : Q'
  eta_pos : (0 : Q') < eta
  eta_le_one : eta ≤ (1 : Q')

namespace PhysicalCorridorDominationMass

/-- The physical refresh coefficient implied by the corridor domination
mass and the all-label common Haar floor. -/
def refreshMass
    (door : PhysicalCorridorDominationMass) : Q' :=
  door.eta * corridorPacketMass door.corridorCount

theorem refreshMass_pos
    (door : PhysicalCorridorDominationMass) :
    (0 : Q') < door.refreshMass := by
  unfold refreshMass
  exact Q'.mul_pos door.eta_pos
    (corridorPacketMass_pos door.corridorCount)

theorem corridorPacketMass_le_one (corridorCount : Nat) :
    corridorPacketMass corridorCount ≤ (1 : Q') := by
  unfold corridorPacketMass
  exact HeatKernelGap.qpow_le_one
    (Q'.le_of_lt allLabelHaarFloor_pos)
    allLabelHaarFloor_le_one corridorCount

theorem refreshMass_le_one
    (door : PhysicalCorridorDominationMass) :
    door.refreshMass ≤ (1 : Q') := by
  unfold refreshMass
  have hnonnegative : (0 : Q') ≤ corridorPacketMass door.corridorCount :=
    Q'.le_of_lt (corridorPacketMass_pos door.corridorCount)
  have hfirst :
      door.eta * corridorPacketMass door.corridorCount ≤
        (1 : Q') * corridorPacketMass door.corridorCount :=
    Q'.mul_le_mul_of_nonneg_right
      door.eta 1 (corridorPacketMass door.corridorCount)
      door.eta_le_one hnonnegative
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.one_mul_eqv
          (corridorPacketMass door.corridorCount)))
      (corridorPacketMass_le_one door.corridorCount))

/-- Exact base-norm rate produced once the physical domination door is
inhabited. -/
def refreshRate
    (door : PhysicalCorridorDominationMass) : Q' :=
  (1 : Q') - door.refreshMass

theorem refreshRate_nonnegative
    (door : PhysicalCorridorDominationMass) :
    (0 : Q') ≤ door.refreshRate := by
  unfold refreshRate
  exact Q'.sub_nonneg_of_le door.refreshMass_le_one

theorem refreshRate_lt_one
    (door : PhysicalCorridorDominationMass) :
    door.refreshRate < (1 : Q') := by
  unfold refreshRate
  exact BakryEmery.one_sub_lt_one door.refreshMass_pos

end PhysicalCorridorDominationMass

#print axioms groupedHeatMode_semigroup
#print axioms allLabelHaarFloor_pos
#print axioms floor_add_residual_eqv_one
#print axioms corridorPacketMass_pos
#print axioms grouped_eighth_implies_step_margin
#print axioms PhysicalCorridorDominationMass.refreshMass_pos
#print axioms PhysicalCorridorDominationMass.refreshRate_lt_one

end YMGap.Continuum.GroupedAllLabelHaarRefresh
