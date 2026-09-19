/-
# Concrete current physical SU(2) sector on the completed Wilson union

The current BF4 construction already has one completed spatial-union carrier,
the original discrete physical-time semigroup, the normalized Wilson probe,
and a same-object response band.  This file packages those existing witnesses
into one concrete sector datum.  It does not identify this `RC`-valued carrier
with the canonical `GNSData`/OS completion; that remains the separate bridge
residual in `BF4WilsonSpatialUnionCanonicalGNSBridge`.

The package is fixed-spacing and small-nome SU(2).  It is a real completed
physical sector and transfer witness, not a continuum theorem or a Clay mass
gap.  Its purpose is to make the forward landmark consumable by later
canonical-carrier and spacing-control compilers.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
import YMGap.Continuum.BF4WilsonSpatialUnionTimePositive
import YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
import YMGap.Continuum.BF4WilsonSpatialUnionResponseLower

namespace YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner completedUnit_norm_one)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionTimePositive
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs

/-- A concrete `RC`-valued transfer/sector package on the current completed
Wilson carrier.  The fields deliberately use the same carrier and same form
throughout; no cross-carrier identification is hidden in the structure. -/
structure CompletedPhysicalSU2Sector : Type 2 where
  /-- One physical discrete-time transfer step. -/
  step : V → V
  /-- The normalized Wilson unit spanning the current vacuum direction. -/
  vacuum : V
  /-- The selected transfer step fixes the current vacuum. -/
  step_vacuum : step vacuum = vacuum
  /-- The selected step preserves the current vacuum complement. -/
  step_preserves_vacuum_complement :
    ∀ x, B x vacuum = RCzero → B (step x) vacuum = RCzero
  /-- The current vacuum has the completed unit norm. -/
  vacuum_norm_one :
    B vacuum vacuum = Quotient.mk crealSetoid cone
  /-- Self-adjointness for the completed Wilson form. -/
  step_selfAdjoint : ∀ x y, B (step x) y = B x (step y)
  /-- One-step reflection positivity on every current-carrier vector. -/
  step_positive : ∀ x, RCnonneg (B x (step x))
  /-- Squared-norm contraction of the same step. -/
  step_contraction : ∀ x, RCle (B (step x) (step x)) (B x x)
  /-- The explicitly selected two-step physical map. -/
  twoStep : V → V
  /-- The two-step map is the square of the selected step. -/
  twoStep_eq_step_sq : ∀ x, twoStep x = step (step x)
  /-- The existing normalized excitation. -/
  probe : V
  /-- The probe is nonzero on the current completed carrier. -/
  probe_ne_zero : probe ≠ Z
  /-- The probe is orthogonal to the current vacuum direction. -/
  probe_vacuum_orthogonal : B probe vacuum = RCzero
  /-- A positive same-object two-step lower response. -/
  probe_twoStep_lower :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (B probe (twoStep probe))
  /-- The matching same-object two-step upper response. -/
  probe_twoStep_upper :
    RCle (B probe (twoStep probe))
      (Quotient.mk crealSetoid (ofQ' rayleighCeiling))
  /-- The current-carrier resolvent probe remains nonzero. -/
  resolvent_probe_ne_zero : R probe ≠ Z
  /-- The current-carrier resolvent probe remains centered. -/
  resolvent_probe_centered :
    center nome_pos nome_lt_one hsmall hd hs (R probe) = R probe
  /-- The explicit squared-norm floor for that resolvent probe. -/
  resolvent_probe_norm_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (B (R probe) (R probe))

/-- The actual current completed physical SU(2) sector. -/
def currentSector : CompletedPhysicalSU2Sector where
  step := T 1
  vacuum := U
  step_vacuum := completedUnit_fixed nome_pos nome_lt_one hsmall hd hs 1
  step_preserves_vacuum_complement :=
    completedTime_preserves_orthogonal nome_pos nome_lt_one hsmall hd hs 1
  vacuum_norm_one := completedUnit_norm_one nome_pos nome_lt_one hsmall hd hs
  step_selfAdjoint := completedInner_time_balance nome_pos nome_lt_one hsmall hd hs 1
  step_positive := completedInner_oneStep_nonnegative nome_pos nome_lt_one hsmall hd hs
  step_contraction := completedInner_time_contraction nome_pos nome_lt_one hsmall hd hs 1
  twoStep := T 2
  twoStep_eq_step_sq := by
    intro x
    simpa only [Nat.reduceAdd] using
      (completedTime_add nome_pos nome_lt_one hsmall hd hs 1 1 x)
  probe := unitExcitation
  probe_ne_zero := unitExcitation_ne_zero
  probe_vacuum_orthogonal := unitExcitation_orthogonal
  probe_twoStep_lower := by
    exact unitExcitation_even_lower 1
  probe_twoStep_upper := by
    exact unitExcitation_even_upper 1
  resolvent_probe_ne_zero := unitExcitation_resolvent_ne_zero
  resolvent_probe_centered := unitExcitation_resolvent_centered
  resolvent_probe_norm_floor := unitExcitation_resolvent_norm_floor

namespace CompletedPhysicalSU2Sector

/-- The packaged probe has a strict positive two-step response floor. -/
theorem current_probe_twoStep_strict_lower :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (B currentSector.probe (currentSector.twoStep currentSector.probe)) :=
  currentSector.probe_twoStep_lower

/-- The packaged resolvent probe supplies a quantitative non-erasure witness. -/
theorem current_resolvent_probe_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (B (R currentSector.probe) (R currentSector.probe)) :=
  currentSector.resolvent_probe_norm_floor

end CompletedPhysicalSU2Sector

end YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.currentSector
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_twoStep_strict_lower
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_resolvent_probe_floor
