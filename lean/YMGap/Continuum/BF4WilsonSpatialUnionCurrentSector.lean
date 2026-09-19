/-
# Concrete current physical SU(2) sector on the completed Wilson union

The current BF4 construction already has one completed spatial-union carrier,
the original discrete physical-time semigroup, the normalized Wilson probe,
and exact same-object correlator pins.  This file packages those existing
witnesses into one concrete sector datum.  It does not identify this `RC`-valued carrier
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
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
import YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation

namespace YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner completedUnit_norm_one)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionTimePositive
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completed_twoStep_form_gap completedCenteredScalar
    completedCenteredScalar_of_orthogonal)
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (norm_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
  (evenOrbitResidual evenOrbitResidual_strict_form_bound)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completedSub)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation
  (connected_embedStage connected_sq_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm (centeredMoment)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
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
local notation "E" => embedStage nome_pos nome_lt_one hsmall hd hs
local notation "P0" => pairing nome_pos nome_lt_one hsmall hd hs
local notation "K" => completedCenteredScalar nome_pos nome_lt_one hsmall hd hs
local notation "C" => center nome_pos nome_lt_one hsmall hd hs

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
  /-- The uniform strict two-step form bound on this current vacuum complement. -/
  twoStep_strict_form_bound :
    ∀ x, B x vacuum = RCzero →
      RCle (B x (twoStep x))
        (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
          (B x x))
  /-- Explicit fixed-spacing time decay on the full current vacuum complement. -/
  time_decay :
    ∀ x, B x vacuum = RCzero → ∀ n : Nat,
      RCle (B (T n x) (T n x))
        (RCscale (twoStepRate nome hd ^ n) (B x x))
  /-- The completed pairing is pinned to the original same-object correlator. -/
  same_object_correlator_pin :
    ∀ (n : Nat) (x y : Stage),
      B (E x) (T n (E y)) = Quotient.mk crealSetoid (P0 x (time n y))
  /-- The centered completed correlator is pinned to the original centered moment. -/
  connected_correlator_pin :
    ∀ (n : Nat) (x y : Stage),
      K n (E x) (E y) =
        Quotient.mk crealSetoid (centeredMoment nome_pos nome_lt_one hsmall hd hs n x y)
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
  twoStep_strict_form_bound :=
    completed_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs
  time_decay := norm_decay nome_pos nome_lt_one hsmall hd hs
  same_object_correlator_pin :=
    completedTime_correlator nome_pos nome_lt_one hsmall hd hs
  connected_correlator_pin :=
    connected_embedStage nome_pos nome_lt_one hsmall hd hs
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

/-- The packaged sector exposes the uniform strict form bound directly. -/
theorem current_twoStep_strict_form_bound (x : V)
    (hx : B x currentSector.vacuum = RCzero) :
    RCle (B x (currentSector.twoStep x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (B x x)) :=
  currentSector.twoStep_strict_form_bound x hx

/-- The packaged sector exposes the strict coercivity margin of the actual
same-carrier residual `(I - T²)`; this is still fixed-spacing SU(2) data. -/
theorem current_twoStep_defect_strict_form_bound (x : V)
    (hx : B x currentSector.vacuum = RCzero) :
    RCle
      (RCscale (1 - twoStepRate nome hd) (B x x))
      (B x (completedSub nome_pos nome_lt_one hsmall hd hs x
        (currentSector.twoStep x))) := by
  simpa only [currentSector, evenOrbitResidual] using
    (evenOrbitResidual_strict_form_bound nome_pos nome_lt_one hsmall hd hs x hx)

/-- The packaged sector exposes the all-vector fixed-spacing decay directly. -/
theorem current_time_decay (x : V)
    (hx : B x currentSector.vacuum = RCzero) (n : Nat) :
    RCle (B (T n x) (T n x))
      (RCscale (twoStepRate nome hd ^ n) (B x x)) :=
  currentSector.time_decay x hx n

/-- The packaged sector exposes the exact dense same-object correlator pin. -/
theorem current_same_object_correlator_pin (n : Nat) (x y : Stage) :
    B (E x) (T n (E y)) = Quotient.mk crealSetoid (P0 x (time n y)) :=
  currentSector.same_object_correlator_pin n x y

/-- The packaged sector exposes the exact connected same-object correlator pin. -/
theorem current_connected_correlator_pin (n : Nat) (x y : Stage) :
    K n (E x) (E y) =
      Quotient.mk crealSetoid (centeredMoment nome_pos nome_lt_one hsmall hd hs n x y) :=
  currentSector.connected_correlator_pin n x y

/-- The connected same-object correlator inherits the explicit current decay. -/
theorem current_connected_correlator_sq_decay (n : Nat) (x y : V) :
    RCle (RCmul (K n x y) (K n x y))
      (RCmul (B (C x) (C x))
        (RCscale (twoStepRate nome hd ^ n) (B (C y) (C y)))) :=
  connected_sq_decay nome_pos nome_lt_one hsmall hd hs n x y

/-- The probe's positive response survives exact connected centering. -/
theorem current_probe_connected_twoStep_lower :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (K 2 currentSector.probe currentSector.probe) := by
  have hx : B currentSector.probe U = RCzero :=
    currentSector.probe_vacuum_orthogonal
  rw [completedCenteredScalar_of_orthogonal nome_pos nome_lt_one hsmall hd hs
    2 currentSector.probe hx]
  exact currentSector.probe_twoStep_lower

/-- The matching upper response also survives exact connected centering. -/
theorem current_probe_connected_twoStep_upper :
    RCle (K 2 currentSector.probe currentSector.probe)
      (Quotient.mk crealSetoid (ofQ' rayleighCeiling)) := by
  have hx : B currentSector.probe U = RCzero :=
    currentSector.probe_vacuum_orthogonal
  rw [completedCenteredScalar_of_orthogonal nome_pos nome_lt_one hsmall hd hs
    2 currentSector.probe hx]
  exact currentSector.probe_twoStep_upper

/-- The packaged probe has a strict positive two-step response floor. -/
theorem current_probe_twoStep_strict_lower :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (B currentSector.probe (currentSector.twoStep currentSector.probe)) :=
  currentSector.probe_twoStep_lower

/-! ## All-time same-object survival consequences -/

/-- The packaged normalized Wilson probe has the existing two-sided response
band at every even discrete time, with the same explicit floor and ceiling.
This is a current-carrier statement; it does not quantify over a changing
spacing family. -/
theorem current_probe_even_band (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ n)))
        (B currentSector.probe (T (2 * n) currentSector.probe)) ∧
      RCle (B currentSector.probe (T (2 * n) currentSector.probe))
        (Quotient.mk crealSetoid (ofQ' (rayleighCeiling ^ n))) := by
  simpa only [currentSector] using
    (unitExcitation_even_band n)

/-- The same probe remains quantitatively nonzero after every finite integer
time step on the completed Wilson carrier. -/
theorem current_probe_time_norm_floor (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ n)))
      (B (T n currentSector.probe) (T n currentSector.probe)) := by
  simpa only [currentSector] using
    (unitExcitation_time_norm_floor n)

/-- No finite discrete-time image of the packaged current probe is the
completed zero.  This is an explicit fixed-spacing non-erasure witness; it
does not assert survival along a changing-spacing or continuum family. -/
theorem current_probe_time_ne_zero (n : Nat) :
    T n currentSector.probe ≠ completedZero nome_pos nome_lt_one hsmall hd hs := by
  simpa only [currentSector] using
    (unitExcitation_time_ne_zero n)

/-- The packaged resolvent probe supplies a quantitative non-erasure witness. -/
theorem current_resolvent_probe_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (B (R currentSector.probe) (R currentSector.probe)) :=
  currentSector.resolvent_probe_norm_floor

end CompletedPhysicalSU2Sector

end YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.currentSector
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_twoStep_strict_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_twoStep_defect_strict_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_time_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_same_object_correlator_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_connected_correlator_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_connected_correlator_sq_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_connected_twoStep_lower
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_connected_twoStep_upper
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_twoStep_strict_lower
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_even_band
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_time_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_probe_time_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector.CompletedPhysicalSU2Sector.current_resolvent_probe_floor
