/-
# The current resolvent on the existing normalized Wilson excitation

The normalized response module supplies one actual nonzero, unit-orthogonal
Wilson vector with a positive two-step response band.  The current-carrier
resolvent therefore has a concrete non-erasure consequence on that SAME
excitation.  This is fixed-spacing SU(2) nontriviality, not continuum
survival or a physical mass statement.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolvent
import YMGap.Continuum.BF4WilsonSpatialUnionResponseLower

namespace YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "C" => center nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs

theorem unitExcitation_center_fixed : C unitExcitation = unitExcitation :=
  (center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mpr
    unitExcitation_orthogonal

theorem unitExcitation_ne_zero : unitExcitation ≠ Z := by
  intro hz
  have h := unitExcitation_time_ne_zero 0
  rw [completedTime_zero] at h
  exact h hz

/-- The existing normalized Wilson probe remains nonzero after applying the
    SAME completed-carrier resolvent. -/
theorem unitExcitation_resolvent_ne_zero : R unitExcitation ≠ Z :=
  resolvent_ne_zero nome_pos nome_lt_one hsmall hd hs unitExcitation
    unitExcitation_center_fixed unitExcitation_ne_zero

theorem unitExcitation_resolvent_centered : C (R unitExcitation) = R unitExcitation :=
  resolvent_centered nome_pos nome_lt_one hsmall hd hs unitExcitation

end YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_center_fixed
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_centered
