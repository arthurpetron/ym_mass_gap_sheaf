/-
# A nonvacuous strict form bound at the existing concrete small nome

At nome 1/1024 and source base one, every analytic guard is already proved.
The universal two-step form bound therefore acts on the SAME Wilson
Completion that contains the existing positive-norm centered plaquette.
The final Type-valued certificate reuses that exact vector and its norm
floor, adding only the newly proved completed-time inequality.

This is a fixed-spacing SU(2) nonvacuity join. It asserts neither a positive
nonzero-time response nor normalization, continuum QFT, physical mass
calibration, or coverage of every compact simple group.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef (completedZero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime (completedTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap
  (twoStepRate_strict completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation (concreteCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)

local notation "hs0" => And.left existingNome_guards
local notation "hd0" => And.right existingNome_guards
local notation "he0" => And.right existingNome_entropyRate
local notation "V" => Completion nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)
local notation "B" => completedInner nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)
local notation "T" => completedTime nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)
local notation "U" => embed nome_pos nome_lt_one hs0 hd0 he0 (by decide) (unit 1)
local notation "Z" => completedZero nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)

/-- Computed rational rate for two original physical-time steps at nome 1/1024. -/
def rate : Q' := twoStepRate nome hd0

theorem rate_strict : (0 : Q') < rate ∧ rate < (1 : Q') :=
  twoStepRate_strict nome_pos hd0 he0

theorem normFloor_positive : (0 : Q') < starRatio nome :=
  starRatio_positive nome_pos nome_lt_one

/-- All guards are discharged; the only premise is actual unit orthogonality. -/
theorem twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x)) (RCmul (Quotient.mk crealSetoid (ofQ' rate)) (B x x)) :=
  completed_twoStep_form_gap nome_pos nome_lt_one hs0 hd0 he0 (by decide) x hx

/-- The existing nonzero excitation, with the SAME completed two-step bound. -/
def concreteGapCertificate :
    {v : V // B v U = RCzero ∧
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio nome))) (B v v) ∧
      v ≠ Z ∧
      RCle (B v (T 2 v)) (RCmul (Quotient.mk crealSetoid (ofQ' rate)) (B v v))} :=
  ⟨concreteCertificate.val, concreteCertificate.property.1,
    concreteCertificate.property.2.1, concreteCertificate.property.2.2,
    twoStep_form_gap concreteCertificate.val concreteCertificate.property.1⟩

/-- No alternative vector or completion is selected by this certificate. -/
theorem concreteGapCertificate_vector : concreteGapCertificate.val = concreteCertificate.val := rfl

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.rate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.rate_strict
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.normFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.concreteGapCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap.concreteGapCertificate_vector
