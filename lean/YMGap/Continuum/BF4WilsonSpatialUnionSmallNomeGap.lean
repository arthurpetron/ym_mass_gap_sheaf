/-
# A nonzero excitation and strict bound on the actual Wilson union

Map the existing nome-1/1024, base-one Wilson excitation into the actual
union Cauchy completion. The proved completed pairing pin preserves its
unit orthogonality and positive norm floor. Comparison with the embedded
zero stage proves that this image is nonzero on the union carrier itself.
The universal union two-step bound then applies to this same vector.

All small-nome guards are discharged. This is fixed-spacing SU(2), not a
positive-time response floor, a normalized vector, a continuum construction,
a physical mass calibration or an every-compact-simple-group result.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.BF4WilsonSpatialUnionFixedBase
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSmallNomeGap

namespace YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion (zeroStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionFixedBase
  (completionMap completedInner_map completionMap_unit completionMap_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonExcitation (concreteCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedGap (twoStepRate_strict)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)

local notation "hs0" => And.left existingNome_guards
local notation "hd0" => And.right existingNome_guards
local notation "he0" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hs0 hd0 he0
local notation "B" => completedInner nome_pos nome_lt_one hs0 hd0 he0
local notation "T" => completedTime nome_pos nome_lt_one hs0 hd0 he0
local notation "U" => completedUnit nome_pos nome_lt_one hs0 hd0 he0
local notation "I" => completionMap nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)
local notation "ZF" => BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedZero
  nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)

/-- The same computed rational rate, now acting on the union completion. -/
def rate : Q' := twoStepRate nome hd0

theorem rate_strict : (0 : Q') < rate ∧ rate < (1 : Q') :=
  twoStepRate_strict nome_pos hd0 he0

theorem normFloor_positive : (0 : Q') < starRatio nome :=
  BF4ExactSlabFixedSpatialWilsonSmallNomeGap.normFloor_positive

/-- Every vector of THIS union completion orthogonal to its unit is covered. -/
theorem twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x)) (RCmul (Quotient.mk crealSetoid (ofQ' rate)) (B x x)) :=
  completed_twoStep_form_gap nome_pos nome_lt_one hs0 hd0 he0 x hx

/-- The original witnessing excitation, mapped by the actual fixed-base map. -/
def vector : V := I concreteCertificate.val

def zeroVector : V := embedStage nome_pos nome_lt_one hs0 hd0 he0 zeroStage

theorem vector_orthogonal : B vector U = RCzero := by
  unfold vector
  rw [← completionMap_unit nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide),
    completedInner_map]
  exact concreteCertificate.property.1

theorem vector_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio nome))) (B vector vector) := by
  unfold vector
  rw [completedInner_map]
  exact concreteCertificate.property.2.1

/-- The comparison zero is the actual embedded zero stage, not a chosen quotient representative. -/
theorem zeroVector_inner_zero : B zeroVector zeroVector = RCzero := by
  have hz : I ZF = zeroVector :=
    completionMap_zero nome_pos nome_lt_one hs0 hd0 he0 (base := 1) (by decide)
  rw [← hz, completedInner_map]
  exact BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedZero_inner_zero
    nome_pos nome_lt_one hs0 hd0 he0 (by decide)

theorem vector_ne_zero : vector ≠ zeroVector := by
  intro hz
  have h := vector_norm_floor
  rw [hz, zeroVector_inner_zero] at h
  have hle : starRatio nome ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le normFloor_positive hle)

/-- A Type-valued nonzero witness with the SAME union operator bound. -/
def concreteGapCertificate :
    {v : V // B v U = RCzero ∧
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio nome))) (B v v) ∧
      v ≠ zeroVector ∧
      RCle (B v (T 2 v)) (RCmul (Quotient.mk crealSetoid (ofQ' rate)) (B v v))} :=
  ⟨vector, vector_orthogonal, vector_norm_floor, vector_ne_zero,
    twoStep_form_gap vector vector_orthogonal⟩

/-- Exact image pin, preserving the already constructed base-one excitation. -/
theorem concreteGapCertificate_image : concreteGapCertificate.val = I concreteCertificate.val := rfl

end YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.rate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.rate_strict
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.normFloor_positive
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.twoStep_form_gap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.vector
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.zeroVector
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.vector_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.vector_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.zeroVector_inner_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.vector_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.concreteGapCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap.concreteGapCertificate_image
