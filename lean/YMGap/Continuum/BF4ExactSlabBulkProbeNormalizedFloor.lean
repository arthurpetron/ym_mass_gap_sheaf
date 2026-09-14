/-
# Positive ORIGINAL normalized covariance floor at every translated volume

The spectator-relative raw floor and SAME full-partition comparison give
(s/16)*Zfull <= rawForm(P-c,P-c), every cutoff K>=1 and rational c.
The cutoff limit and the original partition reciprocal preserve this bound.
The finite completed centering construction then gives connected covariance
at least s/16 for the translated probe, independently of volume.

All objects and their Cauchy moduli are the existing original-action ones.
The nome is fixed at 1/1024. No continuum or coupling-uniform gap follows.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison
import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality

namespace YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference (bulkProbe)
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference (signal)
open YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor
open YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor (recentered)
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation (reciprocal_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- The witness has no cutoff, volume, or centering argument. -/
def normalizedFloor : Q' := signal nome * Q'.invSucc 15

theorem normalizedFloor_positive : (0 : Q') < normalizedFloor := by decide

theorem normalizedFloor_twice : normalizedFloor*2 ≈ rawFloorCoefficient := by decide

theorem rawForm_fullPartition_floor (K : Nat) (hK : 1 ≤ K) (half : Nat) (c : Q') :
    normalizedFloor * rawForm nome K (.unit : PlaquetteExpression half) .unit ≤
      rawForm nome K (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c) :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (existingNome_originalUnit_upper K half)
    (Q'.le_of_lt normalizedFloor_positive))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ normalizedFloor_twice))) (rawForm_relative_floor K hK half c))

theorem rawLimit_scaledUnit_le (half : Nat) (c : Q') :
    leEv (rawLimit nome nome_pos nome_lt_one (.smul normalizedFloor (.unit : PlaquetteExpression half)) .unit)
      (rawLimit nome nome_pos nome_lt_one (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c)) :=
  leEv_of_ofQ'_limit_le (rawLimit_converges nome nome_pos nome_lt_one (.smul normalizedFloor .unit) .unit)
    (rawLimit_converges nome nome_pos nome_lt_one (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c))
    (fun epsilon he => ⟨1, fun K hK => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (rawForm_smul_left nome K normalizedFloor (.unit : PlaquetteExpression half) .unit))
      (Q'.le_trans' _ _ _ (rawForm_fullPartition_floor K hK half c)
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he)))⟩)

/-- SAME cutoff-limit expectation, without a volume-dependent reciprocal floor. -/
theorem normalized_form_floor (half : Nat) (c : Q') :
    leEv (ofQ' normalizedFloor)
      (form nome nome_pos nome_lt_one (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c)) := by
  let a : PlaquetteExpression half := .smul normalizedFloor .unit
  let e := recentered half (bulkProbe half) c
  let r := actionReciprocal nome nome_pos nome_lt_one half
  have hmul := leEv_mul_nonneg_left (reciprocal_nonnegative nome nome_pos nome_lt_one half) (rawLimit_scaledUnit_le half c)
  have hform : leEv (form nome nome_pos nome_lt_one a .unit) (form nome nome_pos nome_lt_one e e) :=
    (leEv_congr (CRealAlg.cmul_comm r (rawLimit nome nome_pos nome_lt_one a .unit))
      (CRealAlg.cmul_comm r (rawLimit nome nome_pos nome_lt_one e e))).mp hmul
  have hunit : Equiv (form nome nome_pos nome_lt_one a .unit) (ofQ' normalizedFloor) :=
    (form_smul_left nome nome_pos nome_lt_one normalizedFloor (.unit : PlaquetteExpression half) .unit).trans
      ((Pivot2.mul_congr_right (form_unit nome nome_pos nome_lt_one half)).trans (CRealAlg.cmul_cone (ofQ' normalizedFloor)))
  exact leEv_trans (leEv_of_equiv hunit.symm) hform

variable (half : Nat)
local notation "D" => seminorm nome nome_pos nome_lt_one half
local notation "B" => completedInner nome nome_pos nome_lt_one

def centeredRepresentative : (D).Cauchy :=
  centerCauchy nome nome_pos nome_lt_one ((D).constant (bulkProbe half))

def centeredCoefficient (n : Nat) : Q' :=
  (unitCoefficient nome nome_pos nome_lt_one ((D).constant (bulkProbe half))).approx n

theorem centeredRepresentative_seq (n : Nat) :
    expressionEqv ((centeredRepresentative half).seq n) (recentered half (bulkProbe half) (centeredCoefficient half n)) := by
  have hs : RatPolyCoeffEqv (polySmul (-1) (polySmul (centeredCoefficient half n) polyOne))
      (polySmul (-(centeredCoefficient half n)) polyOne) :=
    (RatPolyCoeffEqv.smul_assoc _ _ _).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))) polyOne)
  exact ⟨(RatPolyCoeffEqv.refl (lower (bulkProbe half))).add hs, (RatPolyCoeffEqv.refl (upper (bulkProbe half))).add hs⟩

theorem centeredRepresentative_form_floor (n : Nat) :
    leEv (ofQ' normalizedFloor)
      (form nome nome_pos nome_lt_one ((centeredRepresentative half).seq n) ((centeredRepresentative half).seq n)) :=
  leEv_trans (normalized_form_floor half (centeredCoefficient half n))
    (leEv_of_equiv (form_congr nome nome_pos nome_lt_one (centeredRepresentative_seq half n) (centeredRepresentative_seq half n)).symm)

def normRepresentative : CReal :=
  representativeInner nome nome_pos nome_lt_one (centeredRepresentative half) (centeredRepresentative half)

def normCauchy : QCauchy (normRepresentative half).approx :=
  representativeInnerCauchy nome nome_pos nome_lt_one (centeredRepresentative half) (centeredRepresentative half)

theorem norm_floor : leEv (ofQ' normalizedFloor) (normRepresentative half) :=
  leEv_of_convergesTo_le (convergesTo_const (ofQ' normalizedFloor))
    (pairSequence_converges nome nome_pos nome_lt_one (centeredRepresentative half) (centeredRepresentative half))
    (centeredRepresentative_form_floor half)

def state : UnitComplement nome nome_pos nome_lt_one half :=
  centeredState nome nome_pos nome_lt_one (embedExpression nome nome_pos nome_lt_one (bulkProbe half))

theorem norm_pin : Quotient.mk crealSetoid (normRepresentative half) = B (state half).val (state half).val := rfl

theorem state_norm_floor : RCle (Quotient.mk crealSetoid (ofQ' normalizedFloor)) (B (state half).val (state half).val) := by
  rw [← norm_pin]
  exact norm_floor half

/-- The exact connected covariance used by the thermodynamic sequence. -/
theorem connectedCovariance_floor :
    leEv (ofQ' normalizedFloor) (connectedCovariance nome nome_pos nome_lt_one (bulkProbe half) (bulkProbe half)) := by
  have h := state_norm_floor half
  have hp : B (state half).val (state half).val =
      Quotient.mk crealSetoid (connectedCovariance nome nome_pos nome_lt_one (bulkProbe half) (bulkProbe half)) :=
    connectedCovariance_pairing nome nome_pos nome_lt_one (bulkProbe half) (bulkProbe half)
  rw [hp] at h
  exact h

end YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normalizedFloor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normalizedFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normalizedFloor_twice
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.rawForm_fullPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.rawLimit_scaledUnit_le
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normalized_form_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.centeredRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.centeredCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.centeredRepresentative_seq
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.centeredRepresentative_form_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.normCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.state
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.state_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeNormalizedFloor.connectedCovariance_floor
