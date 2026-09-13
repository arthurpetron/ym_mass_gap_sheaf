/-
# A nonzero centered state in the ORIGINAL completed plaquette space

The original raw reflected-norm floor passes through representation-cutoff
removal and multiplication by the SAME original partition reciprocal. The
resulting rational floor is independent of every rational centering value.
It therefore survives the actual modulated Cauchy representative of exact
orthogonal centering. The returned state lies in the existing original
unit complement and has strictly positive completed squared norm.

All constructions are at the certified nome 1/1024 and extent-one slab.
The norm representative and its QCauchy modulus are returned explicitly.
The unit is NOT thereby identified as a stationary physical vacuum. No
time transfer, physical spectral gap, inter-slab compatibility, general
observable realization, or volume/spacing/continuum construction follows.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor
import YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
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
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local notation "D" => seminorm nome nome_pos nome_lt_one 0
local notation "B" => completedInner nome nome_pos nome_lt_one
local notation "lambda" => actionReciprocal nome nome_pos nome_lt_one 0

theorem rawLimit_floor (c : Q') :
    leEv (ofQ' rawFloor) (rawLimit nome nome_pos nome_lt_one (recentered 0 probe c) (recentered 0 probe c)) :=
  leEv_of_ofQ'_limit_le (convergesTo_const (ofQ' rawFloor))
    (rawLimit_converges nome nome_pos nome_lt_one (recentered 0 probe c) (recentered 0 probe c))
    (fun epsilon he => ⟨1, fun K hK => Q'.le_trans' _ _ _ (rawFloor_bound K hK c)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩)

/-- Positive witness uses the computed reciprocal floor of the SAME action. -/
def normalizedFloor : Q' := rawFloor * reciprocalFloor nome nome_pos 0

theorem normalizedFloor_pos : (0 : Q') < normalizedFloor :=
  Q'.mul_pos rawFloor_pos (reciprocalFloor_pos nome nome_pos 0)

theorem normalized_form_floor (c : Q') :
    leEv (ofQ' normalizedFloor) (form nome nome_pos nome_lt_one (recentered 0 probe c) (recentered 0 probe c)) := by
  have hrec : leEv (ofQ' (reciprocalFloor nome nome_pos 0)) lambda :=
    leEv_ofQ'_of_approx_ge (actionReciprocal_approx_ge nome nome_pos nome_lt_one 0)
  have hraw : leEv czero (ofQ' rawFloor) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt rawFloor_pos)
  have hfirst := leEv_mul_nonneg_left hraw hrec
  have hlast := leEv_mul_nonneg_left (reciprocal_nonnegative nome nome_pos nome_lt_one 0) (rawLimit_floor c)
  have hsecond : leEv (CReal.mul (ofQ' rawFloor) lambda)
      (form nome nome_pos nome_lt_one (recentered 0 probe c) (recentered 0 probe c)) :=
    (leEv_congr (CRealAlg.cmul_comm lambda (ofQ' rawFloor))
      (CRealAlg.cmul_comm lambda (rawLimit nome nome_pos nome_lt_one (recentered 0 probe c) (recentered 0 probe c)))).mp hlast
  exact leEv_trans (leEv_of_equiv (CRealAlg.ofQ'_mul rawFloor (reciprocalFloor nome nome_pos 0)))
    (leEv_trans hfirst hsecond)

def centeredRepresentative : (D).Cauchy :=
  centerCauchy nome nome_pos nome_lt_one ((D).constant probe)

def centeredCoefficient (n : Nat) : Q' :=
  (unitCoefficient nome nome_pos nome_lt_one ((D).constant probe)).approx n

theorem centeredRepresentative_seq (n : Nat) :
    expressionEqv (centeredRepresentative.seq n) (recentered 0 probe (centeredCoefficient n)) := by
  have hs : RatPolyCoeffEqv (polySmul (-1) (polySmul (centeredCoefficient n) polyOne))
      (polySmul (-(centeredCoefficient n)) polyOne) :=
    (RatPolyCoeffEqv.smul_assoc _ _ _).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))) polyOne)
  exact ⟨(RatPolyCoeffEqv.refl (lower probe)).add hs, (RatPolyCoeffEqv.refl (upper probe)).add hs⟩

theorem centeredRepresentative_form_floor (n : Nat) :
    leEv (ofQ' normalizedFloor)
      (form nome nome_pos nome_lt_one (centeredRepresentative.seq n) (centeredRepresentative.seq n)) :=
  leEv_trans (normalized_form_floor (centeredCoefficient n))
    (leEv_of_equiv (form_congr nome nome_pos nome_lt_one (centeredRepresentative_seq n) (centeredRepresentative_seq n)).symm)

def normRepresentative : CReal :=
  representativeInner nome nome_pos nome_lt_one centeredRepresentative centeredRepresentative

def normCauchy : QCauchy normRepresentative.approx :=
  representativeInnerCauchy nome nome_pos nome_lt_one centeredRepresentative centeredRepresentative

theorem norm_floor : leEv (ofQ' normalizedFloor) normRepresentative :=
  leEv_of_convergesTo_le (convergesTo_const (ofQ' normalizedFloor))
    (pairSequence_converges nome nome_pos nome_lt_one centeredRepresentative centeredRepresentative)
    centeredRepresentative_form_floor

/-- An actual element of the existing unit complement, not a surrogate carrier. -/
def state : UnitComplement nome nome_pos nome_lt_one 0 :=
  centeredState nome nome_pos nome_lt_one (embedExpression nome nome_pos nome_lt_one probe)

theorem norm_pin : Quotient.mk crealSetoid normRepresentative = B state.val state.val := rfl

theorem state_norm_floor : RCle (Quotient.mk crealSetoid (ofQ' normalizedFloor)) (B state.val state.val) := by
  rw [← norm_pin]
  exact norm_floor

theorem state_orthogonal : B state.val (completedUnit nome nome_pos nome_lt_one 0) = RCzero := state.property

theorem state_ne_zero : state.val ≠ completedZero nome nome_pos nome_lt_one 0 := by
  intro hz
  have h := state_norm_floor
  rw [hz, completedInner_zero_left] at h
  have hle : normalizedFloor ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q')) (Q'.pos_of_lt_of_le normalizedFloor_pos hle)

theorem connectedCovariance_floor :
    leEv (ofQ' normalizedFloor) (connectedCovariance nome nome_pos nome_lt_one probe probe) := by
  have h := state_norm_floor
  have hp : B state.val state.val = Quotient.mk crealSetoid (connectedCovariance nome nome_pos nome_lt_one probe probe) :=
    connectedCovariance_pairing nome nome_pos nome_lt_one probe probe
  rw [hp] at h
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.rawLimit_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normalizedFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normalizedFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normalized_form_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.centeredRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.centeredCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.centeredRepresentative_seq
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.centeredRepresentative_form_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.state
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.state_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.state_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.state_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.connectedCovariance_floor
