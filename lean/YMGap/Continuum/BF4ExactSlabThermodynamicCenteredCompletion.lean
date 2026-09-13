/-
# Original thermodynamic centering and SAME connected-covariance realization

Subtracting the constructed projection onto the SAME original unit gives
a linear, self-adjoint, idempotent and nonexpansive centering map.
The mixed Pythagorean identity has no norm loss. On embedded observables,
its pairing is exactly the previously constructed ORIGINAL connected form;
on common-base expressions it is the original covariance limit.

Centered representatives and their mixed-pairing CReal/QCauchy data are
constructed, not selected. This is the unit complement, not a stationary
physical vacuum, nonzero excitation, physical time operator or strict gap.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance (covarianceLimit covarianceSequence)
open YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate
  (covarianceAmplitude covarianceVolumeModulus covariance_geometric_bound covariance_error_le)
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate)
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection

private theorem rc_negative_one (a : RC) : RCmul (Quotient.mk crealSetoid (ofQ' (-1))) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n)) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_neg_self_eqv (B.approx n))))
        (QPoly.q_add_zero_eqv (A.approx n)))))

local notation "D" => seminorm
local notation "u" => completedUnit
local notation "B" => completedInner
local notation "P" => unitProjection

theorem completedInner_neg_left (x y : Completion) :
    B (completedNeg x) y = RCneg (B x y) := by
  change B (completedSmul (-1) x) y = _
  rw [completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_left (x y z : Completion) :
    B (completedSub x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub RCsub
  rw [completedInner_add_left, completedInner_neg_left]

theorem completedInner_sub_right (x y z : Completion) :
    B x (completedSub y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm x, completedInner_sub_left,
    completedInner_symm y x, completedInner_symm z x]

theorem completedSub_zero (x : Completion) :
    completedSub x (completedZero) = x := by
  have h := completedSub_add_cancel x (completedZero)
  rw [completedAdd_zero] at h
  exact h

def center (x : Completion) : Completion := completedSub x (P x)

/-- The centered representative retains the explicit original coefficient/scalar moduli. -/
def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy X (unitProjectionCauchy X)

theorem center_mk (X : (D).Cauchy) :
    center (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy X) := rfl

theorem center_pairing (x y : Completion) :
    B (center x) y = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  unfold center
  rw [completedInner_sub_left, unitProjection_pairing]

theorem center_selfAdjoint (x y : Completion) :
    B (center x) y = B x (center y) := by
  unfold center
  rw [completedInner_sub_left, completedInner_sub_right, unitProjection_selfAdjoint]

theorem center_orthogonal (x : Completion) : B (center x) u = RCzero := by
  unfold center
  rw [completedInner_sub_left, unitProjection_coefficient, rc_sub_self]

theorem center_fixed_iff (x : Completion) : center x = x ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← h]
    exact center_orthogonal x
  · intro h
    unfold center
    rw [(unitProjection_zero_iff x).mpr h, completedSub_zero]

theorem center_idempotent (x : Completion) :
    center (center x) = center x :=
  (center_fixed_iff _).mpr (center_orthogonal x)

theorem center_unit : center u = completedZero := by
  unfold center
  rw [unitProjection_unit, completedSub_self]

theorem center_zero : center (completedZero) = completedZero :=
  (center_fixed_iff _).mpr (completedInner_zero_left u)

theorem unitProjection_center (x : Completion) : P (center x) = completedZero :=
  (unitProjection_zero_iff _).mpr (center_orthogonal x)

theorem center_unitProjection (x : Completion) : center (P x) = completedZero := by
  unfold center
  rw [unitProjection_idempotent, completedSub_self]

theorem center_decomposition (x : Completion) :
    completedAdd (center x) (P x) = x := completedSub_add_cancel x (P x)

theorem center_add (x y : Completion) :
    center (completedAdd x y) =
      completedAdd (center x) (center y) := by
  apply completed_eq_of_pairings
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left, center_selfAdjoint, center_selfAdjoint]

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    center (completedRealSmul s cs x) =
      completedRealSmul s cs (center x) := by
  apply completed_eq_of_pairings
  intro y
  rw [center_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left, center_selfAdjoint]

theorem center_sub (x y : Completion) :
    center (completedSub x y) =
      completedSub (center x) (center y) := by
  apply completed_eq_of_pairings
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left, center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : Completion) :
    B (center x) (center y) = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Pythagoras, including mixed pairings, on the actual original carrier. -/
theorem orthogonal_decomposition_inner (x y : Completion) :
    RCadd (B (center x) (center y)) (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : Completion) :
    RCle (B (center x) (center x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (center x) (center x)))
    (completedInner_nonnegative (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem center_nonexpansive (x y : Completion) :
    RCle (completedDist (center x) (center y)) (completedDist x y) := by
  unfold completedDist
  rw [← center_sub]
  exact center_norm_le (completedSub x y)

/-- Exactly the unit-orthogonal subspace; no nonzero vector is asserted. -/
def UnitComplement : Type := {x : Completion // B x (completedUnit) = RCzero}

def centeredState (x : Completion) : UnitComplement :=
  ⟨center x, center_orthogonal x⟩

theorem centeredState_fixes (x : UnitComplement) : centeredState x.val = x :=
  Subtype.ext ((center_fixed_iff x.val).mpr x.property)

/-- Exactly the preceding ORIGINAL semantic connected form, on completed centered states. -/
theorem centered_inner_embedObservable (x y : Observable) :
    B (center (embedObservable x)) (center (embedObservable y)) = connectedPairing x y := by
  rw [centered_inner]
  change RCsub (B (embedObservable x) (embedObservable y))
    (RCmul (B (embedObservable x) (embedObservable unit))
      (B (embedObservable unit) (embedObservable y))) = _
  rw [completedInner_embedObservable, completedInner_embedObservable, completedInner_embedObservable,
    pairing_unit_right_value, pairing_unit_left_value]
  rfl

theorem centered_inner_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    B (center (embedPresentation ⟨base,e⟩)) (center (embedPresentation ⟨base,f⟩)) =
      Quotient.mk crealSetoid (BF4ExactSlabThermodynamicConnectedCovariance.covarianceLimit e f) :=
  (centered_inner_embedObservable (embed ⟨base,e⟩) (embed ⟨base,f⟩)).trans (connectedPairing_sameBase e f)

/-- The actual centered pairing representative, its modulus and its completed value pin. -/
def centeredPairingRepresentative (p q : Presentation) :
    Σ' r : CReal, QCauchy r.approx ×'
      (B (center (embedPresentation p)) (center (embedPresentation q)) = Quotient.mk crealSetoid r) :=
  ⟨representativeInner (centerCauchy ((D).constant p)) (centerCauchy ((D).constant q)),
    representativeInnerCauchy (centerCauchy ((D).constant p)) (centerCauchy ((D).constant q)), rfl⟩

theorem centeredPairingRepresentative_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (centeredPairingRepresentative ⟨base,e⟩ ⟨base,f⟩).1 (covarianceLimit e f) := by
  apply Quotient.exact (s := crealSetoid)
  exact (centeredPairingRepresentative ⟨base,e⟩ ⟨base,f⟩).2.2.symm.trans (centered_inner_sameBase e f)

/-- The old boundary-error estimate now bounds the actual completed centered pairing. -/
theorem centeredPairing_geometric_bound {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (centeredPairingRepresentative ⟨base,e⟩ ⟨base,f⟩).1
        (covarianceSequence e f margin)))
      (ofQ' (covarianceAmplitude e f * rate^(margin+1-boxSize base))) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr
    (CReal.sub_congr_left (centeredPairingRepresentative_sameBase e f))))
    (covariance_geometric_bound e f margin)

theorem centeredPairing_error_le {base : Nat} (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : covarianceVolumeModulus e f epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (centeredPairingRepresentative ⟨base,e⟩ ⟨base,f⟩).1
        (covarianceSequence e f margin))) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr
    (CReal.sub_congr_left (centeredPairingRepresentative_sameBase e f))))
    (covariance_error_le e f epsilon he margin hm)

end YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.completedInner_neg_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.completedInner_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.completedInner_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.completedSub_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_fixed_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.unitProjection_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_decomposition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centered_inner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.orthogonal_decomposition_inner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.center_nonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.UnitComplement
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredState_fixes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centered_inner_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centered_inner_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredPairingRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredPairingRepresentative_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredPairing_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion.centeredPairing_error_le
