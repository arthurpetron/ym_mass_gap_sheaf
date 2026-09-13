/-
# The SAME original thermodynamic pairing on Cauchy classes

Computed same-index closeness rates prove independence of both Cauchy
representatives. Quotient elimination, without selecting representatives,
gives the RC-valued pairing on the already-constructed completion carrier.

It agrees with the original semantic OS pairing on embedded observables
and the positive-definite OS quotient. Symmetry, positivity, normalization,
the original unit coefficient and sharp CS all persist in this SAME pairing.
Completed linear operations, positive definiteness on all Cauchy classes
and full quotient-level completeness are subsequent obligations; physical
time, stationary vacuum, excitation, gap and continuum are not asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
import YMGap.Constructive.CRealLimitClose
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

local notation "D" => seminorm

/-- The norm bound only needs the changed first and original second vectors. -/
def closeRate {X X' Y Y' : (D).Cauchy} (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase X') (normBase Y))
    (max (hX.modulus (pairDelta X' Y epsilon))
      (hY.modulus (pairDelta X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate hX hY epsilon ≤ n) :
    leRat (CReal.sub (pairSequence X Y n) (pairSequence X' Y' n)) epsilon ∧
    leRat (CReal.sub (pairSequence X' Y' n) (pairSequence X Y n)) epsilon := by
  let B := pairCeiling X' Y
  let hB := pairCeiling_nonnegative X' Y
  let delta := pairDelta X' Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n) B hB epsilon he
    (hX.close delta hd n hnX) (hY.close delta hd n hnY')
    (leRat_mono (diagonal_le_normCeiling Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y') :
    Equiv (representativeInner X Y) (representativeInner X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges X Y)
    (pairSequence_converges X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate hX hY (HalfPow.half * epsilon), fun n hn => ?_⟩
  have h := pairSequence_close hX hY (HalfPow.half * epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- No representative is selected: the same-object pairing descends by quotient elimination. -/
def completedInner : Completion → Completion → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef hX hY))

theorem completedInner_mk (X Y : (D).Cauchy) :
    completedInner (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner X Y) := rfl

theorem representativeInner_constant (e f : Presentation) :
    Equiv (representativeInner ((D).constant e) ((D).constant f)) (presentedForm e f) :=
  Equiv_of_limit_of_equal (fun _ => CReal.Equiv.refl (presentedForm e f))
    (pairSequence_converges ((D).constant e) ((D).constant f))
    (convergesTo_const (presentedForm e f))

theorem completedInner_embedPresentation (p q : Presentation) :
    completedInner (embedPresentation p) (embedPresentation q) = pairing (embed p) (embed q) :=
  Quotient.sound (representativeInner_constant p q)

theorem completedInner_embedObservable (x y : Observable) :
    completedInner (embedObservable x) (embedObservable y) = pairing x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedInner_embedPresentation

theorem completedInner_embedOSQuotient (x y : Carrier) :
    completedInner (embedOSQuotient x) (embedOSQuotient y) = inner x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedInner_embedObservable

theorem representativeInner_symm (X Y : (D).Cauchy) :
    Equiv (representativeInner X Y) (representativeInner Y X) :=
  Equiv_of_limit_of_equal (fun n => presentedForm_symm (X.seq n) (Y.seq n))
    (pairSequence_converges X Y) (pairSequence_converges Y X)

theorem completedInner_symm (x y : Completion) :
    completedInner x y = completedInner y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm X Y)

theorem representativeInner_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero) (pairSequence_converges X X)
    (fun n => presentedForm_nonnegative (X.seq n))

theorem completedInner_nonnegative (x : Completion) :
    RCnonneg (completedInner x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative

theorem completedUnit_norm_one :
    completedInner completedUnit completedUnit = Quotient.mk crealSetoid cone := by
  change completedInner (embedOSQuotient osUnit) (embedOSQuotient osUnit) = Quotient.mk crealSetoid cone
  rw [completedInner_embedOSQuotient]
  exact unit_norm_one

theorem completedInner_unitCoefficient (x : Carrier) :
    completedInner completedUnit (embedOSQuotient x) = unitCoefficient x := by
  change completedInner (embedOSQuotient osUnit) (embedOSQuotient x) = unitCoefficient x
  rw [completedInner_embedOSQuotient]
  exact inner_unit_coefficient x

theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv (CReal.mul (representativeInner X Y) (representativeInner X Y))
      (CReal.mul (representativeInner X X) (representativeInner Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges X Y) (pairSequence_converges X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges X X) (pairSequence_converges Y Y))
    (fun n => presentedForm_cauchySchwarz (X.seq n) (Y.seq n))

theorem completedInner_cauchySchwarz (x y : Completion) :
    RCle (RCmul (completedInner x y) (completedInner x y))
      (RCmul (completedInner x x) (completedInner y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.pairSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.representativeInner_welldef
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.representativeInner_constant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.representativeInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.representativeInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedUnit_norm_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_unitCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.representativeInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner.completedInner_cauchySchwarz
