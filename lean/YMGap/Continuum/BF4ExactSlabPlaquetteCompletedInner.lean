/-
# Mixed pairing on the actual ORIGINAL plaquette completion

Explicit same-index closeness rates prove independence of both Cauchy
representatives. The resulting RC-valued pairing descends to the actual
seminorm completion, agrees with the original normalized reflected form
on embedded expressions and the null quotient, and is symmetric and
positive with unit diagonal one.

This is the completed pairing, not yet a full Hilbert-space package:
completed linear operations, their laws, positive definiteness and the
appropriate completeness theorem remain subsequent obligations. No
physical transfer, stationary vacuum or spectral gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

/-- The norm bound only needs the changed first and original second vectors. -/
def closeRate {X X' Y Y' : (D).Cauchy} (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase w hw0 hw1 X') (normBase w hw0 hw1 Y))
    (max (hX.modulus (pairDelta w hw0 hw1 X' Y epsilon))
      (hY.modulus (pairDelta w hw0 hw1 X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate w hw0 hw1 hX hY epsilon ≤ n) :
    leRat (CReal.sub (pairSequence w hw0 hw1 X Y n) (pairSequence w hw0 hw1 X' Y' n)) epsilon ∧
    leRat (CReal.sub (pairSequence w hw0 hw1 X' Y' n) (pairSequence w hw0 hw1 X Y n)) epsilon := by
  let B := pairCeiling w hw0 hw1 X' Y
  let hB := pairCeiling_nonnegative w hw0 hw1 X' Y
  let delta := pairDelta w hw0 hw1 X' Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase w hw0 hw1 X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase w hw0 hw1 Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close w hw0 hw1 (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n) B hB epsilon he
    (hX.close delta hd n hnX) (hY.close delta hd n hnY')
    (leRat_mono (diagonal_le_normCeiling w hw0 hw1 Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling w hw0 hw1 X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y') :
    Equiv (representativeInner w hw0 hw1 X Y) (representativeInner w hw0 hw1 X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges w hw0 hw1 X Y)
    (pairSequence_converges w hw0 hw1 X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate w hw0 hw1 hX hY (HalfPow.half * epsilon), fun n hn => ?_⟩
  have h := pairSequence_close w hw0 hw1 hX hY (HalfPow.half * epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- No representative is selected: the same-object pairing descends by quotient elimination. -/
def completedInner : Completion w hw0 hw1 half → Completion w hw0 hw1 half → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner w hw0 hw1 X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef w hw0 hw1 hX hY))

theorem completedInner_mk (X Y : (D).Cauchy) :
    completedInner w hw0 hw1 (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner w hw0 hw1 X Y) := rfl

theorem representativeInner_constant (e f : PlaquetteExpression half) :
    Equiv (representativeInner w hw0 hw1 ((D).constant e) ((D).constant f)) (form w hw0 hw1 e f) :=
  Equiv_of_limit_of_equal (fun _ => CReal.Equiv.refl (form w hw0 hw1 e f))
    (pairSequence_converges w hw0 hw1 ((D).constant e) ((D).constant f))
    (convergesTo_const (form w hw0 hw1 e f))

theorem completedInner_embedExpression (e f : PlaquetteExpression half) :
    completedInner w hw0 hw1 (embedExpression w hw0 hw1 e) (embedExpression w hw0 hw1 f) =
      pairing w hw0 hw1 e f :=
  Quotient.sound (representativeInner_constant w hw0 hw1 e f)

theorem completedInner_embedQuotient (x y : Carrier w hw0 hw1 half) :
    completedInner w hw0 hw1 (embedQuotient w hw0 hw1 x) (embedQuotient w hw0 hw1 y) =
      inner w hw0 hw1 x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedInner_embedExpression w hw0 hw1

theorem representativeInner_symm (X Y : (D).Cauchy) :
    Equiv (representativeInner w hw0 hw1 X Y) (representativeInner w hw0 hw1 Y X) :=
  Equiv_of_limit_of_equal (fun n => form_symm w hw0 hw1 (X.seq n) (Y.seq n))
    (pairSequence_converges w hw0 hw1 X Y) (pairSequence_converges w hw0 hw1 Y X)

theorem completedInner_symm (x y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x y = completedInner w hw0 hw1 y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm w hw0 hw1 X Y)

theorem representativeInner_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner w hw0 hw1 X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero) (pairSequence_converges w hw0 hw1 X X)
    (fun n => form_nonnegative w hw0 hw1 (X.seq n))

theorem completedInner_nonnegative (x : Completion w hw0 hw1 half) :
    RCnonneg (completedInner w hw0 hw1 x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative w hw0 hw1

theorem completedUnit_norm_one (half : Nat) :
    completedInner w hw0 hw1 (completedUnit w hw0 hw1 half) (completedUnit w hw0 hw1 half) = Quotient.mk crealSetoid cone := by
  change completedInner w hw0 hw1 (embedExpression w hw0 hw1 .unit) (embedExpression w hw0 hw1 .unit) = Quotient.mk crealSetoid cone
  rw [completedInner_embedExpression]
  exact Quotient.sound (form_unit w hw0 hw1 half)

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.pairSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.representativeInner_welldef
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.representativeInner_constant
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner_embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner_embedQuotient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.representativeInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.representativeInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner.completedUnit_norm_one
