/-
# Choice-free mixed-pairing completion on the same squared-seminorm quotient

Computed closeness rates prove that the representative scalar limit is
independent of both supplied representatives. Quotient.lift₂ constructs
the completed pairing on D.Completion itself. Dense symmetry and diagonal
positivity, when supplied, pass through these same scalar limits.

No stream uniform bound, completed pairing, selected representative,
metric completeness or positive-definiteness assumption is introduced.
-/

import YMGap.Continuum.CRealSeminormPairingCompletionLimit
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.CRealSeminormPairingCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

variable {D : SquaredSeminorm} (P : PairingData D)

/-- The changed first and original second representatives supply the two
computed ceilings; both given closeness moduli remain explicit. -/
def closeRate {X X' Y Y' : D.Cauchy} (hX : D.Close X X') (hY : D.Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase P X') (normBase P Y))
    (max (hX.modulus (pairDelta P X' Y epsilon))
      (hY.modulus (pairDelta P X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : D.Cauchy}
    (hX : D.Close X X') (hY : D.Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate P hX hY epsilon ≤ n) :
    leRat (sub (pairSequence P X Y n)
      (pairSequence P X' Y' n)) epsilon ∧
    leRat (sub (pairSequence P X' Y' n)
      (pairSequence P X Y n)) epsilon := by
  let B := pairCeiling P X' Y
  let hB := pairCeiling_nonnegative P X' Y
  let delta := pairDelta P X' Y epsilon
  have hdeltaPos : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase P X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase P Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact P.pairing_close (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
    B hB epsilon he (hX.close delta hdeltaPos n hnX) (hY.close delta hdeltaPos n hnY')
    (leRat_mono (diagonal_le_normCeiling P Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling P X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : D.Cauchy}
    (hX : D.Close X X') (hY : D.Close Y Y') :
    Equiv (representativeInner P X Y)
      (representativeInner P X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges P X Y)
    (pairSequence_converges P X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate P hX hY (HalfPow.half*epsilon), fun n hn => ?_⟩
  have h := pairSequence_close P hX hY (HalfPow.half*epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Quotient descent on the SAME supplied squared-seminorm completion. -/
def completedInner : D.Completion → D.Completion → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner P X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef P hX hY))

theorem completedInner_mk (X Y : D.Cauchy) :
    completedInner P
      (Quotient.mk D.completionSetoid X) (Quotient.mk D.completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner P X Y) := rfl

theorem representativeInner_constant (x y : D.Carrier) :
    Equiv (representativeInner P (D.constant x) (D.constant y))
      (P.pairing x y) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (P.pairing x y))
    (pairSequence_converges P (D.constant x) (D.constant y))
    (convergesTo_const (P.pairing x y))

/-- Dense constants retain the supplied actual pairing. -/
theorem completedInner_embedRep (x y : D.Carrier) :
    completedInner P
      (D.embedRep x) (D.embedRep y) =
      Quotient.mk crealSetoid (P.pairing x y) :=
  Quotient.sound (representativeInner_constant P x y)

theorem representativeInner_symm
    (hsymm : ∀ x y, Equiv (P.pairing x y) (P.pairing y x)) (X Y : D.Cauchy) :
    Equiv (representativeInner P X Y)
      (representativeInner P Y X) :=
  Equiv_of_limit_of_equal
    (fun n => hsymm (X.seq n) (Y.seq n))
    (pairSequence_converges P X Y)
    (pairSequence_converges P Y X)

theorem completedInner_symm
    (hsymm : ∀ x y, Equiv (P.pairing x y) (P.pairing y x)) (x y : D.Completion) :
    completedInner P x y = completedInner P y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm P hsymm X Y)

theorem representativeInner_nonnegative
    (hpos : ∀ x, leEv czero (P.pairing x x)) (X : D.Cauchy) :
    leEv czero (representativeInner P X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges P X X)
    (fun n => hpos (X.seq n))

theorem completedInner_nonnegative
    (hpos : ∀ x, leEv czero (P.pairing x x)) (x : D.Completion) :
    RCnonneg (completedInner P x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative P hpos

/-- Uniqueness uses the actual dense scalar sequence, regardless of which
explicit inner or outer moduli another construction used. -/
theorem representativeInner_unique (X Y : D.Cauchy) (L : CReal)
    (hL : ConvergesTo (pairSequence P X Y) L) :
    Equiv (representativeInner P X Y) L :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl _)
    (pairSequence_converges P X Y) hL

theorem completedInner_unit_norm_one (u : D.Carrier)
    (hu : Equiv (P.pairing u u) cone) :
    completedInner P (D.embedRep u) (D.embedRep u) = Quotient.mk crealSetoid cone := by
  rw [completedInner_embedRep]
  exact Quotient.sound hu

end YMGap.Continuum.CRealSeminormPairingCompletion

#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.closeRate
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_close
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_welldef
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_mk
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_constant
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_embedRep
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_symm
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_symm
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_unique
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_unit_norm_one
