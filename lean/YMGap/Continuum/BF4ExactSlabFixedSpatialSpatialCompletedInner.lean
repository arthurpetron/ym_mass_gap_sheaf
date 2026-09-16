/-
# Actual spatial limiting pairing on its SAME Cauchy completion

The explicit closeness moduli control the constructed mixed scalar limits.
Quotient elimination descends them to the existing SpatialCompletion,
without choosing representatives or identifying fixed-width completions.
The embedding pin is the actual spatialPairing of original presentations.
Symmetry, positivity and unit normalization pass through the same limits.

Completed linearity, positive definiteness, centering and the strict gap
are not asserted here, nor are metric completeness or continuum closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

/-- The changed first and original second representatives supply the two
computed ceilings; both given closeness moduli remain explicit. -/
def closeRate {X X' Y Y' : (D).Cauchy} (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 base hsmall hd hs hb X') (normBase hw0 hw1 base hsmall hd hs hb Y))
    (max (hX.modulus (pairDelta hw0 hw1 base hsmall hd hs hb X' Y epsilon))
      (hY.modulus (pairDelta hw0 hw1 base hsmall hd hs hb X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate hw0 hw1 base hsmall hd hs hb hX hY epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 base hsmall hd hs hb X Y n)
      (pairSequence hw0 hw1 base hsmall hd hs hb X' Y' n)) epsilon ∧
    leRat (sub (pairSequence hw0 hw1 base hsmall hd hs hb X' Y' n)
      (pairSequence hw0 hw1 base hsmall hd hs hb X Y n)) epsilon := by
  let B := pairCeiling hw0 hw1 base hsmall hd hs hb X' Y
  let hB := pairCeiling_nonnegative hw0 hw1 base hsmall hd hs hb X' Y
  let delta := pairDelta hw0 hw1 base hsmall hd hs hb X' Y epsilon
  have hdeltaPos : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase hw0 hw1 base hsmall hd hs hb X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase hw0 hw1 base hsmall hd hs hb Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 base hsmall hd hs hb (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
    B hB epsilon he (hX.close delta hdeltaPos n hnX) (hY.close delta hdeltaPos n hnY')
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 base hsmall hd hs hb Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 base hsmall hd hs hb X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y') :
    Equiv (representativeInner hw0 hw1 base hsmall hd hs hb X Y)
      (representativeInner hw0 hw1 base hsmall hd hs hb X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges hw0 hw1 base hsmall hd hs hb X Y)
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate hw0 hw1 base hsmall hd hs hb hX hY (HalfPow.half*epsilon), fun n hn => ?_⟩
  have h := pairSequence_close hw0 hw1 base hsmall hd hs hb hX hY (HalfPow.half*epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Quotient descent on the SAME actual spatial-completion carrier. -/
def completedInner : SpatialCompletion hw0 hw1 base hsmall hd hs hb → SpatialCompletion hw0 hw1 base hsmall hd hs hb → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner hw0 hw1 base hsmall hd hs hb X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef hw0 hw1 base hsmall hd hs hb hX hY))

theorem completedInner_mk (X Y : (D).Cauchy) :
    completedInner hw0 hw1 base hsmall hd hs hb
      (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner hw0 hw1 base hsmall hd hs hb X Y) := rfl

theorem representativeInner_constant (x y : PhysicalSpan base) :
    Equiv (representativeInner hw0 hw1 base hsmall hd hs hb ((D).constant x) ((D).constant y))
      (spatialPairing hw0 hw1 base hsmall hd hs hb x y) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (spatialPairing hw0 hw1 base hsmall hd hs hb x y))
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb ((D).constant x) ((D).constant y))
    (convergesTo_const (spatialPairing hw0 hw1 base hsmall hd hs hb x y))

/-- On every original physical presentation, the completed pairing is
exactly its proved spatial/cutoff/boundary-time scalar, not a new form. -/
theorem completedInner_embedSpan (x y : PhysicalSpan base) :
    completedInner hw0 hw1 base hsmall hd hs hb
      (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb x) (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb y) =
      Quotient.mk crealSetoid (spatialPairing hw0 hw1 base hsmall hd hs hb x y) :=
  Quotient.sound (representativeInner_constant hw0 hw1 base hsmall hd hs hb x y)

theorem representativeInner_symm (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 base hsmall hd hs hb X Y)
      (representativeInner hw0 hw1 base hsmall hd hs hb Y X) :=
  Equiv_of_limit_of_equal
    (fun n => spatialPairing_symm hw0 hw1 base hsmall hd hs hb (X.seq n) (Y.seq n))
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb X Y)
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb Y X)

theorem completedInner_symm (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    completedInner hw0 hw1 base hsmall hd hs hb x y = completedInner hw0 hw1 base hsmall hd hs hb y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm hw0 hw1 base hsmall hd hs hb X Y)

theorem representativeInner_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner hw0 hw1 base hsmall hd hs hb X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb X X)
    (fun n => spatialPairing_nonnegative hw0 hw1 base hsmall hd hs hb (X.seq n))

theorem completedInner_nonnegative (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    RCnonneg (completedInner hw0 hw1 base hsmall hd hs hb x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative hw0 hw1 base hsmall hd hs hb

theorem completedUnit_norm_one :
    completedInner hw0 hw1 base hsmall hd hs hb (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb)
      (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb) = Quotient.mk crealSetoid cone := by
  unfold spatialCompletedUnit
  rw [completedInner_embedSpan]
  exact Quotient.sound (spatialPairing_unit_unit hw0 hw1 base hsmall hd hs hb)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.pairSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.representativeInner_welldef
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.representativeInner_constant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.representativeInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.representativeInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner.completedUnit_norm_one
