/-
# The original intrinsic reflected pairing on its physical Cauchy carrier

Explicit closeness moduli make the constructed scalar limit independent of
both representatives. Quotient elimination, not representative selection,
then defines an RC-valued pairing on the SAME carrier already equipped with
physical time. It retains the original dense pairing, symmetry, positivity
and unit normalization.

This is not yet a full Hilbert-space construction: completed linear laws,
positive definiteness and metric completeness remain separate obligations.
Fixed nome, width and retained heat cutoff remain; no strict gap, isolated
vacuum, continuum or all-group assertion is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

/-- The changed first and original second representatives supply the ceilings. -/
def closeRate {X X' Y Y' : (D).Cauchy} (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 width stage X') (normBase hw0 hw1 width stage Y))
    (max (hX.modulus (pairDelta hw0 hw1 width stage X' Y epsilon))
      (hY.modulus (pairDelta hw0 hw1 width stage X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate hw0 hw1 width stage hX hY epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 width stage X Y n)
      (pairSequence hw0 hw1 width stage X' Y' n)) epsilon ∧
    leRat (sub (pairSequence hw0 hw1 width stage X' Y' n)
      (pairSequence hw0 hw1 width stage X Y n)) epsilon := by
  let B := pairCeiling hw0 hw1 width stage X' Y
  let hB := pairCeiling_nonnegative hw0 hw1 width stage X' Y
  let delta := pairDelta hw0 hw1 width stage X' Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase hw0 hw1 width stage X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase hw0 hw1 width stage Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 width stage (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
    B hB epsilon he (hX.close delta hd n hnX) (hY.close delta hd n hnY')
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width stage Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width stage X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y') :
    Equiv (representativeInner hw0 hw1 width stage X Y)
      (representativeInner hw0 hw1 width stage X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges hw0 hw1 width stage X Y)
    (pairSequence_converges hw0 hw1 width stage X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate hw0 hw1 width stage hX hY (HalfPow.half*epsilon), fun n hn => ?_⟩
  have h := pairSequence_close hw0 hw1 width stage hX hY (HalfPow.half*epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Same-carrier quotient descent; no representative is selected. -/
def completedInner : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner hw0 hw1 width stage X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef hw0 hw1 width stage hX hY))

theorem completedInner_mk (X Y : (D).Cauchy) :
    completedInner hw0 hw1 width stage
      (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner hw0 hw1 width stage X Y) := rfl

theorem representativeInner_constant (x y : PhysicalSpan width) :
    Equiv (representativeInner hw0 hw1 width stage ((D).constant x) ((D).constant y))
      (pairing hw0 hw1 width x.val y.val stage) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (pairing hw0 hw1 width x.val y.val stage))
    (pairSequence_converges hw0 hw1 width stage ((D).constant x) ((D).constant y))
    (convergesTo_const (pairing hw0 hw1 width x.val y.val stage))

theorem completedInner_embedSpan (x y : PhysicalSpan width) :
    completedInner hw0 hw1 width stage
      (embedSpan hw0 hw1 width stage x) (embedSpan hw0 hw1 width stage y) =
      Quotient.mk crealSetoid (pairing hw0 hw1 width x.val y.val stage) :=
  Quotient.sound (representativeInner_constant hw0 hw1 width stage x y)

theorem representativeInner_symm (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width stage X Y)
      (representativeInner hw0 hw1 width stage Y X) :=
  Equiv_of_limit_of_equal (fun n => pairing_symm hw0 hw1 width
      (X.seq n).val (Y.seq n).val (X.seq n).property (Y.seq n).property stage)
    (pairSequence_converges hw0 hw1 width stage X Y)
    (pairSequence_converges hw0 hw1 width stage Y X)

theorem completedInner_symm (x y : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x y = completedInner hw0 hw1 width stage y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm hw0 hw1 width stage X Y)

theorem representativeInner_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner hw0 hw1 width stage X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges hw0 hw1 width stage X X)
    (fun n => pairing_self_nonnegative hw0 hw1 width (X.seq n).val (X.seq n).property stage)

theorem completedInner_nonnegative (x : Completion hw0 hw1 width stage) :
    RCnonneg (completedInner hw0 hw1 width stage x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative hw0 hw1 width stage

theorem completedUnit_norm_one :
    completedInner hw0 hw1 width stage (completedUnit hw0 hw1 width stage)
      (completedUnit hw0 hw1 width stage) = Quotient.mk crealSetoid cone := by
  unfold completedUnit
  rw [completedInner_embedSpan]
  exact Quotient.sound (pairing_unit_unit hw0 hw1 width stage)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.pairSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.representativeInner_welldef
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedInner_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.representativeInner_constant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedInner_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.representativeInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.representativeInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner.completedUnit_norm_one
