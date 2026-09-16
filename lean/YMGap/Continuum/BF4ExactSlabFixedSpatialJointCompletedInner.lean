/-
# Actual cutoff-removed reflected pairing on its SAME Cauchy completion

Explicit closeness moduli control the difference of the constructed scalar
representatives. Quotient elimination therefore descends their limit to
the already defined JointCompletion, without selecting representatives
or identifying any fixed-cutoff carrier with it. The embedding pin retains
the actual jointPairing; symmetry, positivity and unit normalization pass
through the same scalar limits.

Completed linearity, positive definiteness, centering and the strict gap
extension are subsequent obligations. No metric-completeness theorem,
nonconstant excitation, continuum or physical Hamiltonian is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

/-- The changed first and original second representatives supply the two
computed ceilings; both given closeness moduli remain explicit. -/
def closeRate {X X' Y Y' : (D).Cauchy} (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 width X') (normBase hw0 hw1 width Y))
    (max (hX.modulus (pairDelta hw0 hw1 width X' Y epsilon))
      (hY.modulus (pairDelta hw0 hw1 width X' Y epsilon)))

theorem pairSequence_close {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y')
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : closeRate hw0 hw1 width hX hY epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 width X Y n)
      (pairSequence hw0 hw1 width X' Y' n)) epsilon ∧
    leRat (sub (pairSequence hw0 hw1 width X' Y' n)
      (pairSequence hw0 hw1 width X Y n)) epsilon := by
  let B := pairCeiling hw0 hw1 width X' Y
  let hB := pairCeiling_nonnegative hw0 hw1 width X' Y
  let delta := pairDelta hw0 hw1 width X' Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hnX' : normBase hw0 hw1 width X' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnY : normBase hw0 hw1 width Y ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnX : hX.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnY' : hY.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 width (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
    B hB epsilon he (hX.close delta hd n hnX) (hY.close delta hd n hnY')
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width Y n hnY) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width X' n hnX') (Q'.le_max'_left _ _))

theorem representativeInner_welldef {X X' Y Y' : (D).Cauchy}
    (hX : (D).Close X X') (hY : (D).Close Y Y') :
    Equiv (representativeInner hw0 hw1 width X Y)
      (representativeInner hw0 hw1 width X' Y') := by
  apply Equiv_of_limit_of_close (pairSequence_converges hw0 hw1 width X Y)
    (pairSequence_converges hw0 hw1 width X' Y')
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate hw0 hw1 width hX hY (HalfPow.half*epsilon), fun n hn => ?_⟩
  have h := pairSequence_close hw0 hw1 width hX hY (HalfPow.half*epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat h.1 h.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Quotient descent on the SAME actual joint-completion carrier. -/
def completedInner : JointCompletion hw0 hw1 width → JointCompletion hw0 hw1 width → RC :=
  Quotient.lift₂ (fun X Y => Quotient.mk crealSetoid (representativeInner hw0 hw1 width X Y))
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hX⟩
      rcases hY with ⟨hY⟩
      exact Quotient.sound (representativeInner_welldef hw0 hw1 width hX hY))

theorem completedInner_mk (X Y : (D).Cauchy) :
    completedInner hw0 hw1 width
      (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeInner hw0 hw1 width X Y) := rfl

theorem representativeInner_constant (x y : PhysicalSpan width) :
    Equiv (representativeInner hw0 hw1 width ((D).constant x) ((D).constant y))
      (jointPairing hw0 hw1 width x y) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl (jointPairing hw0 hw1 width x y))
    (pairSequence_converges hw0 hw1 width ((D).constant x) ((D).constant y))
    (convergesTo_const (jointPairing hw0 hw1 width x y))

/-- On every original physical presentation, the completed pairing is
exactly its proved cutoff/boundary-time joint scalar, not a new form. -/
theorem completedInner_embedSpan (x y : PhysicalSpan width) :
    completedInner hw0 hw1 width
      (jointEmbedSpan hw0 hw1 width x) (jointEmbedSpan hw0 hw1 width y) =
      Quotient.mk crealSetoid (jointPairing hw0 hw1 width x y) :=
  Quotient.sound (representativeInner_constant hw0 hw1 width x y)

theorem representativeInner_symm (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width X Y)
      (representativeInner hw0 hw1 width Y X) :=
  Equiv_of_limit_of_equal
    (fun n => jointPairing_symm hw0 hw1 width (X.seq n) (Y.seq n))
    (pairSequence_converges hw0 hw1 width X Y)
    (pairSequence_converges hw0 hw1 width Y X)

theorem completedInner_symm (x y : JointCompletion hw0 hw1 width) :
    completedInner hw0 hw1 width x y = completedInner hw0 hw1 width y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_symm hw0 hw1 width X Y)

theorem representativeInner_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner hw0 hw1 width X X) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges hw0 hw1 width X X)
    (fun n => jointPairing_nonnegative hw0 hw1 width (X.seq n))

theorem completedInner_nonnegative (x : JointCompletion hw0 hw1 width) :
    RCnonneg (completedInner hw0 hw1 width x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_nonnegative hw0 hw1 width

theorem completedUnit_norm_one :
    completedInner hw0 hw1 width (jointCompletedUnit hw0 hw1 width)
      (jointCompletedUnit hw0 hw1 width) = Quotient.mk crealSetoid cone := by
  unfold jointCompletedUnit
  rw [completedInner_embedSpan]
  exact Quotient.sound (jointPairing_unit_unit hw0 hw1 width)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.pairSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.representativeInner_welldef
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedInner_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.representativeInner_constant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedInner_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.representativeInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.representativeInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner.completedUnit_norm_one
