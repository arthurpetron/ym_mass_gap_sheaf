/-
# Positive definiteness and separation on the actual joint completion

The actual joint pairing rate bounds each late representative term against
its constructed limit.  A zero completed diagonal therefore supplies an
explicit closeness witness to the embedded zero, proving positive
definiteness without selecting a quotient representative.

The rational subtraction constructed on this same `JointCompletion` then
gives pairing subtraction and extensionality.  No stage-indexed completion is
identified with this carrier, and no completeness or analytic hypothesis is
added.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan distSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
  (normBase normCeiling diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width

private theorem convergesTo_max {s : Nat → CReal} {L : CReal}
    (h : ConvergesTo s L) (base : Nat) : ConvergesTo (fun n => s (max n base)) L := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩

/-- The actual named joint-pairing rate bounds late terms against their
constructed scalar limit. -/
theorem pairSequence_limit_close (X Y : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : pairRate hw0 hw1 width X Y epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 width X Y n)
      (representativeInner hw0 hw1 width X Y)) epsilon ∧
    leRat (sub (representativeInner hw0 hw1 width X Y)
      (pairSequence hw0 hw1 width X Y n)) epsilon :=
  BF4ExactSlabFixedSpatialCompletedPosdef.late_limit_bound
    (pairSequence_converges hw0 hw1 width X Y)
    (pairSequence_bound hw0 hw1 width X Y) epsilon he n hn

/-- The supplied Cauchy representative carries its own computed diagonal
ceiling; no uniform bound or representative choice is added. -/
theorem representativeInner_le_normCeiling (X : (D).Cauchy) :
    leEv (representativeInner hw0 hw1 width X X)
      (ofQ' (normCeiling hw0 hw1 width X)) :=
  leEv_of_convergesTo_le
    (convergesTo_max (pairSequence_converges hw0 hw1 width X X)
      (normBase hw0 hw1 width X))
    (convergesTo_const (ofQ' (normCeiling hw0 hw1 width X)))
    (fun n => by
      simpa only [pairSequence] using diagonal_le_normCeiling hw0 hw1 width X
        (max n (normBase hw0 hw1 width X)) (Nat.le_max_right _ _))

/-- Distance to the literal zero presentation is the actual joint diagonal. -/
theorem jointDistSq_zero (x : PhysicalSpan width) :
    Equiv (jointDistSq hw0 hw1 width x (zero width))
      (jointPairing hw0 hw1 width x x) :=
  Equiv_of_limit_of_equal
    (fun stage => BF4ExactSlabFixedSpatialCompletedPosdef.distSq_zero
      hw0 hw1 width stage x)
    (distSq_converges_joint hw0 hw1 width x (zero width))
    (BF4ExactSlabFixedSpatialChartJointLimits.pairing_converges_jointPairing
      hw0 hw1 width x x)

/-- Zero completed norm constructs closeness with the existing actual
`pairRate`; no quotient representative is selected. -/
def closeZeroOfInnerZero (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 width X X) czero) :
    (D).Close X ((D).constant (zero width)) where
  modulus := pairRate hw0 hw1 width X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close hw0 hw1 width X X epsilon he n hn).1
    have hsub : Equiv
        (sub (pairSequence hw0 hw1 width X X n)
          (representativeInner hw0 hw1 width X X))
        (pairSequence hw0 hw1 width X X n) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (QPoly.q_add_zero_eqv ((pairSequence hw0 hw1 width X X n).approx k))))
    exact leEv_trans (leEv_of_equiv (jointDistSq_zero hw0 hw1 width (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem completedZero_inner_zero : B Z Z = RCzero :=
  completedInner_zero_left hw0 hw1 width Z

/-- Positive definiteness of the existing actual joint pairing. -/
theorem completedInner_posdef (x : V) : B x x = RCzero ↔ x = Z := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero hw0 hw1 width X (Quotient.exact h)⟩
  · intro h
    rw [h]
    exact completedZero_inner_zero hw0 hw1 width

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A'.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A'.approx n)))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A' => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A'.approx n)))

theorem completedInner_sub_left (x y z : V) :
    B (completedSub hw0 hw1 width x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 width y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 width x, completedInner_sub_left,
    completedInner_symm hw0 hw1 width y x, completedInner_symm hw0 hw1 width z x]

theorem completedAdd_zero (x : V) : A x Z = x := by
  rw [completedAdd_comm, completedZero_add]

theorem completedSub_add_cancel (x y : V) :
    A (completedSub hw0 hw1 width x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

theorem completedSub_self (x : V) : completedSub hw0 hw1 width x x = Z := by
  unfold completedSub
  rw [completedAdd_comm, completedNeg_add]

theorem completedSub_norm_zero_iff (x y : V) :
    B (completedSub hw0 hw1 width x y) (completedSub hw0 hw1 width x y) = RCzero ↔ x = y := by
  constructor
  · intro h
    have hz := (completedInner_posdef hw0 hw1 width (completedSub hw0 hw1 width x y)).mp h
    have hxy := congrArg (fun t => A t y) hz
    change A (completedSub hw0 hw1 width x y) y = A Z y at hxy
    rw [completedSub_add_cancel, completedZero_add] at hxy
    exact hxy
  · intro h
    rw [h, completedSub_self, completedZero_inner_zero]

/-- Separation by every pairing test on the same actual joint carrier. -/
theorem completed_eq_of_pairings (x y : V) (h : ∀ z, B x z = B y z) : x = y := by
  apply (completedSub_norm_zero_iff hw0 hw1 width x y).mp
  rw [completedInner_sub_left, h, rc_sub_self]

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.pairSequence_limit_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.representativeInner_le_normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.jointDistSq_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.closeZeroOfInnerZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedZero_inner_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedInner_posdef
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedInner_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedInner_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedAdd_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedSub_add_cancel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedSub_self
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completedSub_norm_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry.completed_eq_of_pairings
