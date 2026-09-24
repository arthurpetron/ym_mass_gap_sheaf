/-
# Actual centered vectors on the SAME all-nome Wilson completion

The exact coefficient-square distance constructs a Cauchy stream of rational
centerings, using the actual mean's supplied modulus. Its class belongs to
the existing completion and is orthogonal to its actual unit. The previously
proved scalar centered time moments are its SAME-operator autocorrelations.

No real-linear completed operations, positive norm floor, changing-scale
survival or continuum construction is assumed or supplied by this file.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

namespace YMGap.Continuum.BF4WilsonAllNomeCenteredVector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra (centerApprox)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
  (centerTolerance centerTolerance_positive coefficient_square_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "F" => intrinsicForm hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => unit width
local notation "U" => unitState hw0 hw1 width
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

attribute [local irreducible] intrinsicForm

private theorem sub_congr {a b c d : CReal} (h : Equiv a b) (j : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add h (neg_congr j)

private def centerValue (a b c : CReal) (q r : Q') : CReal :=
  sub (sub a (mul (ofQ' q) b)) (sub (mul (ofQ' r) c) (ofQ' (q*r)))

private theorem centerValue_expand (a b c : CReal) (q r : Q') :
    Equiv (sub (sub a (mul (ofQ' r) c)) (mul (ofQ' q) (sub b (ofQ' r))))
      (centerValue a b c q r) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.var 4) (.var 2))))
        (.neg (.mul (.var 3) (.add (.var 1) (.neg (.var 4))))))
      (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
        (.neg (.add (.mul (.var 4) (.var 2)) (.neg (.mul (.var 3) (.var 4))))))
      (by decide) (fun
        | 0 => a.approx n
        | 1 => b.approx n
        | 2 => c.approx n
        | 3 => q
        | _ => r))

private theorem centered_pair (x y : IntrinsicExpression width) (q r : Q') :
    Equiv (F (centerApprox x q) (centerApprox y r))
      (centerValue (F x y) (F u y) (F x u) q r) := by
  have huy : Equiv (F u (centerApprox y r)) (sub (F u y) (ofQ' r)) :=
    (centerApprox_pairing_right hw0 hw1 u y r).trans
      (sub_congr (Equiv.refl _)
        ((Pivot2.mul_congr_right (intrinsicForm_unit_unit hw0 hw1)).trans
          (CRealAlg.cmul_cone (ofQ' r))))
  exact (centerApprox_pairing_left hw0 hw1 x (centerApprox y r) q).trans
    ((sub_congr (centerApprox_pairing_right hw0 hw1 x y r)
      (Pivot2.mul_congr_right huy)).trans
      (centerValue_expand (F x y) (F u y) (F x u) q r))

private theorem centerValue_distance (a b c : CReal) (q r : Q') :
    Equiv
      (sub (sub (centerValue a b c q q) (centerValue a b c q r))
        (sub (centerValue a b c r q) (centerValue a b c r r)))
      (ofQ' ((q + -r)^2)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  let P (i j : Nat) : RingNormaliser.PolyExpr :=
    .add (.add (.var 2) (.neg (.mul (.var i) (.var 3))))
      (.neg (.add (.mul (.var j) (.var 4)) (.neg (.mul (.var i) (.var j)))))
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (P 0 0) (.neg (P 0 1))) (.neg (.add (P 1 0) (.neg (P 1 1)))))
    (.mul (.add (.var 0) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.const 1)))
    (by decide) (fun
      | 0 => q
      | 1 => r
      | 2 => a.approx n
      | 3 => b.approx n
      | _ => c.approx n)

/-- This exact distance supplies the centering modulus, not a new norm bound. -/
theorem centerApprox_distance (x : IntrinsicExpression width) (q r : Q') :
    Equiv (distSq hw0 hw1 (centerApprox x q) (centerApprox x r))
      (ofQ' ((q + -r)^2)) :=
  (intrinsicForm_difference_diagonal hw0 hw1 (centerApprox x q) (centerApprox x r)).trans
    ((sub_congr
      (sub_congr (centered_pair hw0 hw1 x x q q) (centered_pair hw0 hw1 x x q r))
      (sub_congr (centered_pair hw0 hw1 x x r q) (centered_pair hw0 hw1 x x r r))).trans
      (centerValue_distance (F x x) (F u x) (F x u) q r))

/-- Original scalar approximation data, clipped for the squared metric. -/
def centeredRate (x : IntrinsicExpression width) (epsilon : Q') : Nat :=
  (intrinsicFormCauchy hw0 hw1 x u).M (centerTolerance epsilon)

def centeredStream (x : IntrinsicExpression width) : (D).Cauchy where
  seq n := centerApprox x ((F x u).approx n)
  modulus := centeredRate hw0 hw1 x
  isCauchy := by
    intro epsilon he m n hm hn
    have h := (intrinsicFormCauchy hw0 hw1 x u).bound
      (centerTolerance epsilon) (centerTolerance_positive he) m n hm hn
    exact leEv_trans (leEv_of_equiv (centerApprox_distance hw0 hw1 x _ _))
      (leEv_of_le (ofQ'_le_ofQ' (coefficient_square_bound he h)))

/-- A constructed vector, not a selected representative of an arbitrary class. -/
def centeredVector (x : IntrinsicExpression width) : Completion hw0 hw1 width :=
  Quotient.mk (D).completionSetoid (centeredStream hw0 hw1 x)

local notation "C" => centeredStream hw0 hw1
local notation "v" => centeredVector hw0 hw1

theorem centeredStream_modulus (x : IntrinsicExpression width) :
    (C x).modulus = centeredRate hw0 hw1 x := rfl

theorem centered_unit_representative (x : IntrinsicExpression width) :
    Equiv (R (C x) ((D).constant u)) czero := by
  have hc := TrigAddCReal.convergesTo_add (convergesTo_const (F x u))
    (TrigAddCReal.convergesTo_neg (mean_approximations_converge hw0 hw1 x))
  exact (Equiv_of_limit_of_equal
    (fun k => centerApprox_unit hw0 hw1 x ((F x u).approx k))
    (CRealSeminormPairingCompletion.pairSequence_converges PD (C x) ((D).constant u))
    hc).trans (sub_self_eqv_zero _)

theorem centeredVector_orthogonal (x : IntrinsicExpression width) :
    B (v x) U = RCzero :=
  Quotient.sound (centered_unit_representative hw0 hw1 x)

/-- The actual existing vacuum-complement subtype receives this explicit vector. -/
def centeredExcitation (x : IntrinsicExpression width) :
    VacuumComplement hw0 hw1 (width := width) :=
  ⟨v x, (completedInner_symm hw0 hw1 U (v x)).trans
    (centeredVector_orthogonal hw0 hw1 x)⟩

/-- The already proved scalar centering limit is the actual autocorrelation
of the constructed vector under the existing completed time map. -/
theorem centeredVector_time_pairing (n : Nat) (x : IntrinsicExpression width) :
    B (v x) (T n (v x)) = Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 n x x) := by
  apply Quotient.sound
  exact Equiv_of_limit_of_equal (fun _ => Equiv.refl _)
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      (C x) ((timeNonexpansive hw0 hw1 n).mapCauchy (C x)))
    (centeredApprox_time_converges hw0 hw1 n x)

theorem centeredVector_diagonal (x : IntrinsicExpression width) :
    B (v x) (v x) = Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 0 x x) := by
  have h := centeredVector_time_pairing hw0 hw1 0 x
  rw [completedTime_zero] at h
  exact h

/-- Centering cancels from time loss on the actual completion, for every
intrinsic expression. This is an identity, not a relative loss estimate. -/
theorem centeredVector_loss_pin (n : Nat) (x : IntrinsicExpression width) :
    RCsub (B (v x) (v x)) (B (v x) (T n (v x))) =
      RCsub (Quotient.mk crealSetoid (F x x))
        (Quotient.mk crealSetoid (F x (advance n x))) := by
  rw [centeredVector_diagonal, centeredVector_time_pairing]
  apply Quotient.sound
  unfold centeredTimeMoment
  rw [advance_zero]
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => (F x x).approx k
           | 1 => (F x (advance n x)).approx k
           | _ => (mul (F x u) (F u x)).approx k))

/-- The changing geometric family now has an actual CENTERED-vector loss
consumer. The cubic bound is unchanged and gives no centered norm floor. -/
theorem centered_dyadic_loss_bound (scale width : Nat)
    (hwidth : BF4DyadicWilsonSquare.side scale < width) :
    let x := BF4WilsonAllNomeLoopTimePin.loopState
      (BF4DyadicWilsonSquare.paddedSquare scale width hwidth)
    RCle (RCmul (Quotient.mk crealSetoid (ofQ' 2))
      (RCsub (B (v x) (v x))
        (B (v x) (T (BF4DyadicWilsonSquare.side scale) (v x)))))
      (Quotient.mk crealSetoid (ofQ' ((384 : Q') *
        (Q'.ofNat (BF4DyadicWilsonSquare.side scale) *
          (Q'.ofNat (BF4DyadicWilsonSquare.side scale) *
            Q'.ofNat (BF4DyadicWilsonSquare.side scale))) * (1 + -w)))) := by
  dsimp only
  rw [centeredVector_loss_pin]
  exact BF4WilsonAllNomeLoopTimePin.dyadic_reflected_loss_bound hw0 hw1 scale width hwidth

#print axioms centerApprox_distance
#print axioms centeredRate
#print axioms centeredStream
#print axioms centeredVector
#print axioms centeredStream_modulus
#print axioms centered_unit_representative
#print axioms centeredVector_orthogonal
#print axioms centeredExcitation
#print axioms centeredVector_time_pairing
#print axioms centeredVector_diagonal
#print axioms centeredVector_loss_pin
#print axioms centered_dyadic_loss_bound

end YMGap.Continuum.BF4WilsonAllNomeCenteredVector
