/-
# Completed time on the literal-width all-nome Wilson carrier

The actual intrinsic advance is nonexpansive for the all-nome seminorm, so
the existing completion machinery descends it to a semigroup on the SAME
completed carrier.  Time balance, one-step positivity, the fixed unit, and
the literal loop-lag pin are inherited from the corresponding dense form.

No strict contraction, spectral gap, carrier transport, or changing-spacing
claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedInner
import YMGap.Continuum.BF4WilsonAllNomeTimeContraction
import YMGap.Continuum.BF4WilsonAllNomeTimeForm

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within unit chart_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance advance_zero advance_add chart_advance_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_chart intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
  (intrinsicForm_difference_diagonal)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm
  (distSq distSq_refl seminorm)
open YMGap.Continuum.BF4WilsonAllNomeTimeContraction
  (distSq_advance_contraction intrinsicForm_advance_contraction)
open YMGap.Continuum.BF4WilsonAllNomeTimeForm
  (intrinsicForm_time_sum intrinsicForm_oneStep_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width

/-- Dense physical time is nonexpansive for the actual all-nome distance. -/
def timeNonexpansive (n : Nat) : (D).Nonexpansive where
  toFun := advance n
  contraction := distSq_advance_contraction hw0 hw1 n

def timeSemigroup : (D).NonexpansiveSemigroup where
  op := timeNonexpansive hw0 hw1
  zero_law := by
    intro x
    change Equiv (distSq hw0 hw1 (advance 0 x) x) czero
    rw [advance_zero]
    exact distSq_refl hw0 hw1 x
  add_law := by
    intro m n x
    change Equiv (distSq hw0 hw1 (advance (m+n) x)
      (advance m (advance n x))) czero
    rw [advance_add]
    exact distSq_refl hw0 hw1 _

/-- Endomorphism of the already constructed all-nome completion. -/
def completedTime (n : Nat) : V -> V :=
  (timeNonexpansive hw0 hw1 n).completionMap

local notation "T" => completedTime hw0 hw1
local notation "A" n => timeNonexpansive hw0 hw1 n

theorem completedTime_zero (x : V) : T 0 x = x :=
  (timeSemigroup hw0 hw1).completionMap_zero x

theorem completedTime_add (m n : Nat) (x : V) :
    T (m+n) x = T m (T n x) :=
  (timeSemigroup hw0 hw1).completionMap_add m n x

theorem completedTime_embed (n : Nat) (x : IntrinsicExpression width) :
    T n (embed hw0 hw1 x) = embed hw0 hw1 (advance n x) := rfl

theorem time_cauchy_seq (n : Nat) (X : (D).Cauchy) (k : Nat) :
    ((A n).mapCauchy X).seq k = advance n (X.seq k) := rfl

/-- Completion time retains the supplied Cauchy modulus verbatim. -/
theorem time_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((A n).mapCauchy X).modulus = X.modulus := rfl

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

private theorem sub_self_eqv_zero (a : CReal) : Equiv (sub a a) czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (a.approx n))

/-- Equality of literal unit charts removes the changed radius tag. -/
private theorem intrinsicForm_advanced_unit_right (n : Nat)
    (x : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 x (advance n (unit width)))
      (intrinsicForm hw0 hw1 x (unit width)) := by
  let H := x.radius+n
  have hx : x.radius <= H := by omega
  have hun : (advance n (unit width)).radius <= H := by
    change 0+n <= H
    omega
  have hu : (unit width).radius <= H := Nat.zero_le _
  have hl := intrinsicForm_chart hw0 hw1 x (advance n (unit width)) H hx hun
  have hr := intrinsicForm_chart hw0 hw1 x (unit width) H hx hu
  exact hl.trans (by simpa only [chart_advance_unit, chart_unit] using hr.symm)

private theorem intrinsicForm_advanced_unit_left (n : Nat)
    (x : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (advance n (unit width)) x)
      (intrinsicForm hw0 hw1 (unit width) x) :=
  (intrinsicForm_symm hw0 hw1 (advance n (unit width)) x).trans
    ((intrinsicForm_advanced_unit_right hw0 hw1 n x).trans
      (intrinsicForm_symm hw0 hw1 x (unit width)))

private theorem advance_unit_null (n : Nat) :
    (D).Null (advance n (unit width)) (unit width) := by
  change Equiv (distSq hw0 hw1 (advance n (unit width)) (unit width)) czero
  have haa := (intrinsicForm_advanced_unit_left hw0 hw1 n
      (advance n (unit width))).trans
    (intrinsicForm_advanced_unit_right hw0 hw1 n (unit width))
  have hau := intrinsicForm_advanced_unit_left hw0 hw1 n (unit width)
  have hua := intrinsicForm_advanced_unit_right hw0 hw1 n (unit width)
  exact (intrinsicForm_difference_diagonal hw0 hw1
    (advance n (unit width)) (unit width)).trans
      ((sub_congr (sub_congr haa hau) (sub_congr hua (Equiv.refl _))).trans
        (sub_self_eqv_zero _))

/-- The embedded constant state is fixed in the same completion. -/
theorem completedUnit_fixed (n : Nat) : T n U = U := by
  unfold unitState
  rw [completedTime_embed]
  exact (D).embedRep_eq_of_null (advance_unit_null hw0 hw1 n)

local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

/-- Physical time and Cauchy approximation remain independent indices. -/
theorem representativeInner_time_sum (m n : Nat) (X Y : (D).Cauchy) :
    Equiv (R ((A m).mapCauchy X) ((A n).mapCauchy Y))
      (R X ((A (m+n)).mapCauchy Y)) := by
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD
    ((A m).mapCauchy X) ((A n).mapCauchy Y)
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD
    X ((A (m+n)).mapCauchy Y)
  apply Equiv_of_limit_of_equal (hA := hleft) (hB := hright)
  intro k
  exact intrinsicForm_time_sum hw0 hw1 m n (X.seq k) (Y.seq k)

theorem completedInner_time_sum (m n : Nat) (x y : V) :
    B (T m x) (T n y) = B x (T (m+n) y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (representativeInner_time_sum hw0 hw1 m n X Y)

theorem completedInner_time_balance (n : Nat) (x y : V) :
    B (T n x) y = B x (T n y) := by
  simpa only [completedTime_zero, Nat.add_zero] using
    completedInner_time_sum hw0 hw1 n 0 x y

/-- Orthogonality to the actual embedded constant, on this SAME carrier.
This definition does not assert that a nonzero centered state survives scaling. -/
def VacuumComplement := {x : V // B U x = RCzero}

theorem completedTime_preserves_vacuumComplement (n : Nat) (x : V)
    (hx : B U x = RCzero) : B U (T n x) = RCzero := by
  rw [← completedInner_time_balance, completedUnit_fixed]
  exact hx

def vacuumComplementTime (n : Nat) (x : VacuumComplement hw0 hw1 (width := width)) :
    VacuumComplement hw0 hw1 (width := width) :=
  ⟨T n x.val, completedTime_preserves_vacuumComplement hw0 hw1 n x.val x.property⟩

theorem representativeInner_time_contraction (n : Nat) (X : (D).Cauchy) :
    leEv (R ((A n).mapCauchy X) ((A n).mapCauchy X)) (R X X) := by
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD
    ((A n).mapCauchy X) ((A n).mapCauchy X)
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD X X
  apply leEv_of_convergesTo_le hleft hright
  intro k
  exact intrinsicForm_advance_contraction hw0 hw1 n (X.seq k)

theorem completedInner_time_contraction (n : Nat) (x : V) :
    RCle (B (T n x) (T n x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_time_contraction hw0 hw1 n X

theorem representativeInner_oneStep_nonnegative (X : (D).Cauchy) :
    leEv (ofQ' 0) (R X ((A 1).mapCauchy X)) := by
  apply leEv_of_convergesTo_le (convergesTo_const (ofQ' 0))
    (CRealSeminormPairingCompletion.pairSequence_converges PD X ((A 1).mapCauchy X))
  intro k
  exact intrinsicForm_oneStep_nonnegative hw0 hw1 (X.seq k)

/-- Positive one-step quadratic form on every completed vector. -/
theorem completedInner_oneStep_nonnegative (x : V) :
    RCnonneg (B x (T 1 x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_oneStep_nonnegative hw0 hw1 X

/-- The completed operator retains the exact original loop time-lag moment. -/
theorem completedTime_loop_lag {width : Nat} (loop : SourceLoop width) (n : Nat) :
    completedInner hw0 hw1 (embed hw0 hw1 (loopState loop))
      (completedTime hw0 hw1 n (embed hw0 hw1 (loopState loop))) =
        Quotient.mk crealSetoid (lagMoment hw0 hw1 loop n) := by
  rw [completedTime_embed, completedInner_embed]
  exact Quotient.sound (pairing_lag hw0 hw1 loop n)

/-- The original geometric loss bound is now an actual completed-operator
matrix coefficient. It remains absolute, not relative to centered variance. -/
theorem completed_dyadic_loss_bound (scale width : Nat)
    (hwidth : BF4DyadicWilsonSquare.side scale < width) :
    let x := embed hw0 hw1 (loopState (BF4DyadicWilsonSquare.paddedSquare scale width hwidth))
    RCle (RCmul (Quotient.mk crealSetoid (ofQ' 2))
      (RCsub (completedInner hw0 hw1 x x)
        (completedInner hw0 hw1 x (completedTime hw0 hw1 (BF4DyadicWilsonSquare.side scale) x))))
      (Quotient.mk crealSetoid (ofQ' ((384 : Q') *
        (Q'.ofNat (BF4DyadicWilsonSquare.side scale) *
          (Q'.ofNat (BF4DyadicWilsonSquare.side scale) *
            Q'.ofNat (BF4DyadicWilsonSquare.side scale))) * (1 + -w)))) := by
  dsimp only
  rw [completedTime_embed, completedInner_embed, completedInner_embed]
  exact BF4WilsonAllNomeLoopTimePin.dyadic_reflected_loss_bound hw0 hw1 scale width hwidth

#print axioms timeNonexpansive
#print axioms timeSemigroup
#print axioms completedTime_zero
#print axioms completedTime_add
#print axioms completedTime_embed
#print axioms time_cauchy_modulus
#print axioms completedUnit_fixed
#print axioms representativeInner_time_sum
#print axioms completedInner_time_sum
#print axioms completedInner_time_balance
#print axioms completedTime_preserves_vacuumComplement
#print axioms vacuumComplementTime
#print axioms completedInner_time_contraction
#print axioms completedInner_oneStep_nonnegative
#print axioms completedTime_loop_lag
#print axioms completed_dyadic_loss_bound

end YMGap.Continuum.BF4WilsonAllNomeCompletedTime
