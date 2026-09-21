/-
# Real-scalar Cauchy streams on the actual joint completion

For a constructive real with supplied rational Cauchy data and a supplied
representative of the existing fixed-width joint completion, this file proves
that pointwise rational scaling is Cauchy in the SAME joint seminorm.  Every
rate is explicit and representative-indexed.  No legacy completion is
identified with `JointCompletion`, and no completed real action, completeness,
spectral, scaling, or continuum claim is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear (jointDistSq_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
  (normBase normCeiling normCeiling_nonnegative diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling
    coefficientTolerance coefficientTolerance_pos coefficientTolerance_budget)
open YMGap.Continuum.RingNormaliser

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

private theorem sub_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add hab (neg_congr hcd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "P" => jointPairing hw0 hw1 width
local notation "d" => jointDistSq hw0 hw1 width

private theorem scalar_difference_pairing (a b : Q') (x y : PhysicalSpan width) :
    Equiv (P (differenceSpan (smulSpan a x) (smulSpan b x)) y)
      (mul (ofQ' (a + -b)) (P x y)) := by
  have h := jointPairing_difference_left hw0 hw1 width
    (smulSpan a x) (smulSpan b x) y
  have hscaled := sub_congr
    (jointPairing_smul_left hw0 hw1 width a x y)
    (jointPairing_smul_left hw0 hw1 width b x y)
  exact h.trans (hscaled.trans (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (by decide) (fun | 0 => a | 1 => b | _ => (P x y).approx n))))

/-- Exact coefficient-square factor for changing only a rational scalar on
one dense vector of the actual joint carrier. -/
theorem jointDistSq_scalar_difference (a b : Q') (x : PhysicalSpan width) :
    Equiv (d (smulSpan a x) (smulSpan b x))
      (mul (ofQ' ((a + -b)*(a + -b))) (P x x)) := by
  let v := differenceSpan (smulSpan a x) (smulSpan b x)
  change Equiv (P v v) (mul (ofQ' ((a + -b)*(a + -b))) (P x x))
  have hleft := scalar_difference_pairing hw0 hw1 width a b x v
  have hright := (jointPairing_symm hw0 hw1 width x v).trans
    (scalar_difference_pairing hw0 hw1 width a b x x)
  exact hleft.trans ((TrigSignedAdd.mul_congr_right hright).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_symm (Q'.mul_assoc_eqv (a + -b) (a + -b) ((P x x).approx n)))))

/-- The common explicit coefficient tolerance controls a scalar change at a
dense vector with a supplied actual-joint diagonal ceiling. -/
theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B)
    (he : (0 : Q') < epsilon) (x : PhysicalSpan width)
    (hnorm : leEv (P x x) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧
      b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (d (smulSpan a x) (smulSpan b x)) (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hdelta := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta :=
    Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hsquare := square_le_of_abs_le hdelta habs
  have hfactor : leEv czero (ofQ' ((a + -b)*(a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  exact leEv_trans (leEv_of_equiv (jointDistSq_scalar_difference hw0 hw1 width a b x))
    (leEv_trans (leEv_mul_nonneg_left hfactor hnorm)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare hB)
        (coefficientTolerance_budget B hB he))))

/-- Both the vector modulus and rational-scalar modulus remain executable
data attached to the supplied representatives. -/
def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : Nat :=
  max (max (cs.M 1) (normBase hw0 hw1 width X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (normCeiling hw0 hw1 width X)
        (normCeiling_nonnegative hw0 hw1 width X) epsilon)))

/-- Pointwise rational scaling of the supplied joint representative is Cauchy
with the displayed rate. -/
theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate hw0 hw1 width s cs X epsilon ≤ m)
    (hn : realScalarRate hw0 hw1 width s cs X epsilon ≤ n) :
    leEv (d (smulSpan (s.approx m) (X.seq m)) (smulSpan (s.approx n) (X.seq n)))
      (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := normCeiling hw0 hw1 width X
  let hB := normCeiling_nonnegative hw0 hw1 width X
  let delta := scalarTolerance A (quarter epsilon)
  have hdlt : (0 : Q') < delta := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : normBase hw0 hw1 width X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare : s.approx m * s.approx m ≤ A*A :=
    square_le_of_abs_le (scalarCeiling_nonnegative s cs)
      (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv
      (d (smulSpan (s.approx m) (X.seq m)) (smulSpan (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    have hscaled := leEv_mul_nonneg_left hfactor (X.isCauchy delta hdlt m n hXm hXn)
    exact leEv_trans
      (leEv_of_equiv (jointDistSq_smul hw0 hw1 width (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hdlt))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond : leEv
      (d (smulSpan (s.approx m) (X.seq n)) (smulSpan (s.approx n) (X.seq n)))
      (ofQ' (quarter epsilon)) :=
    scalar_change_bound hw0 hw1 width (s.approx m) (s.approx n) B epsilon hB he
      (X.seq n) (diagonal_le_normCeiling hw0 hw1 width X n hnormn)
      (cs.bound _ (coefficientTolerance_pos B hB he) m n hsm hsn)
  have hsum := leEv_add (leEv_add hfirst hfirst) (leEv_add hsecond hsecond)
  rw [ofQ'_add, ofQ'_add] at hsum
  have hbudget : Q'.eqv
      ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*epsilon))
        (ExpNeg.two_halves (HalfPow.half*epsilon)))
      (ExpNeg.two_halves epsilon)
  exact leEv_trans
    (jointDistSq_triangle hw0 hw1 width
      (smulSpan (s.approx m) (X.seq m)) (smulSpan (s.approx m) (X.seq n))
      (smulSpan (s.approx n) (X.seq n)))
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

/-- The actual joint-seminorm Cauchy stream underlying the future completed
real-scalar action. -/
def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := smulSpan (s.approx n) (X.seq n)
  modulus := realScalarRate hw0 hw1 width s cs X
  isCauchy := realScalar_bound hw0 hw1 width s cs X

theorem realScalarCauchy_seq (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (n : Nat) :
    (realScalarCauchy hw0 hw1 width s cs X).seq n = smulSpan (s.approx n) (X.seq n) := rfl

theorem realScalarCauchy_modulus (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') :
    (realScalarCauchy hw0 hw1 width s cs X).modulus epsilon =
      realScalarRate hw0 hw1 width s cs X epsilon := rfl

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.jointDistSq_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.scalar_change_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.realScalarCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.realScalarCauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy.realScalarCauchy_modulus
