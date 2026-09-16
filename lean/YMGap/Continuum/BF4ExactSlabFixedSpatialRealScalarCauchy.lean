/-
# Computed real-scalar Cauchy streams for the original reflected form

The nth presentation is literally `s.approx n` times the nth original
physical presentation. Its squared-distance estimate uses the actual dense
scalar laws and the computed eventual diagonal ceiling of the SAME form.
Only the generic rational tolerance and scalar-ceiling arithmetic is reused
from the earlier plaquette module; no plaquette carrier or form is substituted.

The real's rational Cauchy modulus is explicit Type-level input. The output
retains an executable modulus and never extracts one from `CReal.cauchy`.
This supplies a representative for completed real scaling at fixed nome,
width and cutoff stage. Quotient descent is a subsequent consumer; no new
analytic hypothesis, physical gap or continuum assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling
    coefficientTolerance coefficientTolerance_pos coefficientTolerance_budget)

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

/-- Scalar subtraction holds in the actual pairing relation, not as list equality. -/
theorem scalar_difference_pairingEq (a b : Q') (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage
      (addSpan (smulSpan a x) (smulSpan (-1) (smulSpan b x)))
      (smulSpan (a + -b) x) := by
  have hb : Q'.eqv ((-1)*b) (-b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 b)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv b))
  have hnegative : PairingEq hw0 hw1 width stage
      (smulSpan (-1) (smulSpan b x)) (smulSpan (-b) x) :=
    pairingEq_trans hw0 hw1 width stage
      (pairingEq_symm hw0 hw1 width stage (smulSpan_mul hw0 hw1 width stage (-1) b x))
      (smulSpan_congr hw0 hw1 width stage hb x)
  have hsum : PairingEq hw0 hw1 width stage
      (addSpan (smulSpan a x) (smulSpan (-1) (smulSpan b x)))
      (addSpan (smulSpan a x) (smulSpan (-b) x)) :=
    pairingEq_add hw0 hw1 width stage
      (pairingEq_refl hw0 hw1 width stage (smulSpan a x)) hnegative
  exact pairingEq_trans hw0 hw1 width stage hsum
    (pairingEq_symm hw0 hw1 width stage (add_smulSpan hw0 hw1 width stage a (-b) x))

/-- Changing only the scalar costs its exact squared rational difference. -/
theorem distSq_scalar_difference (a b : Q') (x : PhysicalSpan width) :
    Equiv (distSq hw0 hw1 width stage (smulSpan a x) (smulSpan b x))
      (mul (ofQ' ((a + -b)*(a + -b))) (pairing hw0 hw1 width x.val x.val stage)) := by
  let d : PhysicalSpan width := addSpan (smulSpan a x) (smulSpan (-1) (smulSpan b x))
  let e : PhysicalSpan width := smulSpan (a + -b) x
  have hEq : PairingEq hw0 hw1 width stage d e :=
    scalar_difference_pairingEq hw0 hw1 width stage a b x
  have hdiag : Equiv (pairing hw0 hw1 width d.val d.val stage)
      (pairing hw0 hw1 width e.val e.val stage) :=
    diagonal_congr hw0 hw1 width stage (x := d) (y := e) hEq
  have hscale : Equiv (pairing hw0 hw1 width e.val e.val stage)
      (mul (ofQ' ((a + -b)*(a + -b))) (pairing hw0 hw1 width x.val x.val stage)) :=
    diagonal_smul hw0 hw1 width stage (a + -b) x
  change Equiv (pairing hw0 hw1 width d.val d.val stage)
    (mul (ofQ' ((a + -b)*(a + -b))) (pairing hw0 hw1 width x.val x.val stage))
  exact Equiv.trans hdiag hscale

/-- The computed coefficient tolerance controls scalar variation on a bounded
actual reflected diagonal; no strict positivity of that diagonal is required. -/
theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B)
    (he : (0 : Q') < epsilon) (x : PhysicalSpan width)
    (hnorm : leEv (pairing hw0 hw1 width x.val x.val stage) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧
      b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (distSq hw0 hw1 width stage (smulSpan a x) (smulSpan b x))
      (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hd : (0 : Q') ≤ delta := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta :=
    Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hs : (a + -b)*(a + -b) ≤ delta*delta := square_le_of_abs_le hd habs
  have hfactor : leEv czero (ofQ' ((a + -b)*(a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  have hscaled : leEv
      (mul (ofQ' ((a + -b)*(a + -b))) (pairing hw0 hw1 width x.val x.val stage))
      (mul (ofQ' ((a + -b)*(a + -b))) (ofQ' B)) :=
    leEv_mul_nonneg_left hfactor hnorm
  exact leEv_trans (leEv_of_equiv (distSq_scalar_difference hw0 hw1 width stage a b x))
    (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hs hB)
        (coefficientTolerance_budget B hB he))))

/-- The maximum records both computed tail anchors and both supplied rates. -/
def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : Nat :=
  max (max (cs.M 1) (normBase hw0 hw1 width stage X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (normCeiling hw0 hw1 width stage X)
        (normCeiling_nonnegative hw0 hw1 width stage X) epsilon)))

/-- The actual scaled stream is Cauchy in the original reflected distance.
Each leg receives epsilon/4 before the sqrt-free triangle doubles it. -/
theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate hw0 hw1 width stage s cs X epsilon ≤ m)
    (hn : realScalarRate hw0 hw1 width stage s cs X epsilon ≤ n) :
    leEv (distSq hw0 hw1 width stage
      (smulSpan (s.approx m) (X.seq m)) (smulSpan (s.approx n) (X.seq n)))
      (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := normCeiling hw0 hw1 width stage X
  let hB := normCeiling_nonnegative hw0 hw1 width stage X
  let delta := scalarTolerance A (quarter epsilon)
  have hd : (0 : Q') < delta := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : normBase hw0 hw1 width stage X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare : s.approx m * s.approx m ≤ A*A :=
    square_le_of_abs_le (scalarCeiling_nonnegative s cs)
      (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv (distSq hw0 hw1 width stage
      (smulSpan (s.approx m) (X.seq m)) (smulSpan (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    have hscaled : leEv
        (mul (ofQ' (s.approx m * s.approx m)) (distSq hw0 hw1 width stage (X.seq m) (X.seq n)))
        (mul (ofQ' (s.approx m * s.approx m)) (ofQ' delta)) :=
      leEv_mul_nonneg_left hfactor (X.isCauchy delta hd m n hXm hXn)
    exact leEv_trans
      (leEv_of_equiv (distSq_smul hw0 hw1 width stage (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hd))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond : leEv (distSq hw0 hw1 width stage
      (smulSpan (s.approx m) (X.seq n)) (smulSpan (s.approx n) (X.seq n)))
      (ofQ' (quarter epsilon)) :=
    scalar_change_bound hw0 hw1 width stage (s.approx m) (s.approx n) B epsilon hB he (X.seq n)
      (diagonal_le_normCeiling hw0 hw1 width stage X n hnormn)
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
    (distSq_triangle hw0 hw1 width stage
      (smulSpan (s.approx m) (X.seq m))
      (smulSpan (s.approx m) (X.seq n))
      (smulSpan (s.approx n) (X.seq n)))
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

/-- Actual original presentations with their computed squared-distance modulus. -/
def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := smulSpan (s.approx n) (X.seq n)
  modulus := realScalarRate hw0 hw1 width stage s cs X
  isCauchy := realScalar_bound hw0 hw1 width stage s cs X

theorem realScalarCauchy_seq (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (n : Nat) :
    (realScalarCauchy hw0 hw1 width stage s cs X).seq n =
      smulSpan (s.approx n) (X.seq n) := rfl

theorem realScalarCauchy_modulus (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') :
    (realScalarCauchy hw0 hw1 width stage s cs X).modulus epsilon =
      realScalarRate hw0 hw1 width stage s cs X epsilon := rfl

end YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.scalar_difference_pairingEq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.distSq_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.scalar_change_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.realScalarCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.realScalarCauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy.realScalarCauchy_modulus
