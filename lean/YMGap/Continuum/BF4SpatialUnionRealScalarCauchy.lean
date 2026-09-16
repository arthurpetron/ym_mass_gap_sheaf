/-
# Real scalar streams on the SAME spatial union

Scale the nth original presentation by the nth supplied rational scalar
approximation. Two elementary estimates control the changing vector and the
changing scalar separately. The already computed pairing ceiling and the
explicit scalar QCauchy rate give a modulus for this actual stream.

This direct construction needs no extra outer completion or selected scalar
representative. It supplies the real-scalar quotient action and normalization
consumer, not arbitrary quotient-real moduli or full Hilbert/QFT completeness.
-/

import YMGap.Continuum.BF4SpatialUnionScalarDistance
import YMGap.Continuum.CRealSeminormPairingCompletionBounds

namespace YMGap.Continuum.BF4SpatialUnionRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (pairingData)
open YMGap.Continuum.BF4SpatialUnionLinear (distSq_smul)
open YMGap.Continuum.BF4SpatialUnionScalarDistance (scalar_change_bound)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normBase normCeiling normCeiling_nonnegative diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling
    coefficientTolerance coefficientTolerance_pos)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "d" => distSq hw0 hw1 hsmall hd hs

/-- Both tail anchors and both approximation rates remain executable data. -/
def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : Nat :=
  max (max (cs.M 1) (normBase PD X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (normCeiling PD X)
        (normCeiling_nonnegative PD X) epsilon)))

/-- Each difference leg costs epsilon/4 before the squared-distance triangle. -/
theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate hw0 hw1 hsmall hd hs s cs X epsilon ≤ m)
    (hn : realScalarRate hw0 hw1 hsmall hd hs s cs X epsilon ≤ n) :
    leEv (d (smulStage (s.approx m) (X.seq m)) (smulStage (s.approx n) (X.seq n)))
      (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := normCeiling PD X
  let hB := normCeiling_nonnegative PD X
  let delta := scalarTolerance A (quarter epsilon)
  have hdlt : (0 : Q') < delta := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : normBase PD X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare : s.approx m * s.approx m ≤ A*A :=
    square_le_of_abs_le (scalarCeiling_nonnegative s cs)
      (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv
      (d (smulStage (s.approx m) (X.seq m)) (smulStage (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    have hscaled := leEv_mul_nonneg_left hfactor (X.isCauchy delta hdlt m n hXm hXn)
    exact leEv_trans
      (leEv_of_equiv (distSq_smul hw0 hw1 hsmall hd hs (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hdlt))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond : leEv
      (d (smulStage (s.approx m) (X.seq n)) (smulStage (s.approx n) (X.seq n)))
      (ofQ' (quarter epsilon)) :=
    scalar_change_bound hw0 hw1 hsmall hd hs (s.approx m) (s.approx n) B epsilon hB he
      (X.seq n) (diagonal_le_normCeiling PD X n hnormn)
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
    (distance_triangle hw0 hw1 hsmall hd hs
      (smulStage (s.approx m) (X.seq m)) (smulStage (s.approx m) (X.seq n))
      (smulStage (s.approx n) (X.seq n)))
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

/-- No chosen representatives: this input stream and scalar rate are supplied. -/
def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := smulStage (s.approx n) (X.seq n)
  modulus := realScalarRate hw0 hw1 hsmall hd hs s cs X
  isCauchy := realScalar_bound hw0 hw1 hsmall hd hs s cs X

theorem realScalarCauchy_seq (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (n : Nat) :
    (realScalarCauchy hw0 hw1 hsmall hd hs s cs X).seq n =
      smulStage (s.approx n) (X.seq n) := rfl

theorem realScalarCauchy_modulus (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : (realScalarCauchy hw0 hw1 hsmall hd hs s cs X).modulus epsilon =
      realScalarRate hw0 hw1 hsmall hd hs s cs X epsilon := rfl

end YMGap.Continuum.BF4SpatialUnionRealScalarCauchy

#print axioms YMGap.Continuum.BF4SpatialUnionRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4SpatialUnionRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4SpatialUnionRealScalarCauchy.realScalarCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionRealScalarCauchy.realScalarCauchy_seq
#print axioms YMGap.Continuum.BF4SpatialUnionRealScalarCauchy.realScalarCauchy_modulus
