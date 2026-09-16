/-
# Witnessed real-scalar laws on the SAME spatial union completion

Scalar sums and products use the existing computed QCauchy data. Testing
against the actual completed pairing proves the module laws without
selecting vector or scalar representatives. The same physical time commutes
with real scaling, and the actual squared distance scales quadratically.

These are laws for supplied modulus-bearing CReal scalars, not a choice of
modulus for arbitrary legacy RC values or an assertion of full QFT structure.
-/

import YMGap.Continuum.BF4SpatialUnionCompletedRealScalar
import YMGap.Continuum.BF4SpatialUnionCompletedDistance
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4SpatialUnionGeometry (completedInner_time_balance)
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4SpatialUnionCompletedDistance (completedDist)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "S" => completedRealSmul hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

theorem completedRealSmul_addScalar (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S (add s t) (scalarAddCauchy s t cs ct) x =
      completedAdd hw0 hw1 hsmall hd hs (S s cs x) (S t ct x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_realSmul_left, completedInner_add_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv (s.approx n) (t.approx n) (X.approx n)))

theorem completedRealSmul_mul (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : V) :
    S s cs (S t ct x) = S (mul s t) (scalarMulCauchy s t cs ct) x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_realSmul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv (s.approx n) (t.approx n) (X.approx n))))

theorem completedRealSmul_neg (s : CReal) (cs : QCauchy s.approx) (x : V) :
    S s cs (completedNeg hw0 hw1 hsmall hd hs x) =
      completedNeg hw0 hw1 hsmall hd hs (S s cs x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_realSmul_left, completedInner_neg_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_neg_eqv (s.approx n) (X.approx n)))

theorem completedRealSmul_sub (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    S s cs (completedSub hw0 hw1 hsmall hd hs x y) =
      completedSub hw0 hw1 hsmall hd hs (S s cs x) (S s cs y) := by
  unfold completedSub
  rw [completedRealSmul_add, completedRealSmul_neg]

theorem completedInner_realSmul_both (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B (S s cs x) (S s cs y) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (B x y)) := by
  rw [completedInner_realSmul_left, completedInner_realSmul_right]

theorem completedInner_realSmul_diagonal (s : CReal) (cs : QCauchy s.approx) (x : V) :
    B (S s cs x) (S s cs x) =
      RCmul (Quotient.mk crealSetoid s) (RCmul (Quotient.mk crealSetoid s) (B x x)) :=
  completedInner_realSmul_both hw0 hw1 hsmall hd hs s cs x x

/-- Orthogonality is retained for the actual vectors, without re-centering. -/
theorem completedRealSmul_orthogonal (s : CReal) (cs : QCauchy s.approx)
    (x y : V) (h : B x y = RCzero) : B (S s cs x) y = RCzero := by
  rw [completedInner_realSmul_left, h]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (s.approx n)))

theorem completedTime_realSmul (n : Nat) (s : CReal) (cs : QCauchy s.approx) (x : V) :
    T n (S s cs x) = S s cs (T n x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_time_balance, completedInner_realSmul_left,
    completedInner_realSmul_left, completedInner_time_balance]

/-- The squared distance, rather than a chosen square-root norm, scales by s squared. -/
theorem completedDist_realSmul (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    completedDist hw0 hw1 hsmall hd hs (S s cs x) (S s cs y) =
      RCmul (Quotient.mk crealSetoid s)
        (RCmul (Quotient.mk crealSetoid s) (completedDist hw0 hw1 hsmall hd hs x y)) := by
  unfold completedDist
  rw [← completedRealSmul_sub, completedInner_realSmul_diagonal]

#print axioms completedRealSmul_addScalar
#print axioms completedRealSmul_mul
#print axioms completedRealSmul_neg
#print axioms completedRealSmul_sub
#print axioms completedInner_realSmul_both
#print axioms completedInner_realSmul_diagonal
#print axioms completedRealSmul_orthogonal
#print axioms completedTime_realSmul
#print axioms completedDist_realSmul

end YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra
