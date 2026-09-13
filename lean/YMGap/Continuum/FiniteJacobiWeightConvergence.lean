/-
# Constructive convergence of the actual finite Jacobi weights

The two-segment formula supplies the explicit loss 2 Q^(N-j+1)/(1-Q).
This module turns that estimate into a COMPUTABLE cutoff, uniform for all
j in a supplied finite band 0..J. No index is extracted from a Prop-level
existential, and no convergence uniform over all j or all Q is claimed.

The original finite weights remain bounded in [0,1] even outside the band.
Combining the finite-band modulus with Gaussian/Chebyshev tails, and passing
to the differentiated Jacobi limit, are subsequent obligations.
-/

import YMGap.Continuum.FiniteJacobiWeightBounds
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.FiniteJacobiWeightConvergence

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteJacobiWeightBounds

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The base-dependent prefactor 2/(1-Q), exposed as data. -/
def lossScale (Q : Q') : Q' := (2 : Q') * HKConv.divPos 1 (1 + -Q)

theorem lossScale_nonnegative (Q : Q') : (0 : Q') ≤ lossScale Q :=
  Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (HKConv.divPos_nonneg Q'.zero_le_one)

/-- The rational tolerance supplied to the existing power cutoff. -/
def lossTolerance (Q ε : Q') : Q' := HKConv.divPos ε (lossScale Q + 1)

theorem lossTolerance_pos (Q : Q') {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < lossTolerance Q ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem lossTolerance_budget (Q : Q') {ε : Q'} (hε : (0 : Q') < ε) :
    lossScale Q * lossTolerance Q ε ≤ ε := by
  have hp : (0 : Q') < lossScale Q + 1 := Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (lossScale_nonnegative Q))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_lt (lossTolerance_pos Q hε)))
      (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp))))

/-- Type-level cutoff for the geometric coefficient deficit. -/
def lossCutoff (Q ε : Q') : Nat := HKConvGen.powBaseCutoff Q (lossTolerance Q ε)

/-- All later distances satisfy the requested deficit budget. -/
theorem lossBound_le {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (n : Nat) (hn : lossCutoff Q ε ≤ n) :
    lossBound Q n ≤ ε := by
  have hpow : Q ^ n ≤ lossTolerance Q ε := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hQ0) (Q'.le_of_lt hQ1) hn)
    (HKConvGen.pow_base_le_cutoff hQ0 hQ1 (lossTolerance_pos Q hε))
  have he : lossBound Q n ≈ lossScale Q * Q ^ n := by
    unfold lossBound HKConvGen.geoTailBase lossScale
    mul_add_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (lossScale_nonnegative Q))
      (lossTolerance_budget Q hε))

/-- Absolute deficit bound for each actual coefficient in range. -/
theorem centeredWeight_abs_loss {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    Q'.abs (centeredWeight Q N j + -(1 : Q')) ≤ lossBound Q (N - j + 1) := by
  apply Q'.abs_le
  · exact Q'.neg_le_sub_of_le_add (one_le_centeredWeight_add_loss hQ0 hQ1 N j hj)
  · apply Q'.sub_le_of_le_add
    exact Q'.le_trans' _ _ _ (centeredWeight_le_one hQ0 hQ1 N j hj)
      (Q'.add_le_self_of_nonneg 1 _ (lossBound_nonnegative (Q'.le_of_lt hQ0) _))

/-- Cutoff uniform over the NAMED finite coefficient band j<=J, at the
NAMED base Q and tolerance epsilon. No choice is used to produce it. -/
def centeredCutoff (Q : Q') (J : Nat) (ε : Q') : Nat := J + lossCutoff Q ε

/-- The actual normalized coefficients converge to one, uniformly on every
supplied finite band, with the explicit cutoff above. -/
theorem centeredWeight_abs_close {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (J : Nat) {ε : Q'} (hε : (0 : Q') < ε) (N j : Nat)
    (hN : centeredCutoff Q J ε ≤ N) (hj : j ≤ J) :
    Q'.abs (centeredWeight Q N j + -(1 : Q')) ≤ ε := by
  have hNj : j ≤ N := by unfold centeredCutoff at hN; omega
  have hn : lossCutoff Q ε ≤ N - j + 1 := by unfold centeredCutoff at hN; omega
  exact Q'.le_trans' _ _ _ (centeredWeight_abs_loss hQ0 hQ1 N j hNj)
    (lossBound_le hQ0 hQ1 hε _ hn)

end YMGap.Continuum.FiniteJacobiWeightConvergence

#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossScale
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossScale_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossTolerance
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossTolerance_pos
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossTolerance_budget
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossCutoff
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.lossBound_le
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.centeredWeight_abs_loss
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.centeredCutoff
#print axioms YMGap.Continuum.FiniteJacobiWeightConvergence.centeredWeight_abs_close
