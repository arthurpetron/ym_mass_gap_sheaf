/-
# Explicit removal of finite Jacobi weights on ORIGINAL face polynomials

A computed finite band pays half the tolerance using convergence of the
actual Jacobi weights. The original coefficient tail pays the other half.
The literal deficit sum has small syntactic coefficient L1; no cancellation
in that norm or pointwise-to-Haar convergence principle is assumed.

Every cutoff depends on the supplied nome, extent, face and tolerance.
This proves one-face coefficient/Haar error control, not a physical gap.
-/

import YMGap.Continuum.PolynomialWeightedSumBounds
import YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin
import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound
import YMGap.Continuum.FiniteJacobiWeightConvergence

namespace YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.PolynomialWeightedSumBounds
open YMGap.Continuum.JacobiWeightedHeatPolynomial
open YMGap.Continuum.FiniteJacobiWeightConvergence

local infix:50 " ≈ " => Q'.eqv

def deficit (w : Q') (N r : Nat) : Q' := 1 + -(weight w N r)

theorem weight_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N r : Nat) :
    (0 : Q') ≤ weight w N r ∧ weight w N r ≤ (1 : Q') :=
  FiniteJacobiWeightBounds.centeredWeight_bounds (HKPos.q_mul_pos hw0 hw0)
    (FiniteJacobiCoefficients.square_base_lt_one hw0 hw1) N (r + 1)

theorem weight_abs_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N r : Nat) :
    Q'.abs (weight w N r) ≤ (1 : Q') := by
  rw [ExpNeg.abs_of_nonneg (weight_bounds hw0 hw1 N r).1]
  exact (weight_bounds hw0 hw1 N r).2

theorem deficit_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N r : Nat) :
    (0 : Q') ≤ deficit w N r ∧ deficit w N r ≤ (1 : Q') := by
  have h := weight_bounds hw0 hw1 N r
  exact ⟨Q'.sub_nonneg_of_le h.2, Q'.sub_le_of_le_add
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ h.1) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))⟩

theorem deficit_abs_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N r : Nat) :
    Q'.abs (deficit w N r) ≤ (1 : Q') := by
  rw [ExpNeg.abs_of_nonneg (deficit_bounds hw0 hw1 N r).1]
  exact (deficit_bounds hw0 hw1 N r).2

/-- Small weights on a named finite label band; label r uses centered index r+1. -/
theorem deficit_abs_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (J : Nat) {δ : Q'} (hδ : (0 : Q') < δ) (N r : Nat)
    (hN : centeredCutoff (w * w) J δ ≤ N) (hr : r < J) :
    Q'.abs (deficit w N r) ≤ δ :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm 1 (weight w N r)))
    (centeredWeight_abs_close (HKPos.q_mul_pos hw0 hw0)
      (FiniteJacobiCoefficients.square_base_lt_one hw0 hw1) J hδ N (r + 1) hN (by omega))

/-- The actual deficit polynomial, with all original shared variables. -/
def faceDeficit (w : Q') (N extent id : Nat) : RatPoly :=
  finitePolySum (fun r => polySmul (deficit w N r) (faceHeatTerm w extent id r)) (List.range N)

theorem faceHeat_eq_weighted_add_deficit (w : Q') (K extent id : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial w K extent id)
      (polyAdd (weightedFace w (K + 1) extent id) (faceDeficit w (K + 1) extent id)) := by
  rw [faceHeatPolynomial_eq_sum]
  exact (weighted_recombine (faceHeatTerm w extent id) (weight w (K + 1)) (List.range (K + 1))).symm

/-- The original cutoff-independent face bound also covers every weighted prefix. -/
theorem weightedFace_coefficientL1_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) : ∀ N : Nat,
    polynomialCoefficientL1 (weightedFace w N extent id) ≤ faceHeatBound w extent id
  | 0 => faceHeatBound_nonnegative (Q'.le_of_lt hw0) extent id
  | K + 1 => by
      have h := weighted_coefficientL1_le_one (faceHeatTerm w extent id) (weight w (K + 1))
        (List.range (K + 1)) (fun r _ => weight_abs_le_one hw0 hw1 (K + 1) r)
      rw [← faceHeatPolynomial_eq_sum] at h
      exact Q'.le_trans' _ _ _ h (faceHeat_coefficientL1_bound hw0 hw1 extent id K)

/-- Original tail starts AFTER this computed number of initial labels. -/
def bandLength (w : Q') (extent id : Nat) (ε : Q') : Nat :=
  faceHeatCutoff w extent id (HalfPow.half * ε) + 1

/-- Explicit finite-band weight budget, scaled by the original full face bound. -/
def bandTolerance (w : Q') (extent id : Nat) (ε : Q') : Q' :=
  HKConv.divPos (HalfPow.half * ε) (faceHeatBound w extent id + 1)

theorem bandTolerance_pos (w : Q') (extent id : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < bandTolerance w extent id ε :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hε))

theorem bandTolerance_budget {w : Q'} (hw0 : (0 : Q') < w) (extent id : Nat)
    {ε : Q'} (hε : (0 : Q') < ε) :
    bandTolerance w extent id ε * faceHeatBound w extent id ≤ HalfPow.half * ε := by
  have hB := faceHeatBound_nonnegative (Q'.le_of_lt hw0) extent id
  have hp : (0 : Q') < faceHeatBound w extent id + 1 := Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (bandTolerance_pos w extent id hε)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

/-- Type-level all-later cutoff: no index is extracted from a convergence proposition. -/
def weightRemovalCutoff (w : Q') (extent id : Nat) (ε : Q') : Nat :=
  centeredCutoff (w * w) (bandLength w extent id ε) (bandTolerance w extent id ε)

theorem bandLength_le_weightRemovalCutoff (w : Q') (extent id : Nat) (ε : Q') :
    bandLength w extent id ε ≤ weightRemovalCutoff w extent id ε := Nat.le_add_right _ _

/-- Both parts of the literal deficit are bounded in coefficient L1.
The finite-band and tail budgets each pay half of the supplied tolerance. -/
theorem faceDeficit_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (ε : Q') (hε : (0 : Q') < ε) (N : Nat)
    (hN : weightRemovalCutoff w extent id ε ≤ N) :
    polynomialCoefficientL1 (faceDeficit w N extent id) ≤ ε := by
  let J := bandLength w extent id ε
  let δ := bandTolerance w extent id ε
  have hδ : (0 : Q') < δ := bandTolerance_pos w extent id hε
  have hJN : J ≤ N := Nat.le_trans (bandLength_le_weightRemovalCutoff w extent id ε) hN
  have hhead := weighted_coefficientL1_le (faceHeatTerm w extent id) (deficit w N) δ
    (List.range J) (fun r hr => deficit_abs_small hw0 hw1 J hδ N r hN (List.mem_range.mp hr))
  have hheadNorm : polynomialCoefficientL1 (finitePolySum (faceHeatTerm w extent id) (List.range J))
      ≤ faceHeatBound w extent id := by
    change polynomialCoefficientL1 (finitePolySum (faceHeatTerm w extent id)
      (List.range (faceHeatCutoff w extent id (HalfPow.half * ε) + 1))) ≤ _
    rw [← faceHeatPolynomial_eq_sum]
    exact faceHeat_coefficientL1_bound hw0 hw1 extent id _
  have hheadSmall := Q'.le_trans' _ _ _ hhead
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hheadNorm (Q'.le_of_lt hδ))
      (bandTolerance_budget hw0 extent id hε))
  have htail := weighted_coefficientL1_le_one (fun r => faceHeatTerm w extent id (J + r))
    (fun r => deficit w N (J + r)) (List.range (N - J))
    (fun r _ => deficit_abs_le_one hw0 hw1 N (J + r))
  have htailSmall := Q'.le_trans' _ _ _ htail
    (faceHeatTail_small hw0 hw1 extent id (HalfPow.half * ε) (ExpNeg.half_mul_pos _ hε)
      (faceHeatCutoff w extent id (HalfPow.half * ε)) (N - J) (Nat.le_refl _))
  have hsplit := sum_range_add (fun r => polySmul (deficit w N r) (faceHeatTerm w extent id r)) J (N - J)
  rw [Nat.add_sub_of_le hJN] at hsplit
  unfold faceDeficit
  rw [hsplit]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
    (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hheadSmall htailSmall) (Q'.le_of_eqv (ExpNeg.two_halves ε)))

theorem faceDeficit_haar_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent id : Nat) (ε : Q') (hε : (0 : Q') < ε) (N : Nat)
    (hN : weightRemovalCutoff w extent id ε ≤ N) :
    Q'.abs (quaternionHaar blocks (faceDeficit w N extent id)) ≤ ε :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _) (faceDeficit_small hw0 hw1 extent id ε hε N hN)

end YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval

#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.deficit
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.weight_bounds
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.weight_abs_le_one
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.deficit_bounds
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.deficit_abs_le_one
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.deficit_abs_small
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.faceDeficit
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.faceHeat_eq_weighted_add_deficit
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.weightedFace_coefficientL1_bound
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.bandLength
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.bandTolerance
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.bandTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.bandTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.weightRemovalCutoff
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.bandLength_le_weightRemovalCutoff
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.faceDeficit_small
#print axioms YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval.faceDeficit_haar_small
