/-
# Jacobi weight removal in ORIGINAL Haar order, uniformly over placements

The literal original face deficit is split into a finite label band and
its high-spin tail. Sharp character intervals pay both parts, rather than
a syntactic coefficient norm depending on the plaquette's placement.
The returned cutoff depends only on the supplied nome and tolerance.
The certificate therefore survives arbitrary positive shared-link
backgrounds without a background-size factor.

This is weight-removal/truncation control, not low-spin spatial decay,
coupling-uniform clustering, physical scaling or a mass-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
import YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval

namespace YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval (deficit deficit_bounds deficit_abs_small faceDeficit)
open YMGap.Continuum.FiniteJacobiWeightConvergence (centeredCutoff)
open YMGap.Continuum.PolynomialWeightedSumBounds (sum_range_add)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def weightedRangeInterval {blocks : Nat} (f : Nat → RatPoly) (c a : Nat → Q')
    (hI : ∀ r, Interval blocks (f r) (c r)) (ha : ∀ r, (0 : Q') ≤ a r)
    (N : Nat) (A : Q') (hA : ∀ r, r < N → a r ≤ A) :
    Interval blocks (finitePolySum (fun r => polySmul (a r) (f r)) (List.range N)) (A * finSum c N) :=
  (Interval.finiteRange _ _ (fun r => (hI r).smul (a r) (ha r)) N).weaken
    (Q'.le_trans' _ _ _ (finSum_le_lt _ _ N (fun r hr =>
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hA r hr) (hI r).nonnegative))
      (Q'.ge_of_eqv (const_mul_finSum c A N)))

def bandSize (w epsilon : Q') : Nat := tailCutoff w (HalfPow.half * epsilon) + 1

def weightTolerance (w epsilon : Q') : Q' :=
  HKConv.divPos (HalfPow.half * epsilon) (prefixCap w + 1)

theorem weightTolerance_positive (w : Q') {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < weightTolerance w epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ he))

theorem weightTolerance_budget {w epsilon : Q'} (hw0 : (0 : Q') < w) (he : (0 : Q') < epsilon) :
    weightTolerance w epsilon * prefixCap w ≤ HalfPow.half * epsilon := by
  have hp : (0 : Q') < prefixCap w + 1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (prefixCap_nonnegative hw0))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (weightTolerance_positive w he)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

/-- Number of labels N needed to remove the finite Jacobi weights in Haar order. -/
def deficitCutoff (w epsilon : Q') : Nat :=
  centeredCutoff (w*w) (bandSize w epsilon) (weightTolerance w epsilon)

theorem bandSize_le_deficitCutoff (w epsilon : Q') : bandSize w epsilon ≤ deficitCutoff w epsilon :=
  Nat.le_add_right _ _

private theorem majorant_tail_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : tailCutoff w epsilon ≤ K) :
    finSum (fun r => pointwiseHeatMajorant w (K+1+r)) L ≤ epsilon := by
  have hN : spacingLabelCutoff w ≤ K+1 := by unfold tailCutoff at hK; omega
  have hM : spacingTailCauchyCutoff w epsilon ≤ K+1-spacingLabelCutoff w := by
    unfold tailCutoff at hK
    omega
  have h := shiftedMajorant_block hw0 hw1 (K+1-spacingLabelCutoff w) L
  simp only [← Nat.add_assoc, Nat.add_sub_of_le hN] at h
  exact Q'.le_trans' _ _ _ h (closedTail_small hw0 hw1 epsilon he _ hM)

/-- Actual old faceDeficit, with one cutoff valid for EVERY physical face/extent. -/
def faceDeficitInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (epsilon : Q') (he : (0 : Q') < epsilon)
    (N : Nat) (hN : deficitCutoff w epsilon ≤ N) :
    Interval (boundaryCompleteSlabLinks extent).length (faceDeficit w N extent id) epsilon := by
  let J := bandSize w epsilon
  let delta := weightTolerance w epsilon
  have hd : (0 : Q') < delta := weightTolerance_positive w he
  have hJN : J ≤ N := Nat.le_trans (bandSize_le_deficitCutoff w epsilon) hN
  let head := weightedRangeInterval (faceHeatTerm w extent id) (pointwiseHeatMajorant w) (deficit w N)
    (heatTermInterval (Q'.le_of_lt hw0) extent id hi) (fun r => (deficit_bounds hw0 hw1 N r).1)
    J delta (fun r hr => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (deficit_abs_small hw0 hw1 J hd N r hN hr))
  have hhead : delta * finSum (pointwiseHeatMajorant w) J ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (majorant_prefix_bound hw0 hw1 J) (Q'.le_of_lt hd)) (weightTolerance_budget hw0 he)
  let tail := weightedRangeInterval (fun r => faceHeatTerm w extent id (J+r))
    (fun r => pointwiseHeatMajorant w (J+r)) (fun r => deficit w N (J+r))
    (fun r => heatTermInterval (Q'.le_of_lt hw0) extent id hi (J+r))
    (fun r => (deficit_bounds hw0 hw1 N (J+r)).1) (N-J) 1
    (fun r _ => (deficit_bounds hw0 hw1 N (J+r)).2)
  have htail : (1 : Q') * finSum (fun r => pointwiseHeatMajorant w (J+r)) (N-J) ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (majorant_tail_small hw0 hw1 (HalfPow.half*epsilon) (ExpNeg.half_mul_pos _ he)
        (tailCutoff w (HalfPow.half*epsilon)) (N-J) (Nat.le_refl _))
  have hsplit := sum_range_add (fun r => polySmul (deficit w N r) (faceHeatTerm w extent id r)) J (N-J)
  rw [Nat.add_sub_of_le hJN] at hsplit
  unfold faceDeficit
  rw [hsplit]
  exact ((head.weaken hhead).add (tail.weaken htail)).changeCap (ExpNeg.two_halves epsilon)

theorem faceDeficit_weighted_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (epsilon : Q') (he : (0 : Q') < epsilon)
    (N : Nat) (hN : deficitCutoff w epsilon ≤ N) {p : RatPoly}
    (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    Q'.abs (quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceDeficit w N extent id))) ≤
      epsilon * quaternionHaar (boundaryCompleteSlabLinks extent).length p :=
  (faceDeficitInterval hw0 hw1 extent id hi epsilon he N hN).weighted_haar_bound P

end YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval

#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.bandSize
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.weightTolerance
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.weightTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.weightTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.deficitCutoff
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.bandSize_le_deficitCutoff
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.faceDeficitInterval
#print axioms YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval.faceDeficit_weighted_bound
