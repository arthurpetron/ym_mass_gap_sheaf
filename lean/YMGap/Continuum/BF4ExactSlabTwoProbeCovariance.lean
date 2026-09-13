/-
# Distance decay after removing the ORIGINAL representation cutoff

The same-cutoff connected numerator has a computed Cauchy modulus.
Its limit is N(pq)Z-N(p)N(q) for the existing original moment limits.
Multiplying by the existing positive reciprocal twice identifies it with
E(pq)-E(p)E(q), and cancels the SAME partition square in the finite bound.
No volume-dependent reciprocal ceiling enters the resulting coefficient.

This is normalized finite-volume clustering under explicit small-nome
guards. Thermodynamic transport, actual reflected-time instances, strict
operator gap and continuum scaling are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
import YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabTwoProbeCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def streamReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private theorem streamReal_eq_limit (r : Nat → Q') (c : QCauchy r) :
    Equiv (streamReal r c) (ofQ'CauchySeq r c) := by
  intro epsilon he
  exact ⟨c.M epsilon, fun n hn => c.bound epsilon he n _ hn
    (Nat.le_trans hn (self_le_QMhat r c n))⟩

private theorem order_of_approx {a b : CReal} (h : ∀ n, a.approx n ≤ b.approx n) : leEv a b := by
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _ (h n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

private theorem mul_right_mono {a b r : CReal} (hr : leEv czero r) (h : leEv a b) :
    leEv (CReal.mul a r) (CReal.mul b r) :=
  (leEv_congr (CRealAlg.cmul_comm _ _) (CRealAlg.cmul_comm _ _)).mp (leEv_mul_nonneg_left hr h)

private theorem abs_mul_right {a r : CReal} (hr : ∀ n, (0 : Q') ≤ r.approx n) :
    leEv (CReal.abs (CReal.mul a r)) (CReal.mul (CReal.abs a) r) := by
  apply order_of_approx
  intro n
  have h := ExpNeg.abs_mul_le (a.approx n) (r.approx n)
  rw [ExpNeg.abs_of_nonneg (hr n)] at h
  exact h

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

local notation "extent" => centralExtent half
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "faces" => slabPhysicalFaceEdges extent
local notation "N" => numeratorLimit w hw0 hw1 blocks extent faces
local notation "Z" => fullActionLimit w hw0 hw1 half
local notation "L" => actionReciprocal w hw0 hw1 half
local notation "E" => expectation w hw0 hw1 half

private def rawMoment (p : RatPoly) : CReal := streamReal _ (numeratorCauchy w hw0 hw1 blocks extent faces p)
private def rawPartition : CReal := streamReal _ (heatProductHaarCauchy w hw0 hw1 blocks extent faces)

/-- Data-bearing modulus of the actual common-cutoff determinant, not four reindexed cutoffs. -/
def connectedNumeratorCauchy (p q : RatPoly) : QCauchy (fun K => connectedNumerator w K extent faces p q) :=
  scalarAddCauchy _ _
    (scalarMulCauchy (rawMoment w hw0 hw1 half (polyMul p q)) (rawPartition w hw0 hw1 half)
      (numeratorCauchy w hw0 hw1 blocks extent faces (polyMul p q)) (heatProductHaarCauchy w hw0 hw1 blocks extent faces))
    (scalarNegCauchy _ (scalarMulCauchy (rawMoment w hw0 hw1 half p) (rawMoment w hw0 hw1 half q)
      (numeratorCauchy w hw0 hw1 blocks extent faces p) (numeratorCauchy w hw0 hw1 blocks extent faces q)))

def connectedNumeratorLimit (p q : RatPoly) : CReal := ofQ'CauchySeq _ (connectedNumeratorCauchy w hw0 hw1 half p q)

def connectedNumeratorCutoff (p q : RatPoly) : Q' → Nat := (connectedNumeratorCauchy w hw0 hw1 half p q).M

theorem connectedNumerator_approx_close (p q : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat) (hK : connectedNumeratorCutoff w hw0 hw1 half p q epsilon ≤ K)
    (hn : connectedNumeratorCutoff w hw0 hw1 half p q epsilon ≤ n) :
    connectedNumerator w K extent faces p q ≤ (connectedNumeratorLimit w hw0 hw1 half p q).approx n + epsilon ∧
    (connectedNumeratorLimit w hw0 hw1 half p q).approx n ≤ connectedNumerator w K extent faces p q + epsilon :=
  (connectedNumeratorCauchy w hw0 hw1 half p q).bound epsilon he K _ hK
    (Nat.le_trans hn (self_le_QMhat _ _ n))

theorem connectedNumeratorLimit_formula (p q : RatPoly) :
    Equiv (connectedNumeratorLimit w hw0 hw1 half p q)
      (CReal.sub (CReal.mul (N (polyMul p q)) Z) (CReal.mul (N p) (N q))) := by
  have hm (r : RatPoly) : Equiv (rawMoment w hw0 hw1 half r) (N r) := streamReal_eq_limit _ _
  have hz : Equiv (rawPartition w hw0 hw1 half) Z := streamReal_eq_limit _ _
  have hraw : Equiv
      (CReal.sub (CReal.mul (rawMoment w hw0 hw1 half (polyMul p q)) (rawPartition w hw0 hw1 half))
        (CReal.mul (rawMoment w hw0 hw1 half p) (rawMoment w hw0 hw1 half q)))
      (connectedNumeratorLimit w hw0 hw1 half p q) := streamReal_eq_limit _ _
  exact hraw.symm.trans
    ((CReal.sub_congr_left ((Pivot2.mul_congr_left (hm (polyMul p q))).trans (Pivot2.mul_congr_right hz))).trans
      (CReal.sub_congr_right ((Pivot2.mul_congr_left (hm p)).trans (Pivot2.mul_congr_right (hm q)))))

/-- The existing original expectations, on one and the same finite slab. -/
def covariance (p q : RatPoly) : CReal := CReal.sub (E (polyMul p q)) (CReal.mul (E p) (E q))

def covarianceCauchy (p q : RatPoly) : QCauchy (covariance w hw0 hw1 half p q).approx :=
  scalarAddCauchy _ _ (expectationCauchy w hw0 hw1 half (polyMul p q))
    (scalarNegCauchy _ (scalarMulCauchy _ _ (expectationCauchy w hw0 hw1 half p) (expectationCauchy w hw0 hw1 half q)))

theorem covariance_formula (p q : RatPoly) :
    Equiv (CReal.mul (CReal.mul (connectedNumeratorLimit w hw0 hw1 half p q) L) L)
      (covariance w hw0 hw1 half p q) := by
  refine ((Pivot2.mul_congr_left (Pivot2.mul_congr_left (connectedNumeratorLimit_formula w hw0 hw1 half p q)))).trans ?_
  have hs : Equiv
      (CReal.mul (CReal.mul (CReal.sub (CReal.mul (N (polyMul p q)) Z) (CReal.mul (N p) (N q))) L) L)
      (CReal.sub (CReal.mul (E (polyMul p q)) (CReal.mul Z L)) (CReal.mul (E p) (E q))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.var 4)) (.var 4))
      (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))
        (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 4))))) (by decide)
      (fun | 0 => (N (polyMul p q)).approx n | 1 => (Z).approx n | 2 => (N p).approx n | 3 => (N q).approx n | _ => (L).approx n)
  exact hs.trans (CReal.sub_congr_left
    ((Pivot2.mul_congr_right (action_mul_reciprocal w hw0 hw1 half)).trans (CRealAlg.cmul_cone _)))

theorem connectedNumeratorLimit_bound (p q : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (connectedNumerator w K extent faces p q) ≤ b*partitionSquare w K extent faces) :
    leEv (CReal.abs (connectedNumeratorLimit w hw0 hw1 half p q)) (CReal.mul (ofQ' b) (CReal.mul Z Z)) := by
  let d := streamReal _ (connectedNumeratorCauchy w hw0 hw1 half p q)
  let z := rawPartition w hw0 hw1 half
  have hd : Equiv d (connectedNumeratorLimit w hw0 hw1 half p q) := streamReal_eq_limit _ _
  have hz : Equiv z Z := streamReal_eq_limit _ _
  have hraw : leEv (CReal.abs d) (CReal.mul (ofQ' b) (CReal.mul z z)) := order_of_approx h
  exact (leEv_congr (abs_equiv_congr hd)
    (Pivot2.mul_congr_right ((Pivot2.mul_congr_left hz).trans (Pivot2.mul_congr_right hz)))).mp hraw

theorem covariance_bound (p q : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (connectedNumerator w K extent faces p q) ≤ b*partitionSquare w K extent faces) :
    leEv (CReal.abs (covariance w hw0 hw1 half p q)) (ofQ' b) := by
  have hl := reciprocal_nonnegative w hw0 hw1 half
  have habs := leEv_trans
    (abs_mul_right (a := CReal.mul (connectedNumeratorLimit w hw0 hw1 half p q) L)
      (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n)))
    (mul_right_mono hl (abs_mul_right (a := connectedNumeratorLimit w hw0 hw1 half p q)
      (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))))
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (covariance_formula w hw0 hw1 half p q).symm))
    (leEv_trans habs (leEv_trans
      (mul_right_mono hl (mul_right_mono hl (connectedNumeratorLimit_bound w hw0 hw1 half p q b h)))
      (leEv_of_equiv (BF4ExactSlabBoundaryLimitNormalization.normalizedPartition_cancel w hw0 hw1 half 0 b))))

/-- The proved finite distance coefficient survives cutoff removal and exact normalization unchanged. -/
theorem covariance_distance_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (p q : RatPoly) (c d : Q')
    (Ip : Interval blocks p c) (Iq : Interval blocks q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    leEv (CReal.abs (covariance w hw0 hw1 half p q)) (ofQ' (distanceBudget P Q w hd hs c d)) :=
  covariance_bound w hw0 hw1 half p q _ (fun K =>
    full_connectedNumerator_distance_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
      K extent p q c d Ip Iq left right P Q hl hr)

end YMGap.Continuum.BF4ExactSlabTwoProbeCovariance

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumeratorCauchy
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumeratorLimit
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumeratorCutoff
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumerator_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumeratorLimit_formula
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.covariance
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.covarianceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.covariance_formula
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.connectedNumeratorLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.covariance_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCovariance.covariance_distance_bound
