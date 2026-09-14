/-
# Preserve an eventual original numerator floor through SAME normalization

A lower bound rho*Z_K^2 <= N_K, valid beyond an explicit cutoff start,
passes to the already constructed original limits. Multiplication by the
existing positive action reciprocal twice cancels the SAME partition
square, leaving rho <= covariance. No reciprocal ceiling, replacement
functional or new analytic input is used. All streams retain QCauchy data.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeCovariance

namespace YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabTwoProbeCovariance
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def originalStream (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon,c.bound epsilon he⟩

theorem originalStream_limit (r : Nat → Q') (c : QCauchy r) :
    Equiv (originalStream r c) (ofQ'CauchySeq r c) := by
  intro epsilon he
  exact ⟨c.M epsilon,fun n hn => c.bound epsilon he n _ hn
    (Nat.le_trans hn (self_le_QMhat r c n))⟩

theorem order_of_eventual_approx {a b : CReal} (start : Nat)
    (h : ∀ n, start ≤ n → a.approx n ≤ b.approx n) : leEv a b := by
  intro epsilon he
  exact ⟨start,fun n hn => Q'.le_trans' _ _ _ (h n hn)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem multiply_right_order {a b r : CReal} (hr : leEv czero r) (h : leEv a b) :
    leEv (CReal.mul a r) (CReal.mul b r) :=
  (leEv_congr (CRealAlg.cmul_comm _ _) (CRealAlg.cmul_comm _ _)).mp (leEv_mul_nonneg_left hr h)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

local notation "extent" => centralExtent half
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "faces" => slabPhysicalFaceEdges extent
local notation "Z" => fullActionLimit w hw0 hw1 half
local notation "L" => actionReciprocal w hw0 hw1 half

theorem connectedNumeratorLimit_floor (p q : RatPoly) (rho : Q') (start : Nat)
    (h : ∀ K, start ≤ K → rho*partitionSquare w K extent faces ≤ connectedNumerator w K extent faces p q) :
    leEv (CReal.mul (ofQ' rho) (CReal.mul Z Z)) (connectedNumeratorLimit w hw0 hw1 half p q) := by
  let d := originalStream _ (connectedNumeratorCauchy w hw0 hw1 half p q)
  let z := originalStream _ (heatProductHaarCauchy w hw0 hw1 blocks extent faces)
  have hd : Equiv d (connectedNumeratorLimit w hw0 hw1 half p q) := originalStream_limit _ _
  have hz : Equiv z Z := originalStream_limit _ _
  have hraw : leEv (CReal.mul (ofQ' rho) (CReal.mul z z)) d := order_of_eventual_approx start h
  exact (leEv_congr
    (Pivot2.mul_congr_right ((Pivot2.mul_congr_left hz).trans (Pivot2.mul_congr_right hz))) hd).mp hraw

theorem covariance_floor (p q : RatPoly) (rho : Q') (start : Nat)
    (h : ∀ K, start ≤ K → rho*partitionSquare w K extent faces ≤ connectedNumerator w K extent faces p q) :
    leEv (ofQ' rho) (covariance w hw0 hw1 half p q) := by
  have hl := reciprocal_nonnegative w hw0 hw1 half
  have hn := connectedNumeratorLimit_floor w hw0 hw1 half p q rho start h
  exact leEv_trans (leEv_of_equiv (normalizedPartition_cancel w hw0 hw1 half 0 rho).symm)
    (leEv_trans (multiply_right_order hl (multiply_right_order hl hn))
      (leEv_of_equiv (covariance_formula w hw0 hw1 half p q)))

theorem covariance_swap (p q : RatPoly) :
    Equiv (covariance w hw0 hw1 half p q) (covariance w hw0 hw1 half q p) :=
  (CReal.sub_congr_left (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.mul_comm p q))).trans
    (CReal.sub_congr_right (CRealAlg.cmul_comm _ _))

end YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport

#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.originalStream
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.originalStream_limit
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.order_of_eventual_approx
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.multiply_right_order
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.connectedNumeratorLimit_floor
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.covariance_floor
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceLowerTransport.covariance_swap
