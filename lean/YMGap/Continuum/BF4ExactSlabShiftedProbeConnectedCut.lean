/-
# Odd-cut rejection in the ORIGINAL two-replica connected form

Evaluate the existing QuaternionHaarBiadditive.connected on two original
all-spin slab integrands. Its four-moment pin retains the partition and
both endpoint means. A thin odd cut in EITHER replica kills both terms of
this connected coefficient. The filter preserves finite sums with the
original two-replica heat weights, at every nome and cutoff.

This is not yet the joint connected-selection/representation expansion.
It gives no sign of retained pairs, and permits empty odd cuts and
even-spin interactions. No response lower bound or continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut
import YMGap.Continuum.QuaternionHaarBiadditive
import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalCut
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- No replacement connected form: these are the original two slots. -/
def pairTerm (margin : Nat) (labels other : EdgeLabelling) : Q' :=
  (connected (N margin) (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))).value
    (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) labels)
    (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) other)

theorem pairTerm_pin (margin : Nat) (labels other : EdgeLabelling) :
    pairTerm margin labels other ≈
      moment margin true true labels * moment margin false false other +
        -(moment margin true false labels * moment margin false true other) := by
  have h00 : moment margin false false other ≈
      quaternionHaar (N margin) (polyMul polyOne
        (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) other)) :=
    haar_of_coeff ((RatPolyCoeffEqv.one_mul polyOne).mul (RatPolyCoeffEqv.refl _))
  have h10 : moment margin true false labels ≈
      quaternionHaar (N margin) (polyMul (lower (enlarge margin shiftedProbe))
        (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) labels)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_one _).mul (RatPolyCoeffEqv.refl _))
  have h01 : moment margin false true other ≈
      quaternionHaar (N margin) (polyMul (upper (enlarge margin shiftedProbe))
        (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) other)) :=
    haar_of_coeff ((RatPolyCoeffEqv.one_mul _).mul (RatPolyCoeffEqv.refl _))
  exact Q'.add_eqv_congr' (qmul (Q'.eqv_refl _) (Q'.eqv_symm h00))
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_symm h10) (Q'.eqv_symm h01)))

theorem pair_left_rejected (margin time : Nat) (labels other : EdgeLabelling)
    (h : cutKeep margin time labels = false) : pairTerm margin labels other ≈ 0 := by
  have h11 := cut_rejected_zero margin time true true labels h
  have h10 := cut_rejected_zero margin time true false labels h
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin labels other)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (qmul h11 (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul h10 (Q'.eqv_refl _))))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.zero_mul_eqv _)
        (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv _))) (by decide)))

theorem pair_right_rejected (margin time : Nat) (labels other : EdgeLabelling)
    (h : cutKeep margin time other = false) : pairTerm margin labels other ≈ 0 := by
  have h00 := cut_rejected_zero margin time false false other h
  have h01 := cut_rejected_zero margin time false true other h
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin labels other)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (qmul (Q'.eqv_refl _) h00)
      (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) h01)))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_zero_eqv _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _))) (by decide)))

def pairKeep (margin time : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  cutKeep margin time pair.1 && cutKeep margin time pair.2

theorem pair_rejected (margin time : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (h : pairKeep margin time pair = false) : pairTerm margin pair.1 pair.2 ≈ 0 := by
  cases hl : cutKeep margin time pair.1 with
  | false => exact pair_left_rejected margin time pair.1 pair.2 hl
  | true =>
    have hr : cutKeep margin time pair.2 = false := by simpa only [pairKeep, hl, Bool.true_and] using h
    exact pair_right_rejected margin time pair.1 pair.2 hr

/-- The actual original face-factor weights, one for each replica. -/
def weightedPairTerm (w : Q') (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  (slabParametricKPhysicalFaceFactor w K (responseExtent margin) pair.1 *
    slabParametricKPhysicalFaceFactor w K (responseExtent margin) pair.2) * pairTerm margin pair.1 pair.2

theorem weighted_pair_rejected (w : Q') (K margin time : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (h : pairKeep margin time pair = false) : weightedPairTerm w K margin pair ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pair_rejected margin time pair h)) (Q'.mul_zero_eqv _)

/-- Delete zero pairs before estimates; the SAME signed connected sum is retained. -/
theorem weighted_sum_filter (w : Q') (K margin time : Nat) (pairs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) pairs ≈
      listQSum (weightedPairTerm w K margin) (pairs.filter (pairKeep margin time)) :=
  FiniteSelectionMobius.sum_filter_zero _ _ _ (fun pair _ h => weighted_pair_rejected w K margin time pair h)

end YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pairTerm
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pairTerm_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pair_left_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pair_right_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pairKeep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.pair_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.weightedPairTerm
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.weighted_pair_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut.weighted_sum_filter
