/-
# Exact signed leading term and relative remainder of the ORIGINAL numerator

The numerator is w^36 * (A + w*B(w)), with A and B computed on the same
retained original replica carrier. A contains precisely power-36 terms;
the existing minimum-power theorem forces those labels to be fundamental
on exactly twelve occupied faces. A's value/sign and a useful bound on B
remain open. In particular this is not a positive response certificate.
-/

import YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower

namespace YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

def leadingPair (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  if pairPower margin pair = 36 then signedAmplitude margin pair else 0

def higherPairResidual (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  if pairPower margin pair = 36 then 0
  else signedAmplitude margin pair * qpow w (pairPower margin pair - 37)

theorem pair_residual_split (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hp : 36 ≤ pairPower margin pair) :
    pairResidual w margin pair ≈ leadingPair margin pair + w * higherPairResidual w margin pair := by
  unfold pairResidual leadingPair higherPairResidual
  by_cases he : pairPower margin pair = 36
  · rw [if_pos he, if_pos he, he, Nat.sub_self, qpow_zero]
    refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm ?_)
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_zero_eqv w))
      (Q'.eqv_of_eq (Q'.add_zero' _))
  · rw [if_neg he, if_neg he, Q'.zero_add']
    have hs : pairPower margin pair - 36 = (pairPower margin pair - 37) + 1 := by omega
    rw [hs]
    change signedAmplitude margin pair * (qpow w (pairPower margin pair - 37) * w) ≈ _
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)

def leadingCoefficient (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (leadingPair margin)
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))

def higherResidual (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (higherPairResidual w margin)
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))

private theorem sum_split {A : Type} (w : Q') (f a b : A → Q') (xs : List A)
    (h : ∀ x, x ∈ xs → f x ≈ a x + w*b x) :
    listQSum f xs ≈ listQSum a xs + w * listQSum b xs :=
  Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ xs h)
    (Q'.eqv_trans _ _ _ (listQSum_add a (fun x => w*b x) xs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (listQSum_mul_left w b xs)))

theorem residual_split (w : Q') (K margin time : Nat) :
    numeratorResidual w K margin time ≈ leadingCoefficient K margin time + w * higherResidual w K margin time := by
  apply sum_split
  intro ids hs
  apply sum_split
  intro pair hp
  exact pair_residual_split w margin pair (retained_power_minimum hs hp)

theorem original_leading_remainder (w : Q') (K margin time : Nat) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
        qpow w 36 * (leadingCoefficient K margin time + w * higherResidual w K margin time) :=
  Q'.eqv_trans _ _ _ (original_numerator_factorization w K margin time)
    (Q'.mul_eqv_congr_left _ _ _ (residual_split w K margin time))

theorem residual_at_zero (K margin time : Nat) :
    numeratorResidual 0 K margin time ≈ leadingCoefficient K margin time :=
  Q'.eqv_trans _ _ _ (residual_split 0 K margin time)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.zero_mul_eqv _))
      (Q'.eqv_of_eq (Q'.add_zero' _)))

end YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder

#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.leadingPair
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.higherPairResidual
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.pair_residual_split
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.leadingCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.higherResidual
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.residual_split
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.original_leading_remainder
#print axioms YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder.residual_at_zero
