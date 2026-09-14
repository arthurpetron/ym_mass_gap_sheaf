/-
# Original signed pairs have explicit parity and higher-label activities

The SAME heat-weighted connected pair is bounded by 8*oddRate^B*higherRate^H,
where B and H are computed on its original physical labels. The existing
nome is unchanged. Higher-label geometric tails retain their actual
near-one denominator; neither a spatial count nor a full response floor
is obtained from these per-pair and fixed-parity bounds alone.
-/

import YMGap.Continuum.SU2FiniteParityHigherProduct
import YMGap.Continuum.BF4ExactSlabSharpCharacterWeights

namespace YMGap.Continuum.BF4ExactSlabParityHigherPairBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabSharpCharacterWeights
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def pairParity (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  parityCount pair.1 (slabPhysicalFaceEdges (responseExtent margin)) +
    parityCount pair.2 (slabPhysicalFaceEdges (responseExtent margin))

/-- Sum of quotient units, not merely the number of faces with label at least two. -/
def pairHigher (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  higherCount pair.1 (slabPhysicalFaceEdges (responseExtent margin)) +
    higherCount pair.2 (slabPhysicalFaceEdges (responseExtent margin))

theorem weightedPairTerm_parity_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hb : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → pair.1 id ≤ K ∧ pair.2 id ≤ K) :
    Q'.abs (weightedPairTerm w K margin pair) ≤
      8 * (qpow (oddRate w) (pairParity margin pair) * qpow (higherRate w) (pairHigher margin pair)) := by
  have hp := pairedProduct_pin w pair.1 pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  have he := Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv 8
    (pairDimension margin pair * pairDimension margin pair) (qpow w (pairPower margin pair)))
    (Q'.mul_eqv_congr_left 8 _ _ (Q'.eqv_symm hp))
  exact Q'.le_trans' _ _ _ (weightedPairTerm_bound w hw0 K margin pair hb)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ 8
        (pairedProduct_bound hw0 hw1 pair.1 pair.2 (slabPhysicalFaceEdges (responseExtent margin))) (by decide)))

theorem existingNome_rates :
    oddRate nome ≈ Q'.invSucc (2^28-1) ∧
      higherRate nome ≈ 9*Q'.invSucc (2^80-1) := by decide

theorem existingNome_higher_guard :
    (0 : Q') < higherRate nome ∧ higherRate nome < HalfPow.half := by decide

/-- At the existing physical nome, every finite higher-label tail has the explicit scalar cap. -/
theorem existingNome_higherTail_bound (bit : Nat) (hb : bit ≤ 1) (start count : Nat) :
    finSum (fun i => heatWeight nome (2*(start+i)+bit)) count ≤ higherTailBound nome bit start :=
  higherTail_bound (by decide) (by decide) existingNome_higher_guard.1 (by decide) bit hb start count

/-- Keep the near-one higher-label sum factor, rather than paying a factor two per face. -/
theorem existingNome_higher_factor : higherTailBound nome 0 0 ≤ 1 + 2*higherRate nome := by decide

end YMGap.Continuum.BF4ExactSlabParityHigherPairBound

#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.pairParity
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.pairHigher
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.weightedPairTerm_parity_bound
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.existingNome_rates
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.existingNome_higher_guard
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.existingNome_higherTail_bound
#print axioms YMGap.Continuum.BF4ExactSlabParityHigherPairBound.existingNome_higher_factor
