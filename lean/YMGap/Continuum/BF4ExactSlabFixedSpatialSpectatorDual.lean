/-
# Literal plaquette dual with a link-independent spectator

The original selected-link product heat sends the inverse-heat plaquette
dual multiplied by a link-independent spectator to the centered source
multiplied by the transformed spectator.  Erasing one selected link leaves
the spectator image unchanged under supported Haar tests and gives a
literal output independent of that link.  These are kinetic identities,
not interacting endpoint or uniform-gap bounds.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_nodup activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive (source dualTest)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost (inverseRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm not_mem_erase mem_of_mem_erase)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem power_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (power_positive hw k) hw

/-- A selected independent edge can be omitted from the full product map.
The erased output is literally independent of that edge, so it can serve
as a Haar spectator without asserting that the un-erased representative
is syntactically independent. -/
theorem active_erased_spectator (width : Nat) (w : Q') (K : Nat)
    (i : Nat) (hi : i ∈ activeBlocks width)
    (A : RatPoly) (hA : SupportedQuaternionBlocks (N width) A)
    (hAI : QuaternionBlockIndependent i A) :
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) A)
      (productMap (N width) w K (eraseIndex i (activeBlocks width)) A) ∧
    QuaternionBlockIndependent i
      (productMap (N width) w K (eraseIndex i (activeBlocks width)) A) := by
  let rest := eraseIndex i (activeBlocks width)
  have hnot : i ∉ rest := not_mem_erase i (activeBlocks_nodup width)
  have hlt : i < N width := activeBlocks_lt width i hi
  have hrest : ∀ j, j ∈ rest → j < N width :=
    fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)
  have hp : (activeBlocks width).Perm (i::rest) := select_perm i hi
  have hcoeff : RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width) A)
      (productMap (N width) w K (i::rest) A) :=
    partialHaarHeads_congr (N width)
      ((polynomialProduct_perm _ hp).mul_right A)
  exact ⟨(SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier hcoeff)).trans
      (productMap_cons_input_independent (N width) w K i rest
        hlt hnot hrest A hA hAI),
    productMap_independent_of_not_mem (N width) w K rest hrest i hlt hnot A hA⟩

/-- Exact inverse-heat dual preimage with the entire transformed spectator.
The four active face links are needed for the plaquette eigenfactor; the
spectator is only required to be independent of those same links. -/
theorem plaquette_spectator_dual_preimage {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : 1 ≤ K)
    (A : RatPoly) (hA : SupportedQuaternionBlocks (N width) A)
    (hAI : ∀ l, l ∈ edgesOf face →
      QuaternionBlockIndependent ((baseLinks width).idxOf l) A)
    (m : Q') :
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width)
        (polyMul (dualTest hw0 width face m) A))
      (polyMul (source width face m)
        (productMap (N width) w K (activeBlocks width) A)) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let PA := productMap (N width) w K (activeBlocks width) A
  let r := inverseRate hw0
  have hr : r * qpow w 12 ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv (qpow w 12) (power_positive hw0 12))
  have heigen : SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) (polySmul r (polyMul f A)))
      (polySmul 1 (polyMul f PA)) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_smul (N width) w K (activeBlocks width) r (polyMul f A)))).trans
      (((plaquette_spectator_kinetic width face hf hactive w K hK A hA hAI).smul r).trans
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
          ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
            (RatPolyCoeffEqv.smul_coefficient hr (polyMul f PA))))))
  have hother : SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) (polySmul (-m) A))
      (polySmul (-m) PA) :=
    SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_smul (N width) w K (activeBlocks width) (-m) A))
  have hdual : RatPolyCoeffEqv (polyMul (dualTest hw0 width face m) A)
      (polyAdd (polySmul r (polyMul f A)) (polySmul (-m) A)) := by
    have hd : dualTest hw0 width face m =
        polyAdd (polySmul r f) (polySmul (-m) polyOne) := rfl
    rw [hd, polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.polyMul_smul_left r f A).add
      ((RatPolyCoeffEqv.polyMul_smul_left (-m) polyOne A).trans
        ((RatPolyCoeffEqv.one_mul A).smul (-m)))
  have hsource : RatPolyCoeffEqv
      (polyMul (source width face m) PA)
      (polyAdd (polySmul 1 (polyMul f PA)) (polySmul (-m) PA)) := by
    have hs : source width face m =
        polyAdd (polySmul 1 f) (polySmul (-m) polyOne) := rfl
    rw [hs, polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.polyMul_smul_left 1 f PA).add
      ((RatPolyCoeffEqv.polyMul_smul_left (-m) polyOne PA).trans
        ((RatPolyCoeffEqv.one_mul PA).smul (-m)))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_congr (N width) w K (activeBlocks width) hdual))).trans
    ((SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_add (N width) w K (activeBlocks width)
        (polySmul r (polyMul f A)) (polySmul (-m) A)))).trans
      ((heigen.add hother).trans
        (SupportedHaarEqv.of_carrier
          (RatPolyCoeffEqv.haarCarrier hsource.symm))))

#print axioms active_erased_spectator
#print axioms plaquette_spectator_dual_preimage

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
