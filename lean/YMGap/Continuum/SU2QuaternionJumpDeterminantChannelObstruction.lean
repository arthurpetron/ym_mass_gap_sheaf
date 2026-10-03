/-
# A signed channel in the original one-link jump determinant

For g=1 and b=2*x0, the determinant channel functional at the ACTUAL
fundamental representation-column leaf x0 is -1/4. Hence the universal
nonnegative-functional premise of productChannels_nome_interpolation is
false for this functional. For the degree-two source 4*x0^2-1, the ACTUAL
original product-channel sum at w=1/2,K=2 is 255/256, strictly greater
than its proposed nome-zero/nome-one interpolation 7/8. Negative
channels are favorable cross terms, not negative squared source norms.

This is a one-link Haar diagnostic. It is not a counterexample for the
particular BF4 terminal source, nor an interacting or continuum claim.
-/

import YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison
import YMGap.Continuum.SU2QuaternionRelativeHeatTransmission

namespace YMGap.Continuum.SU2QuaternionJumpDeterminantChannelObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels (channelSum)
open YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftHead)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

/-- The literal g=1,V=1 determinant functional of a Gram polynomial p. -/
def jumpDeterminantChannel (b p : RatPoly) : Q' :=
  quaternionHaar 1 (polyMul p (polyMul b b)) * quaternionHaar 1 p -
    quaternionHaar 1 (polyMul p b) * quaternionHaar 1 (polyMul p b)

/-- The actual real false-row leaf of the degree-one, column-zero tensor. -/
def fundamentalLeaf : RatPoly :=
  (polynomialColumn
    (asRepresentationQuaternion (PolyQuaternion.coordinateVariable 0)) 1 0 false).1

def fundamentalHeatChannel (w : Q') : GramChannel :=
  (coeffAt (heatKernelPacket 1 w) 1 * basisInverseWeight 1 0, fundamentalLeaf)

private theorem leaf_mem : fundamentalLeaf ∈ tensorLeaves 1
    (polynomialColumn
      (asRepresentationQuaternion (PolyQuaternion.coordinateVariable 0)) 1 0) := by
  change fundamentalLeaf ∈ tensorLeaves 0
    (polynomialColumn
      (asRepresentationQuaternion (PolyQuaternion.coordinateVariable 0)) 1 0 false) ++ _
  exact List.mem_append_left _ List.mem_cons_self

/-- The diagnostic polynomial is an actual original prefix channel. -/
theorem fundamentalLeaf_heatChannel (w : Q') :
    fundamentalHeatChannel w ∈ heatChannels 0 w 1 := by
  apply List.mem_flatMap.mpr
  refine ⟨1, by decide, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨0, by decide, ?_⟩
  exact List.mem_map.mpr ⟨fundamentalLeaf, leaf_mem, rfl⟩

/-- The same leaf carries its original Casimir tag and inverse basis weight. -/
theorem fundamentalLeaf_spectralChannel :
    (⟨c4 1, dimQ 1 * basisInverseWeight 1 0, fundamentalLeaf⟩ : SpectralChannel)
      ∈ spectralHeatChannels 0 1 := by
  apply List.mem_flatMap.mpr
  refine ⟨1, by decide, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨0, by decide, ?_⟩
  exact List.mem_map.mpr ⟨fundamentalLeaf, leaf_mem, rfl⟩

theorem fundamentalLeaf_supported : SupportedQuaternionBlocks 1 fundamentalLeaf :=
  heatChannels_supported (by decide : 0 < 1) (1 : Q') 1 _
    (fundamentalLeaf_heatChannel 1)

/-- Ratio-free centered identity, independent of the particular finite leaf. -/
theorem centered_channel_pin (b : RatPoly)
    (hmean : quaternionHaar 1 b ≈ (0 : Q')) :
    jumpDeterminantChannel b b ≈
      -(quaternionHaar 1 (polyMul b b) * quaternionHaar 1 (polyMul b b)) := by
  unfold jumpDeterminantChannel
  have h := Q'.mul_eqv_congr_left
    (quaternionHaar 1 (polyMul b (polyMul b b))) _ _ hmean
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.const 0)) (.neg (.mul (.var 1) (.var 1))))
      (.neg (.mul (.var 1) (.var 1))) (by decide)
      (fun
        | 0 => quaternionHaar 1 (polyMul b (polyMul b b))
        | _ => quaternionHaar 1 (polyMul b b)))

/-- Exact original Haar moments of the actual fundamental tensor leaf. -/
theorem fundamentalLeaf_channel_negative_pin :
    jumpDeterminantChannel (polySmul 2 (polyVar 0)) fundamentalLeaf ≈
      -(Q'.mkPos 1 4 (by decide)) := by
  decide +kernel

/-- The precise nonnegative-functional premise used by nome interpolation
cannot hold for this jump determinant, even on one supported link. -/
theorem not_channel_nonnegative :
    ¬ (∀ p, SupportedQuaternionBlocks 1 p →
      (0 : Q') ≤ jumpDeterminantChannel (polySmul 2 (polyVar 0)) p) := by
  intro h
  have hbad : (0 : Q') ≤ -(Q'.mkPos 1 4 (by decide)) :=
    Q'.le_trans' _ _ _ (h fundamentalLeaf fundamentalLeaf_supported)
      (Q'.le_of_eqv fundamentalLeaf_channel_negative_pin)
  exact (by decide : ¬ ((0 : Q') ≤ -(Q'.mkPos 1 4 (by decide)))) hbad

/-- The original second character at the coordinate quaternion. -/
def quadraticSource : RatPoly :=
  polyAdd (polySmul 4 (polyMul (polyVar 0) (polyVar 0))) (polySmul (-1) polyOne)

/-- Literal existing productChannels and channelSum, with no supplied kernel
expansion or presumed positive functional. -/
def quadraticDeterminantSum (w : Q') : Q' :=
  channelSum (productChannels 1 w 2 [0]) (jumpDeterminantChannel quadraticSource)

theorem quadraticSource_haar :
    quaternionHaar 1 quadraticSource ≈ (0 : Q') ∧
    quaternionHaar 1 (polyMul quadraticSource quadraticSource) ≈ (1 : Q') := by
  decide +kernel

/-- All three original finite-channel values, including both degenerate nomes. -/
theorem quadraticDeterminantSum_pins :
    quadraticDeterminantSum 0 ≈ (1 : Q') ∧
    quadraticDeterminantSum (Q'.mkPos 1 2 (by decide)) ≈ Q'.mkPos 255 256 (by decide) ∧
    quadraticDeterminantSum 1 ≈ (0 : Q') := by
  decide +kernel

/-- Omitting hF from productChannels_nome_interpolation gives a false
conclusion on the original one-link, cutoff-two channel list. -/
theorem quadratic_nome_interpolation_fails :
    (1 - qpow (Q'.mkPos 1 2 (by decide)) 3) * quadraticDeterminantSum 0 +
      qpow (Q'.mkPos 1 2 (by decide)) 3 * quadraticDeterminantSum 1 <
      quadraticDeterminantSum (Q'.mkPos 1 2 (by decide)) := by
  decide +kernel

#print axioms fundamentalLeaf_heatChannel
#print axioms fundamentalLeaf_spectralChannel
#print axioms fundamentalLeaf_supported
#print axioms centered_channel_pin
#print axioms fundamentalLeaf_channel_negative_pin
#print axioms not_channel_nonnegative
#print axioms quadraticSource_haar
#print axioms quadraticDeterminantSum_pins
#print axioms quadratic_nome_interpolation_fails

end YMGap.Continuum.SU2QuaternionJumpDeterminantChannelObstruction
