/-
# Constructed relative Ward bound for the original odd-time plaquette

The complete weight is V*g_n*g_(n+1). Its six-face spatial derivative and
both terminal derivatives supply the relative bound, uniformly in width,
time depth, and sufficiently late character cutoff at each fixed nome.
The signed Ward correction is controlled, not deleted. This is an angular
energy bound in terms of the SAME original interacting variance, not a
transfer gap or a continuum nontriviality claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound
import YMGap.Continuum.QuaternionHaarRelativeCenteredWard

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativeCenteredWard

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks terminalMessage

/-- Per angular direction: six incident spatial faces and two terminal factors. -/
def marginalScoreCap (w : Q') : Q' := 6*relativeCap w 4096+2*relativeCap w 32

/-- No global density minimum appears in this rational coefficient. -/
def angularVarianceFactor (w : Q') : Q' := 6*(1+marginalScoreCap w*marginalScoreCap w)

theorem marginalScoreCap_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < marginalScoreCap w := by
  have h6 := Q'.mul_pos (by decide : (0 : Q') < 6)
    (relativeCap_positive hw0 (by decide : (0 : Q') ≤ 4096))
  have h2 := Q'.mul_pos (by decide : (0 : Q') < 2)
    (relativeCap_positive hw0 (by decide : (0 : Q') ≤ 32))
  exact Q'.pos_of_lt_of_le h6
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt h2))

theorem headCutoff_le_endpointRelativeCutoff (w : Q') :
    headCutoff w ≤ endpointRelativeCutoff w :=
  Nat.le_trans (headCutoff_le_relativeCutoff w 4096) (Nat.le_max_left _ _)

/-- The original middle-ratio variance controls the actual frame angular
energy. All analytic inputs are constructed from the original heat action. -/
theorem frame_energy_le_originalVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hlinear : HasQuaternionBlockDegree 0 1
      (reindexQuaternionPolynomial
        (headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
          (List.idxOf_lt_length_of_mem hl)) p)) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
      (List.idxOf_lt_length_of_mem hl)
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap p
    quaternionHaar (N width) (polyMul W (angularSquare f)) ≤
      angularVarianceFactor w * (oddMass w K width n *
        (middleRatio hw0 hw1 K width hhead (n+1) n (polyMul p p) +
          -(middleRatio hw0 hw1 K width hhead (n+1) n p *
            middleRatio hw0 hw1 K width hhead (n+1) n p))) := by
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
    (List.idxOf_lt_length_of_mem hl)
  have hidx := List.idxOf_lt_length_of_mem hl
  have hN : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le _) hidx
  have hlen : N width-1+1 = N width := Nat.sub_add_cancel hN
  have hZ : (0 : Q') < quaternionHaar (N width-1+1) (frameWeight w K width n swap) := by
    rw [hlen]
    exact frameMass_positive hw0 hw1 K width hhead n swap
  have hsupp : SupportedQuaternionBlocks (N width-1+1)
      (reindexQuaternionPolynomial swap p) := by
    rw [hlen]
    exact reindex_supported swap p
  have hrel (i j : Nat) (hi : i < 4) (hj : j < 4) :
      QuaternionHaarRelativeAngularBound.RelativeBound (N width-1+1) i j
        (frameWeight w K width n swap) (marginalScoreCap w) := by
    rw [hlen]
    exact frameRelativeBound hw0 hw1 K width n hK selected hl hs hi hj
  have h := energy_le_variance (marginalScoreCap_positive hw0) hrel hsupp hlinear hZ
  simp only [hlen] at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (frameMass_pin w K width n swap))
      (Q'.mul_eqv_congr_left _ _ _ (frameVariance_pin hw0 hw1 K width hhead n swap p hp)))))

/-- Concrete plaquette instance: physical incidence supplies linearity;
there is no unsupplied Ward-residual or variance-comparison hypothesis. -/
theorem plaquette_energy_le_originalVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : endpointRelativeCutoff w ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    {link : Z4Link} (hl : link ∈ edgesOf face)
    (hs : (baseLinks width).idxOf link ∈ activeBlocks width) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf link)
      (List.idxOf_lt_length_of_mem (incident_mem_baseLinks hf hl))
    let p := characterPolynomial (plaquette width face).scalar 1
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap p
    quaternionHaar (N width) (polyMul W (angularSquare f)) ≤
      angularVarianceFactor w * (oddMass w K width n *
        (middleRatio hw0 hw1 K width hhead (n+1) n (polyMul p p) +
          -(middleRatio hw0 hw1 K width hhead (n+1) n p *
            middleRatio hw0 hw1 K width hhead (n+1) n p))) := by
  exact frame_energy_le_originalVariance hw0 hw1 K width n hK link
    (incident_mem_baseLinks hf hl) hs
    (characterPolynomial (plaquette width face).scalar 1)
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
    (plaquette_character_head_degree width hf hl)

#print axioms marginalScoreCap_positive
#print axioms headCutoff_le_endpointRelativeCutoff
#print axioms frame_energy_le_originalVariance
#print axioms plaquette_energy_le_originalVariance

end YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
