/-
# Word-local source cost for the ORIGINAL growing-square filtered gain

Only the square's lower word links are conditionally centered by hybridSweep.
Every other lower coordinate, the full original heat kernel, q=V*g_n,
the output action V, centered b and finite OWN mean stay unchanged. The local
cost is proved no larger than the existing full source loss. The covariance
cost keeps its negative spin-two moment and literal mean residue.

This does not control either cost by the interacting OWN variance or lag-one
reserve, prove a gain sign, or produce a changing-family survival budget.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance
import YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance

namespace YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainLocalCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (link orientedLink spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt activeBlocks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (source_edges_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
  (fullSourceDefectPair centeredMeanPair commutatorGain_source_pair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup (paddedSquare_indices_nodup)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein (fullSourceDefectPair_productMap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect (multiplicationDefect)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance (wordCovarianceRate)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted_supported)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance
  (originalSourceHeatLoss centeredMessageSquare centeredMessageCharacterSquare)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

/-- Actual full-joint heat loss after sweeping ONLY this square's word slots.
The retained upper action is V and the signed source is the original V*g_n. -/
def originalLocalSourceHeatLoss (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  localSourceLoss (N width) w K (activeBlocks width)
    ((paddedSquare scale width hwidth).edges.map
      (fun e => (baseLinks width).idxOf e.link))
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))
    (spatialWeight w K width)

private theorem active_word (width scale : Nat) (hwidth : side scale < width) :
    ∀ e, e ∈ (paddedSquare scale width hwidth).edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width := by
  intro e he
  have he' : e ∈ (square scale).edges := by
    rw [← paddedSquare_edges scale width hwidth]
    exact he
  exact source_edges_active_after_padding hwidth (square scale) e he'

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link), (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hp => by
      have he := hp e List.mem_cons_self
      change PolyQuaternion.mul
        (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
        (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es (fun f hf => hp f (List.mem_cons_of_mem e hf))]
      unfold orientedLink link
      rw [if_pos he]
      rfl

/-- Actual word localization improves the existing SAME weighted full source cost. -/
theorem originalLocalSourceHeatLoss_le_full {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    originalLocalSourceHeatLoss w K width n scale hwidth ≤ originalSourceHeatLoss w K width n := by
  let selected := (paddedSquare scale width hwidth).edges.map
    (fun e => (baseLinks width).idxOf e.link)
  have hs : ∀ i, i ∈ selected → i ∈ activeBlocks width := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi
    exact active_word width scale hwidth e he
  have hV := spatialWeight_supported w K width
  have h := localSourceLoss_le_fullSourceLoss (N width) hw0 hw1 K hhead
    (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width)
    selected (paddedSquare_indices_nodup scale width hwidth) hs
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))
    (supported_polyMul hV (terminalMessage_supported w K width n))
    (spatialWeight w K width) hV
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead)
  simpa only [originalLocalSourceHeatLoss, originalSourceHeatLoss, weightedMass, selected] using h

/-- Literal full-source defect, with original square geometry and word-only loss.
The complete favorable moment is retained; no concentration hypothesis is input. -/
theorem paddedSquare_fullSourceDefectPair_local_retained_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a ≤
      originalLocalSourceHeatLoss w K width n scale hwidth *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let f := sourceCharacter width es 1
  let a := qpow w (12*side scale)
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  let V := spatialWeight w K width
  let q := polyMul V (terminalMessage w K width n)
  let b := centeredMessage w K width n f c
  let C := multiplicationDefect (N width) w K (activeBlocks width) q f a
  have hV : SupportedQuaternionBlocks (N width) V := spatialWeight_supported w K width
  have hq := supported_polyMul hV (terminalMessage_supported w K width n)
  have hb : SupportedQuaternionBlocks (N width) b :=
    transferStep_supported w K width (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported (sourceCharacter_supported width es 1) c))
  have hword : wordAt block es = sourceWord width es :=
    wordAt_sourceWord width es (paddedSquare scale width hwidth).physical
  have htrace : characterPolynomial (sourceWord width es).scalar 1 = f := by
    unfold f sourceCharacter
    rfl
  have hlen3 : 3*es.length = 12*side scale := by
    dsimp only [es]
    rw [paddedSquare_edges, square_length]
    omega
  have hlen8 : 8*es.length = 32*side scale := by
    dsimp only [es]
    rw [paddedSquare_edges, square_length]
    omega
  have hgeneric := fundamental_word_local_covariance_pair_retained_bound
    (N width) hw0 hw1 K hhead htwo (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) block es
    (paddedSquare_indices_nodup scale width hwidth) (active_word width scale hwidth) q hq V hV
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead) b hb
  unfold wordCovarianceRate at hgeneric
  rw [hword, htrace, hlen3, hlen8] at hgeneric
  have hpair : fullSourceDefectPair w K width n f c a ≈ H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (fullSourceDefectPair_productMap w K width n f c a)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V b C))
  have hsquare : fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a ≈
      H width (polyMul V (polyMul b C)) * H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpair)
      (Q'.mul_eqv_congr_left _ _ _ hpair)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare) (by
    simpa only [C, a, b, q, V, f, es, block, centeredMessageSquare,
      centeredMessageCharacterSquare, originalLocalSourceHeatLoss, weightedMass] using hgeneric)

attribute [local irreducible] ownMean originalLocalSourceHeatLoss

set_option maxHeartbeats 1000000 in
private theorem commutatorGain_local_retained_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue)*(commutatorGain w K width n f c a-residue) ≤
      originalLocalSourceHeatLoss w K width n scale hwidth *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := qpow w (12*side scale)
  let d := qpow w (32*side scale)
  let residue := (a-1)*c*centeredMeanPair w K width n f c
  have hg : commutatorGain w K width n f c a ≈
      fullSourceDefectPair w K width n f c a + residue :=
    commutatorGain_source_pair w K width n f c a
  have hsub : commutatorGain w K width n f c a-residue ≈ fullSourceDefectPair w K width n f c a :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hg (Q'.eqv_refl (-residue)))
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
        (.var 0) (by decide) (fun | 0 => fullSourceDefectPair w K width n f c a | _ => residue))
  have hsquare : (commutatorGain w K width n f c a-residue)*(commutatorGain w K width n f c a-residue) ≈
      fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hsub)
      (Q'.mul_eqv_congr_left _ _ _ hsub)
  have hbound : fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a ≤
      originalLocalSourceHeatLoss w K width n scale hwidth *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) :=
    (paddedSquare_fullSourceDefectPair_local_retained_bound hw0 hw1 K width hhead htwo n scale hwidth c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare) hbound

/-- SAME finite OWN center and complete gain-minus-mean-residue. The retained
source cost is NOT identified with OWN variance or a lag-one reserve. -/
theorem paddedSquare_own_commutatorGain_local_retained_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let f := sourceCharacter width loop.edges 1
    let c := ownMean hw0 hw1 K width hhead n loop
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue)*(commutatorGain w K width n f c a-residue) ≤
      originalLocalSourceHeatLoss w K width n scale hwidth *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) :=
  commutatorGain_local_retained_bound hw0 hw1 K width hhead htwo n scale hwidth
    (ownMean hw0 hw1 K width hhead n (paddedSquare scale width hwidth))

#print axioms originalLocalSourceHeatLoss
#print axioms originalLocalSourceHeatLoss_le_full
#print axioms paddedSquare_fullSourceDefectPair_local_retained_bound
#print axioms paddedSquare_own_commutatorGain_local_retained_bound

end YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainLocalCovariance
