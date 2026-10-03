/-
# The original padded-square gain as a literal full-source Stein sum

The actual source is V*g_n and the upper test is V*T(g_n*(f-c)), with
f the ORIGINAL fundamental character of the growing padded Wilson square.
The ordered word has distinct active links and perimeter 4*side, proved
from its geometry. The complete source is differentiated at each selected
link, without deleting action/terminal factors or claiming their independence.

The exact finite correction (a-1)*c*ell(A*b) remains, with a=w^(12*side).
No finite stationarity, source-independent eigenpin, favorable sign, norm
estimate, changing-family budget or continuum survival is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.SU2QuaternionProductHeatWilsonStein

namespace YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow)
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
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
  (source_edges_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
  (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup (paddedSquare_indices_nodup)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonStein
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hphysical => by
      have he := hphysical e List.mem_cons_self
      have ht : ∀ f, f ∈ es → f.link ∈ baseLinks width :=
        fun f hf => hphysical f (List.mem_cons_of_mem e hf)
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es ht]
      unfold orientedLink link
      rw [if_pos he]
      rfl

/-- Literal original source/test fold into the SAME active product map.
This is equality of the actual pairing, not a kinetic approximation. -/
theorem fullSourceDefectPair_productMap (w : Q') (K width n : Nat)
    (f : RatPoly) (c a : Q') :
    fullSourceDefectPair w K width n f c a ≈
      H width (polyMul
        (polyMul (spatialWeight w K width) (centeredMessage w K width n f c))
        (multiplicationDefect (N width) w K (activeBlocks width)
          (polyMul (spatialWeight w K width) (terminalMessage w K width n)) f a)) := by
  let V := spatialWeight w K width
  let g := terminalMessage w K width n
  let b := centeredMessage w K width n f c
  let q := polyMul V g
  let r := polyMul V b
  have hfirst : RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width) (polyMul q f))
      (transferStep w K width (polyMul g f)) := by
    rw [transferStep_eq_productMap]
    exact productMap_congr (N width) w K (activeBlocks width) (RatPolyCoeffEqv.mul_assoc V g f)
  have hsecond : productMap (N width) w K (activeBlocks width) q =
      transferStep w K width g := (transferStep_eq_productMap w K width g).symm
  have hdef : RatPolyCoeffEqv (multiplicationDefect (N width) w K (activeBlocks width) q f a)
      (polyAdd (transferStep w K width (polyMul g f))
        (polySmul (-a) (polyMul (transferStep w K width g) f))) := by
    unfold multiplicationDefect
    rw [hsecond]
    exact hfirst.add (RatPolyCoeffEqv.refl _)
  have hp : H width (polyMul r (multiplicationDefect (N width) w K (activeBlocks width) q f a)) ≈
      weightedMass w K width (polyMul b (transferStep w K width (polyMul g f))) +
        (-a)*weightedMass w K width (polyMul b (polyMul (transferStep w K width g) f)) := by
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (hdef.mul_left r)) ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.add_eqv_congr' ?_ ?_)
    · exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc V b _)
    · exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V b _)))
  exact Q'.eqv_trans _ _ _ (fullSourceDefectPair_transfer w K width n f c a) (Q'.eqv_symm hp)

/-- Computed signed Stein sum for the literal growing-square gain.
The upper test's factor TWO is the original fundamental trace factor. -/
def paddedSquareGradient (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) (c : Q') : Q' :=
  let es := (paddedSquare scale width hwidth).edges
  let f := sourceCharacter width es 1
  let q := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let r := polyMul (spatialWeight w K width) (centeredMessage w K width n f c)
  wordGradientSum (N width) w K (activeBlocks width)
    (fun e => (baseLinks width).idxOf e.link) es
    (fun e he => List.idxOf_lt_length_of_mem ((paddedSquare scale width hwidth).physical e he))
    PolyQuaternion.one q (polySmul 2 r)

/-- Exact full-source gain, with the finite moving-center correction retained.
All activity, support and word distinctness premises are proved from the
ORIGINAL padded-square geometry rather than supplied as hypotheses. -/
theorem paddedSquare_commutatorGain_source_gradient (w : Q') (K width n scale : Nat)
    (hK : 1 ≤ K) (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    commutatorGain w K width n f c a ≈ paddedSquareGradient w K width n scale hwidth c +
      (a-1)*c*centeredMeanPair w K width n f c := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let f := sourceCharacter width es 1
  let a := qpow w (12*side scale)
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  let q := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let r := polyMul (spatialWeight w K width) (centeredMessage w K width n f c)
  have hq : SupportedQuaternionBlocks (N width) q :=
    supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  have hf := sourceCharacter_supported width es 1
  have hb : SupportedQuaternionBlocks (N width) (centeredMessage w K width n f c) :=
    transferStep_supported w K width (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported hf c))
  have hr : SupportedQuaternionBlocks (N width) r :=
    supported_polyMul (spatialWeight_supported w K width) hb
  have hactive : ∀ e, e ∈ es → block e ∈ activeBlocks width := by
    intro e he
    have he' : e ∈ (square scale).edges := by
      rw [← paddedSquare_edges scale width hwidth]
      exact he
    exact source_edges_active_after_padding hwidth (square scale) e he'
  have hword : wordAt block es = sourceWord width es :=
    wordAt_sourceWord width es (paddedSquare scale width hwidth).physical
  have hlen : 3*es.length = 12*side scale := by
    dsimp only [es]
    rw [paddedSquare_edges, square_length]
    omega
  have hgeneric := multiplicationDefect_fundamental_word_source_gradient
    (N width) w K hK (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width)
    block es (paddedSquare_indices_nodup scale width hwidth) hactive q r hq hr
  rw [hword, hlen] at hgeneric
  have htrace : characterPolynomial (sourceWord width es).scalar 1 = f := by
    unfold f sourceCharacter
    rfl
  rw [htrace] at hgeneric
  have hsource : fullSourceDefectPair w K width n f c a ≈
      paddedSquareGradient w K width n scale hwidth c :=
    Q'.eqv_trans _ _ _ (fullSourceDefectPair_productMap w K width n f c a) hgeneric
  exact Q'.eqv_trans _ _ _ (commutatorGain_source_pair w K width n f c a)
    (Q'.add_eqv_congr' hsource (Q'.eqv_refl _))

/-- Specialization to the actual finite OWN mean; no mixed/even mean or
zero finite centeredMeanPair is substituted for it. -/
theorem paddedSquare_own_commutatorGain_source_gradient {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (hK : 1 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let f := sourceCharacter width loop.edges 1
    let c := ownMean hw0 hw1 K width hhead n loop
    let a := qpow w (12*side scale)
    commutatorGain w K width n f c a ≈ paddedSquareGradient w K width n scale hwidth c +
      (a-1)*c*centeredMeanPair w K width n f c :=
  paddedSquare_commutatorGain_source_gradient w K width n scale hK hwidth
    (ownMean hw0 hw1 K width hhead n (paddedSquare scale width hwidth))

end YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein.fullSourceDefectPair_productMap
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein.paddedSquareGradient
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein.paddedSquare_commutatorGain_source_gradient
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein.paddedSquare_own_commutatorGain_source_gradient
