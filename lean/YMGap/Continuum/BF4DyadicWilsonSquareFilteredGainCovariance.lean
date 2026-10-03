/-
# Whole-word covariance cost of the ORIGINAL growing-square filtered gain

The complete source is q=V*g_n, the centered test is b=T(g_n*(f-c)),
and V is retained as the original certified output action. Whole-word
conditional covariance pays (1-w^(32*side))*ell(b^2) times the ACTUAL
conditional source loss. No perimeter-squared telescope or raw test norm
is substituted. The finite mean residue (a-1)*c*ell(A*b) remains literal.
The retained version also keeps the negative original moment
  -(w^(12*side)^2-w^(32*side))*ell(b^2*f^2).
No concentration near f^2=4 is asserted or assumed.

The source loss is NOT the interacting OWN variance or lag-one reserve.
Its useful relative control and a changing-family signed gain budget remain
open. No stationarity, favorable sign or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein
import YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder

namespace YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
  (source_edges_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
  (fullSourceDefectPair centeredMeanPair commutatorGain_source_pair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup (paddedSquare_indices_nodup)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein
  (fullSourceDefectPair_productMap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect (multiplicationDefect)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

/-- Original terminal source loss, weighted by V ONCE at the output.
This is not raw Haar heat loss and not an interacting observable variance. -/
def originalSourceHeatLoss (w : Q') (K width n : Nat) : Q' :=
  weightedMass w K width (fullSourceLoss (N width) w K (activeBlocks width)
    (polyMul (spatialWeight w K width) (terminalMessage w K width n)))

/-- Literal centered-message square on the SAME original middle carrier. -/
def centeredMessageSquare (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : Q' :=
  let b := centeredMessage w K width n f c
  weightedMass w K width (polyMul b b)

/-- The exact original moment in the favorable spin-one/spin-two correction.
The SAME b, f and spatial action occur, without a radial concentration input. -/
def centeredMessageCharacterSquare (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : Q' :=
  let b := centeredMessage w K width n f c
  weightedMass w K width (polyMul (polyMul b b) (polyMul f f))

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

private theorem subtract_residue (gain defect residue : Q')
    (h : gain ≈ defect+residue) : gain-residue ≈ defect :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h (Q'.eqv_refl (-residue)))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => defect | _ => residue))

/-- The full ORIGINAL source defect has a whole-word covariance cost.
Its geometry, active links and action certificate are constructed here;
no source independence, covariance conclusion or variance comparison is input. -/
theorem paddedSquare_fullSourceDefectPair_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a ≤
      (1-qpow w (32*side scale)) *
        (centeredMessageSquare w K width n f c * originalSourceHeatLoss w K width n) := by
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
  have hq : SupportedQuaternionBlocks (N width) q :=
    supported_polyMul hV (terminalMessage_supported w K width n)
  have hf := sourceCharacter_supported width es 1
  have hb : SupportedQuaternionBlocks (N width) b :=
    transferStep_supported w K width (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported hf c))
  let PV := spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead
  have hactive : ∀ e, e ∈ es → block e ∈ activeBlocks width := by
    intro e he
    have he' : e ∈ (square scale).edges := by
      rw [← paddedSquare_edges scale width hwidth]
      exact he
    exact source_edges_active_after_padding hwidth (square scale) e he'
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
  have hgeneric := fundamental_word_covariance_pair_bound
    (N width) hw0 hw1 K hhead htwo (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) block es
    (paddedSquare_indices_nodup scale width hwidth) hactive q hq V hV PV b hb
  unfold wordCovarianceRate at hgeneric
  rw [hword, htrace, hlen3, hlen8] at hgeneric
  have hpair : fullSourceDefectPair w K width n f c a ≈
      H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (fullSourceDefectPair_productMap w K width n f c a)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V b C))
  have hsquare : fullSourceDefectPair w K width n f c a *
      fullSourceDefectPair w K width n f c a ≈
      H width (polyMul V (polyMul b C)) * H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpair)
      (Q'.mul_eqv_congr_left _ _ _ hpair)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare) (by
    simpa only [C, a, b, q, V, f, es, centeredMessageSquare,
      originalSourceHeatLoss, weightedMass] using hgeneric)

/-- The gain cost retains its literal finite moving-mean residue inside
the square. In particular this theorem does NOT assert that G is positive. -/
theorem paddedSquare_commutatorGain_covariance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue) *
        (commutatorGain w K width n f c a-residue) ≤
      (1-qpow w (32*side scale)) *
        (centeredMessageSquare w K width n f c * originalSourceHeatLoss w K width n) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := qpow w (12*side scale)
  let residue := (a-1)*c*centeredMeanPair w K width n f c
  have h := subtract_residue _ _ residue (commutatorGain_source_pair w K width n f c a)
  have hsq : (commutatorGain w K width n f c a-residue) *
      (commutatorGain w K width n f c a-residue) ≈
      fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
    (paddedSquare_fullSourceDefectPair_square_bound hw0 hw1 K width hhead htwo n scale hwidth c)

/-- The SAME actual finite OWN center is substituted, without changing the
source, output action, depth, square or any normalization. -/
theorem paddedSquare_own_commutatorGain_covariance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let f := sourceCharacter width loop.edges 1
    let c := ownMean hw0 hw1 K width hhead n loop
    let a := qpow w (12*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue) *
        (commutatorGain w K width n f c a-residue) ≤
      (1-qpow w (32*side scale)) *
        (centeredMessageSquare w K width n f c * originalSourceHeatLoss w K width n) :=
  paddedSquare_commutatorGain_covariance_bound hw0 hw1 K width hhead htwo n scale hwidth
    (ownMean hw0 hw1 K width hhead n (paddedSquare scale width hwidth))

/-- Retain the complete negative moment in the ACTUAL square covariance
cost. Neither radial concentration nor OWN-variance comparison is input. -/
theorem paddedSquare_fullSourceDefectPair_retained_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a ≤
      originalSourceHeatLoss w K width n *
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
  have hq : SupportedQuaternionBlocks (N width) q :=
    supported_polyMul hV (terminalMessage_supported w K width n)
  have hf := sourceCharacter_supported width es 1
  have hb : SupportedQuaternionBlocks (N width) b :=
    transferStep_supported w K width (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported hf c))
  let PV := spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead
  have hactive : ∀ e, e ∈ es → block e ∈ activeBlocks width := by
    intro e he
    have he' : e ∈ (square scale).edges := by
      rw [← paddedSquare_edges scale width hwidth]
      exact he
    exact source_edges_active_after_padding hwidth (square scale) e he'
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
  have hgeneric := fundamental_word_covariance_pair_retained_bound
    (N width) hw0 hw1 K hhead htwo (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) block es
    (paddedSquare_indices_nodup scale width hwidth) hactive q hq V hV PV b hb
  unfold wordCovarianceRate at hgeneric
  rw [hword, htrace, hlen3, hlen8] at hgeneric
  have hpair : fullSourceDefectPair w K width n f c a ≈
      H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (fullSourceDefectPair_productMap w K width n f c a)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V b C))
  have hsquare : fullSourceDefectPair w K width n f c a *
      fullSourceDefectPair w K width n f c a ≈
      H width (polyMul V (polyMul b C)) * H width (polyMul V (polyMul b C)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpair)
      (Q'.mul_eqv_congr_left _ _ _ hpair)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare) (by
    simpa only [C, a, b, q, V, f, es, centeredMessageSquare,
      centeredMessageCharacterSquare, originalSourceHeatLoss, weightedMass] using hgeneric)

/-- Complete retained moment bound on G minus the literal moving-mean
residue. The favorable original moment is NOT replaced by a cap. -/
theorem paddedSquare_commutatorGain_retained_covariance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue) *
        (commutatorGain w K width n f c a-residue) ≤
      originalSourceHeatLoss w K width n *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := qpow w (12*side scale)
  let residue := (a-1)*c*centeredMeanPair w K width n f c
  have h := subtract_residue _ _ residue (commutatorGain_source_pair w K width n f c a)
  have hsq : (commutatorGain w K width n f c a-residue) *
      (commutatorGain w K width n f c a-residue) ≈
      fullSourceDefectPair w K width n f c a * fullSourceDefectPair w K width n f c a :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
    (paddedSquare_fullSourceDefectPair_retained_square_bound hw0 hw1 K width hhead htwo n scale hwidth c)

/-- Retained bound at the actual finite OWN center of this square. -/
theorem paddedSquare_own_commutatorGain_retained_covariance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let f := sourceCharacter width loop.edges 1
    let c := ownMean hw0 hw1 K width hhead n loop
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue) *
        (commutatorGain w K width n f c a-residue) ≤
      originalSourceHeatLoss w K width n *
        ((1-d)*centeredMessageSquare w K width n f c -
          (a*a-d)*centeredMessageCharacterSquare w K width n f c) :=
  paddedSquare_commutatorGain_retained_covariance_bound hw0 hw1 K width hhead htwo n scale hwidth
    (ownMean hw0 hw1 K width hhead n (paddedSquare scale width hwidth))


end YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.originalSourceHeatLoss
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.centeredMessageSquare
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.centeredMessageCharacterSquare
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_fullSourceDefectPair_square_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_commutatorGain_covariance_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_own_commutatorGain_covariance_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_fullSourceDefectPair_retained_square_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_commutatorGain_retained_covariance_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance.paddedSquare_own_commutatorGain_retained_covariance_bound
