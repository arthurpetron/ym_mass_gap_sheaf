/-
# The actual middle-slice pairing is an original selected-chain expectation

The m-th chronological slice has its literal original spatial placement.
Under one common temporal sweep, its signed physical face probe and the
complete selected chain become the existing compact middle pairing. The
spatial factor at the insertion occurs exactly once, inside weightedMass.

At every retained cutoff the positive two-message denominator is the SAME
original partition. Its computed reciprocal therefore gives the original
finiteValue, not a separately normalized message law. Width, nome, cutoff,
and both finite time lengths remain explicit. This finite geometric pin
constructs no bulk limit, stationary law, reflected OS state or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- Every coordinate of the m-th slice has its original placement, with
all n later slices still present in the same chronological carrier. -/
theorem middle_block {width start m n extent i : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent) (hi : i < N width) :
    (embedding (m+n) hw ht).block (m*(N width)+i) =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start+m ≤ extent by omega)).block i := by
  induction m generalizing start with
  | zero =>
      have ht0 : start+n ≤ extent := by simpa only [Nat.zero_add] using ht
      simpa only [BlockEmbedding.block, embedding,
        BF4ExactSlabFixedSpatialSliceCarrier.embedding,
        Nat.zero_add, Nat.add_zero, Nat.zero_mul] using
        (head_block (steps := n) hw ht0 hi)
  | succ m ih =>
      have hcount : m+1+n = (m+n)+1 := by omega
      have hs : start+1+(m+n) ≤ extent := by omega
      have h := (tail_block (steps := m+n) hw
        (show start+((m+n)+1) ≤ extent by omega) (m*(N width)+i)).trans
        (ih (start := start+1) hs)
      have htime : start+1+m = start+(m+1) := by omega
      have hindex : (m+1)*(N width)+i = N width+(m*(N width)+i) := by
        simp only [Nat.succ_mul]
        omega
      simpa only [BlockEmbedding.block, embedding,
        BF4ExactSlabFixedSpatialSliceCarrier.embedding,
        hcount, htime, hindex] using h

/-- Exact polynomial placement at the middle slice, including term order. -/
theorem middle_polynomial_pin {width start m n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    (embedding (m+n) hw ht).polynomial (liftBoundary (m*(N width)) p) =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start+m ≤ extent by omega)).polynomial p := by
  apply BlockEmbedding.polynomial_liftBoundary
  · have h := Nat.mul_le_mul_right (N width) (show m+1 ≤ m+n+1 by omega)
    simpa only [Nat.add_mul, Nat.one_mul] using h
  · exact fun _ hi => middle_block hw ht hi
  · exact hp

/-- Swept original-chain pairing with an arbitrary supported middle
polynomial. No face, sign or cutoff positivity premise is used here. -/
theorem swept_middle_pairing {width start m n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (B extent)
        (polyMul
          ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
            (show start+m ≤ extent by omega)).polynomial p)
          (ambientChain w K extent width start (m+n))) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width m) p)
          (terminalMessage w K width n)) := by
  let E := embedding (m+n) hw ht
  let M := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
    (show start+m ≤ extent by omega)
  let U := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  let c := chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+n) polyOne
  let lifted := liftBoundary (m*(N width)) p
  have hunit : PaddedPolynomialCoeffEqv (B extent) (U.polynomial polyOne) polyOne :=
    .of_prefix U.polynomial_one_prefix
  have hchain : PaddedPolynomialCoeffEqv (B extent) (E.polynomial c)
      (ambientChain w K extent width start (m+n)) :=
    (chain_pin hw ht w K polyOne (supported_one (N width))).trans
      (((PaddedPolynomialCoeffEqv.refl _ _).mul hunit).trans
        (.of_coeff (RatPolyCoeffEqv.mul_one _)))
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul lifted c))
      (polyMul (M.polynomial p) (ambientChain w K extent width start (m+n))) := by
    rw [BlockEmbedding.polynomial_mul, middle_polynomial_pin hw ht p hp]
    exact (PaddedPolynomialCoeffEqv.refl _ _).mul hchain
  have hlift : SupportedQuaternionBlocks ((m+n+1)*(N width)) lifted :=
    support_mono (lift_supported hp (m*(N width))) (by
      simp only [Nat.add_mul, Nat.one_mul]
      omega)
  have hsource : SupportedQuaternionBlocks ((m+n+1)*(N width)) (polyMul lifted c) :=
    supported_polyMul hlift
      (chain_supported (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) (m+n) (supported_one (N width)))
  have hambient := supported_polyMul (M.polynomial_supported p)
    (ambientChain_supported w K extent width start (m+n))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hpin.haar (E.polynomial_supported _) hambient))
    (Q'.eqv_trans _ _ _ (E.haar _ hsource) (middle_pairing w K width m n hp))

/-- A physical signed probe at start+m is integrated with the SAME
original selected action and the SAME heat cutoff, with one middle V. -/
theorem original_middle_pairing {width start m n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent) (w : Q') (K : Nat)
    (fs : List FaceFactor) (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    quaternionHaar (B extent)
        (polyMul (sweptProduct extent 0 (placeProbes (start+m) fs))
          (originalChainAction w K extent width start (m+n))) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width m) (sourceProbe width fs))
          (terminalMessage w K width n)) := by
  have hm : start+m ≤ extent := by omega
  let M := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw hm
  let p := sourceProbe width fs
  let probes := placeProbes (start+m) fs
  have hprobe := sourceProbe_pin hw hm fs hfs
  have ha := ambientChain_supported w K extent width start (m+n)
  have hprobes := product_supported (sweptCharacter extent 0)
    (swept_character_supported extent 0) probes
  have hreplace := (hprobe.symm.mul (.refl _ (ambientChain w K extent width start (m+n)))).haar
    (supported_polyMul hprobes ha) (supported_polyMul (M.polynomial_supported p) ha)
  have horiginal := original_chain_pairing w K extent width start (m+n) probes
    (placeProbes_physical hw hm fs hfs) (placeProbes_spatial (start+m) fs hfs)
  exact Q'.eqv_trans _ _ _ horiginal (Q'.eqv_trans _ _ _ hreplace
    (swept_middle_pairing hw ht w K p (sourceProbe_supported width fs)))

/-- The compact middle scalar is the existing original insertion numerator,
not a new observable or a chain with its joining weight removed. -/
theorem middleNumerator_pin {width start m n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent) (w : Q') (K : Nat)
    (fs : List FaceFactor) (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width m) (sourceProbe width fs))
          (terminalMessage w K width n)) ≈
      numerator w (B extent) extent (chainIds extent width start (m+n))
        (sweptProduct extent 0 (placeProbes (start+m) fs)) K :=
  Q'.eqv_symm (original_middle_pairing hw ht w K fs hfs)

private theorem reciprocal_unique (z r s : Q') (hr : z*r ≈ 1) (hs : z*s ≈ 1) : r ≈ s :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv r))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ (Q'.eqv_symm hs))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
          (fun | 0 => r | 1 => z | _ => s))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ s hr) (Q'.one_mul_eqv s))))

/-- The actual interior ratio has the original finiteValue normalization.
Its denominator positivity is constructed from the existing actual terminal
messages; no additional positivity or Perron hypothesis is supplied. -/
theorem middleRatio_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m n extent : Nat} (hw : width ≤ extent) (ht : start+(m+n) ≤ extent)
    (fs : List FaceFactor) (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m n (sourceProbe width fs) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+n))
        (fun _ hi => chainIds_physical hi)
        (sweptProduct extent 0 (placeProbes (start+m) fs)) stage := by
  let K := headCutoff w+stage
  let z := weightedMass w K width
    (polyMul (terminalMessage w K width m) (terminalMessage w K width n))
  have hz : (0 : Q') < z := terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) m n
  let r := Q'.recipPos z hz
  let s := reciprocalTerm w hw0 hw1 extent (chainIds extent width start (m+n))
    (fun _ hi => chainIds_physical hi) stage
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hz
  have hpartition : z ≈ compactPartition w K width (m+n) :=
    Q'.eqv_trans _ _ _ (terminalPair_total w K width m n)
      (weightedMass_iterate_compactPartition w K width (m+n))
  have hs : z*s ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ s hpartition)
    (compactPartition_reciprocal w hw0 hw1 hw ht stage)
  have hrs : r ≈ s := reciprocal_unique z r s hr hs
  change weightedMass w K width
      (polyMul (polyMul (terminalMessage w K width m) (sourceProbe width fs))
        (terminalMessage w K width n)) * r ≈
    numerator w (B extent) extent (chainIds extent width start (m+n))
      (sweptProduct extent 0 (placeProbes (start+m) fs)) K * s
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r (middleNumerator_pin hw ht w K fs hfs))
    (Q'.mul_eqv_congr_left _ _ _ hrs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.middle_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.middle_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.swept_middle_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.original_middle_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.middleNumerator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle.middleRatio_originalFiniteValue
