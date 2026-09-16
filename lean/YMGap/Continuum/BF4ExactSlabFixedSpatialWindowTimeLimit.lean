/-
# Constructive two-boundary time limit for an actual polynomial window

The scalar is the existing windowRatio with its unchanged original K/V
chain numerator and positive terminal-pair partition. The common-tail
estimate constructs rational Cauchy data for the diagonal boundary sequence,
with the explicit threshold 1 + geometricCutoff. The extra one preserves
the first refreshed layer required by the two-boundary comparison.

Every late rectangle approaches the same returned CReal representative;
the left length, right length and representative index vary independently.
The modulus is independent of the late heat cutoff, but keeps nome, spatial
width and the observed polynomial cap explicit. Polynomial specialization
constructs the interval from syntactic support, without a new bound premise.
This is a fixed-window scalar time limit, not yet a consistent stationary
cylinder state, cutoff removal, reflected OS construction or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
  (windowTimeCap windowTimeCap_nonnegative windowRatio_commonTail)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks mixRate windowRatio windowTimeCap

/-- Explicit common boundary-length threshold. The first refreshed layer
is retained, including the zero-rate and zero-cap branches. No K argument. -/
def windowTimeModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c epsilon : Q') : Nat :=
  1 + geometricCutoff (mixRate hw0 hw1 width) (windowTimeCap hw0 hw1 width c) epsilon

/-- Type-level Cauchy data for the actual normalized window diagonal. -/
def windowTimeCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    QCauchy (fun t => windowRatio hw0 hw1 K width hK t L t p) where
  M := windowTimeModulus hw0 hw1 width c
  bound := by
    intro epsilon he i j hi hj
    let s := geometricCutoff (mixRate hw0 hw1 width) (windowTimeCap hw0 hw1 width c) epsilon
    have hi' : s+1 ≤ i := by
      change 1+s ≤ i at hi
      omega
    have hj' : s+1 ≤ j := by
      change 1+s ≤ j at hj
      omega
    have hb := windowRatio_commonTail hw0 hw1 K width hK L s i i j j I hi' hi' hj' hj'
    have heq := geometric_bound (mixRate_nonnegative hw0 hw1 width)
      (mixRate_lt_one hw0 hw1 width) (windowTimeCap_nonnegative hw0 hw1 width I.nonnegative)
      he s (Nat.le_refl s)
    exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ heq),
      Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ heq)⟩

/-- The displayed explicit modulus is the one stored in the Cauchy witness. -/
theorem windowTimeCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) (epsilon : Q') :
    (windowTimeCauchy hw0 hw1 K width hK L I).M epsilon =
      windowTimeModulus hw0 hw1 width c epsilon := rfl

/-- The constructed fixed-window time limit with the same finite normalization. -/
def windowTimeLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) : CReal :=
  ofQ'CauchySeq _ (windowTimeCauchy hw0 hw1 K width hK L I)

theorem windowTime_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    ConvergesTo (fun t => ofQ' (windowRatio hw0 hw1 K width hK t L t p))
      (windowTimeLimit hw0 hw1 K width hK L I) :=
  convergesTo_ofQ'CauchySeq _ (windowTimeCauchy hw0 hw1 K width hK L I)

/-- Independent boundary lengths approach the SAME diagonal representative.
All three displayed indices retain the required first-layer offset. -/
theorem windowTime_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) (s m n k : Nat)
    (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hk : s+1 ≤ k) :
    windowRatio hw0 hw1 K width hK m L n p ≤
        (windowTimeLimit hw0 hw1 K width hK L I).approx k +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width c ∧
      (windowTimeLimit hw0 hw1 K width hK L I).approx k ≤
        windowRatio hw0 hw1 K width hK m L n p +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width c :=
  windowRatio_commonTail hw0 hw1 K width hK L s m n
    (QMhat _ (windowTimeCauchy hw0 hw1 K width hK L I) k)
    (QMhat _ (windowTimeCauchy hw0 hw1 K width hK L I) k) I hm hn
    (Nat.le_trans hk (self_le_QMhat _ _ k)) (Nat.le_trans hk (self_le_QMhat _ _ k))

/-- Every supported window polynomial receives Cauchy data from its actual
computed certificate; no interval or analytic cap is a new input. -/
def polynomialWindowCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    QCauchy (fun t => windowRatio hw0 hw1 K width hK t L t p) :=
  windowTimeCauchy hw0 hw1 K width hK L (polynomialInterval ((L+1)*(N width)) p hp)

theorem polynomialWindowCauchy_modulus {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) (epsilon : Q') :
    (polynomialWindowCauchy hw0 hw1 K width hK L p hp).M epsilon =
      windowTimeModulus hw0 hw1 width (polynomialCap p) epsilon := rfl

/-- Actual scalar time limit for any supported polynomial on the fixed window. -/
def polynomialWindowLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) : CReal :=
  windowTimeLimit hw0 hw1 K width hK L (polynomialInterval ((L+1)*(N width)) p hp)

theorem polynomialWindow_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    ConvergesTo (fun t => ofQ' (windowRatio hw0 hw1 K width hK t L t p))
      (polynomialWindowLimit hw0 hw1 K width hK L p hp) :=
  windowTime_converges hw0 hw1 K width hK L (polynomialInterval ((L+1)*(N width)) p hp)

/-- Computed-cap specialization of the representative bound, not only a
convergence assertion about an unspecified limit. -/
theorem polynomialWindow_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (s m n k : Nat) (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hk : s+1 ≤ k) :
    windowRatio hw0 hw1 K width hK m L n p ≤
        (polynomialWindowLimit hw0 hw1 K width hK L p hp).approx k +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap p) ∧
      (polynomialWindowLimit hw0 hw1 K width hK L p hp).approx k ≤
        windowRatio hw0 hw1 K width hK m L n p +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap p) :=
  windowTime_approx_rectangular hw0 hw1 K width hK L
    (polynomialInterval ((L+1)*(N width)) p hp) s m n k hm hn hk

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTimeModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTimeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTimeCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTimeLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTime_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.windowTime_approx_rectangular
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindowCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindowCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindowLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindow_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindow_approx_rectangular
