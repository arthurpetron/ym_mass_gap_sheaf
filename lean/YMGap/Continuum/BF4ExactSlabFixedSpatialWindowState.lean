/-
# Positive window functionals and consistent placement of empty slices

The expectation is the already constructed polynomialWindowLimit, not a
new state supplied as a hypothesis. Same-partition finite laws and limit
uniqueness give normalization, signed rational linearity and positivity.
The rectangle estimate also controls each fixed-offset diagonal. Thus
exact finite padding identities give right-padding and one-slice-shift
consistency of this SAME limiting family. A zero-transition window agrees
with the existing supported-slice expectation.

These are real polynomial windows at fixed nome, spatial width and heat
cutoff. No finite stationary identity is assumed. Original ambient gauge
observable identification, cutoff removal, reflected physical OS positivity,
continuum construction and a physical Hamiltonian gap remain separate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks mixRate windowRatio

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Every fixed-offset diagonal approaches the same returned window limit.
Both the sequence threshold and representative threshold are the existing
explicit windowTimeModulus; no subsequence selection is used. -/
theorem windowTime_converges_offsets {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L a b : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    ConvergesTo (fun t => ofQ' (windowRatio hw0 hw1 K width hK (t+a) L (t+b) p))
      (windowTimeLimit hw0 hw1 K width hK L I) := by
  intro epsilon he
  let s := geometricCutoff (mixRate hw0 hw1 width) (windowTimeCap hw0 hw1 width c) epsilon
  refine ⟨windowTimeModulus hw0 hw1 width c epsilon, fun t ht =>
    ⟨windowTimeModulus hw0 hw1 width c epsilon, fun k hk => ?_⟩⟩
  have ht' : s+1 ≤ t := by
    change 1+s ≤ t at ht
    omega
  have hk' : s+1 ≤ k := by
    change 1+s ≤ k at hk
    omega
  have hb := windowTime_approx_rectangular hw0 hw1 K width hK L I s (t+a) (t+b) k
    (by omega) (by omega) hk'
  have herror := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (windowTimeCap_nonnegative hw0 hw1 width I.nonnegative)
    he s (Nat.le_refl s)
  exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ herror),
    Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ herror)⟩

/-- Computed-cap offset convergence for every supported polynomial. -/
theorem polynomialWindow_converges_offsets {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L a b : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    ConvergesTo (fun t => ofQ' (windowRatio hw0 hw1 K width hK (t+a) L (t+b) p))
      (polynomialWindowLimit hw0 hw1 K width hK L p hp) :=
  windowTime_converges_offsets hw0 hw1 K width hK L a b
    (polynomialInterval ((L+1)*(N width)) p hp)

/-- Normalization of every representative of the returned functional. -/
theorem windowLimit_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L polyOne (supported_one _)) (ofQ' 1) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    windowRatio_one hw0 hw1 K width hK
      (QMhat _ (polynomialWindowCauchy hw0 hw1 K width hK L polyOne (supported_one _)) k) L
      (QMhat _ (polynomialWindowCauchy hw0 hw1 K width hK L polyOne (supported_one _)) k))

/-- Addition survives differing polynomial caps and representative moduli. -/
theorem windowLimit_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((L+1)*(N width)) q) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L (polyAdd p q) (supported_add hp hq))
      (add (polynomialWindowLimit hw0 hw1 K width hK L p hp)
        (polynomialWindowLimit hw0 hw1 K width hK L q hq)) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_add hw0 hw1 K width hK t L t p q))
    (polynomialWindow_converges hw0 hw1 K width hK L (polyAdd p q) (supported_add hp hq))
    (TrigAddCReal.convergesTo_add (polynomialWindow_converges hw0 hw1 K width hK L p hp)
      (polynomialWindow_converges hw0 hw1 K width hK L q hq))

/-- Rational linearity allows arbitrary signed scales. -/
theorem windowLimit_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L (polySmul c p) (support_smul hp c))
      (mul (ofQ' c) (polynomialWindowLimit hw0 hw1 K width hK L p hp)) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_smul hw0 hw1 K width hK t L t c p))
    (polynomialWindow_converges hw0 hw1 K width hK L (polySmul c p) (support_smul hp c))
    (convergesTo_constMul c (polynomialWindow_converges hw0 hw1 K width hK L p hp))

theorem windowLimit_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((L+1)*(N width)) q) (h : RatPolyCoeffEqv p q) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L p hp)
      (polynomialWindowLimit hw0 hw1 K width hK L q hq) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_congr hw0 hw1 K width hK t L t h))
    (polynomialWindow_converges hw0 hw1 K width hK L p hp)
    (polynomialWindow_converges hw0 hw1 K width hK L q hq)

/-- Arbitrary-insertion Haar equality survives the same window action and
limit. In particular the carrier relations are not lost by taking limits. -/
theorem windowLimit_carrier_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((L+1)*(N width)) q)
    (h : HaarCarrierEqv ((L+1)*(N width)) p q) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L p hp)
      (polynomialWindowLimit hw0 hw1 K width hK L q hq) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => windowRatio_carrier_congr hw0 hw1 K width hK t L t h))
    (polynomialWindow_converges hw0 hw1 K width hK L p hp)
    (polynomialWindow_converges hw0 hw1 K width hK L q hq)

/-- Positivity uses each actual finite representative, in the transitive
eventual order; it is not reflection positivity or an OS inner product. -/
theorem windowLimit_certificate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (P : Certificate ((L+1)*(N width)) p) :
    leEv (ofQ' 0) (polynomialWindowLimit hw0 hw1 K width hK L p hp) :=
  leEv_ofQ'_of_approx_ge (fun k =>
    windowRatio_certificate_nonnegative hw0 hw1 K width hK
      (QMhat _ (polynomialWindowCauchy hw0 hw1 K width hK L p hp) k) L
      (QMhat _ (polynomialWindowCauchy hw0 hw1 K width hK L p hp) k) hp P)

theorem windowLimit_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    leEv (ofQ' 0) (polynomialWindowLimit hw0 hw1 K width hK L
      (polyMul p p) (supported_polyMul hp hp)) :=
  windowLimit_certificate_nonnegative hw0 hw1 K width hK L
    (supported_polyMul hp hp) (.square p hp)

/-- Adding one unobserved right slice does not change the limiting expectation.
The finite comparison is (t,L,t+1), not an assumed finite stationary law. -/
theorem windowLimit_pad_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK (L+1) p (windowSupport_right hp))
      (polynomialWindowLimit hw0 hw1 K width hK L p hp) := by
  have hconv := polynomialWindow_converges_offsets hw0 hw1 K width hK L 0 1 p hp
  simp only [Nat.add_zero] at hconv
  exact Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_pad_right hw0 hw1 K width hK t L t hp))
    (polynomialWindow_converges hw0 hw1 K width hK (L+1) p (windowSupport_right hp)) hconv

/-- Shifting all observed coordinates by one slice and adding that unobserved
left slice preserves the limit. The exact finite comparison is (t+1,L,t). -/
theorem windowLimit_pad_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK (L+1)
      (liftBoundary (N width) p) (windowSupport_left hp))
      (polynomialWindowLimit hw0 hw1 K width hK L p hp) := by
  have hconv := polynomialWindow_converges_offsets hw0 hw1 K width hK L 1 0 p hp
  simp only [Nat.add_zero] at hconv
  exact Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_pad_left hw0 hw1 K width hK t L t hp))
    (polynomialWindow_converges hw0 hw1 K width hK (L+1)
      (liftBoundary (N width) p) (windowSupport_left hp)) hconv

/-- Translation of a supported insertion by one slice preserves its value
in one common enlarged window. This follows from the two proved padding
laws, not from stationarity of a finite boundary-conditioned chain. -/
theorem windowLimit_shift {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK (L+1)
      (liftBoundary (N width) p) (windowSupport_left hp))
      (polynomialWindowLimit hw0 hw1 K width hK (L+1) p (windowSupport_right hp)) :=
  Equiv.trans (windowLimit_pad_left hw0 hw1 K width hK L p hp)
    (Equiv.symm (windowLimit_pad_right hw0 hw1 K width hK L p hp))

/-- The zero-transition window is the SAME previously constructed slice
functional, even though the two constructive moduli differ. -/
theorem windowLimit_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK 0 p (by simpa only [Nat.zero_add, Nat.one_mul] using hp))
      (BF4ExactSlabFixedSpatialPolynomialState.expectation hw0 hw1 K width hK p hp) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => windowRatio_zero hw0 hw1 K width hK t t hp))
    (polynomialWindow_converges hw0 hw1 K width hK 0 p (by simpa only [Nat.zero_add, Nat.one_mul] using hp))
    (BF4ExactSlabFixedSpatialPolynomialState.expectation_converges hw0 hw1 K width hK p hp)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowTime_converges_offsets
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.polynomialWindow_converges_offsets
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_pad_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_pad_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState.windowLimit_zero
