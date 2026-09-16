/-
# Quantitative right-boundary forgetting for any observed polynomial window

The constructed window certificates bound F_m relative to u_(m+L), with
endpoints given by the observed polynomial's computed cap. Iterating the
original transfer shrinks this SAME bracket. Every later normalized window
ratio lies in the earlier bracket, giving 2*C*q^s common-right-tail control.
The bound is independent of the fixed left boundary m and late cutoff K;
it still depends on nome, spatial width and the window polynomial. It does
not compare different left boundaries or establish stationarity/physical OS.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
import YMGap.Continuum.SU2QuaternionHeadWindowBounds
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowBounds
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks mixRate windowRatio

/-- The interval on the entire observed window constructs the initial
relative bracket; no positivity assumption on the signed insertion is used. -/
def initialWindowBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    Bracket width (observedMessage w K width m L p) (terminalMessage w K width (m+L)) := by
  have hD := iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) m L polyOne
  change terminalMessage w K width (m+L) =
    iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) L
      (terminalMessage w K width m) at hD
  have hu := windowMessage_upper_certificate (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK)
    L (terminalMessage_supported w K width m) (terminalMessage_certificate hw0 hw1 K width hK m) I
  have hl := windowMessage_lower_certificate (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK)
    L (terminalMessage_supported w K width m) (terminalMessage_certificate hw0 hw1 K width hK m) I
  rw [← hD] at hu hl
  exact ⟨-c, c, Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_coefficient (Q'.neg_neg_eqv c) _)) hl, hu⟩

/-- Computed actual-transfer brackets after n right-boundary steps. -/
def windowBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    Bracket width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (observedMessage w K width m L p))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (terminalMessage w K width (m+L))) :=
  iterateBracket hw0 hw1 K width hK n
    (observedMessage_supported w K width m L I.support)
    (terminalMessage_supported w K width (m+L))
    (terminalMessage_certificate hw0 hw1 K width hK (m+L))
    (terminalMessage_mass_positive hw0 hw1 K width hK (m+L))
    (initialWindowBracket hw0 hw1 K width hK m L I)

theorem windowBracket_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) :
    (windowBracket hw0 hw1 K width hK m L n I).upper +
      -(windowBracket hw0 hw1 K width hK m L n I).lower ≈
        mixRate hw0 hw1 width ^ n * (c+c) :=
  Q'.eqv_trans _ _ _
    (iterateBracket_width hw0 hw1 K width hK n
      (observedMessage_supported w K width m L I.support)
      (terminalMessage_supported w K width (m+L))
      (terminalMessage_certificate hw0 hw1 K width hK (m+L))
      (terminalMessage_mass_positive hw0 hw1 K width hK (m+L))
      (initialWindowBracket hw0 hw1 K width hK m L I))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_neg_eqv c)))

/-- Every later actual normalized window ratio lies in the earlier bracket. -/
theorem windowRatio_later_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L s n : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) (hsn : s ≤ n) :
    (windowBracket hw0 hw1 K width hK m L s I).lower ≤ windowRatio hw0 hw1 K width hK m L n p ∧
      windowRatio hw0 hw1 K width hK m L n p ≤ (windowBracket hw0 hw1 K width hK m L s I).upper := by
  have he := windowRatio_iterate hw0 hw1 K width hK m L n I.support
  have hb := massRatio_bounds hw0 hw1 K width hK
    (iterateWeightedMass_positive hw0 hw1 K width hK n
      (terminalMessage_supported w K width (m+L))
      (terminalMessage_certificate hw0 hw1 K width hK (m+L))
      (terminalMessage_mass_positive hw0 hw1 K width hK (m+L)))
    (windowBracket hw0 hw1 K width hK m L n I)
  have hn := iterateBracket_nested hw0 hw1 K width hK s n hsn
    (observedMessage_supported w K width m L I.support)
    (terminalMessage_supported w K width (m+L))
    (terminalMessage_certificate hw0 hw1 K width hK (m+L))
    (terminalMessage_mass_positive hw0 hw1 K width hK (m+L))
    (initialWindowBracket hw0 hw1 K width hK m L I)
  exact ⟨Q'.le_trans' _ _ _ hn.1 (Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ hb.2 hn.2)⟩

private theorem common_interval (l u x y C : Q')
    (hx : l ≤ x ∧ x ≤ u) (hy : l ≤ y ∧ y ≤ u) (hc : u + -l ≈ C) :
    x ≤ y+C ∧ y ≤ x+C := by
  have hcancel : l + (u + -l) ≈ u := poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
    (fun | 0 => l | _ => u)
  have hup (z : Q') (hz : l ≤ z) : u ≤ z+C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right l z (u + -l) hz)
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl z) hc)))
  exact ⟨Q'.le_trans' _ _ _ hx.2 (hup y hy.1), Q'.le_trans' _ _ _ hy.2 (hup x hx.1)⟩

/-- Two arbitrary right-boundary distances have a common quantitative bound,
independent of the fixed left distance m. No comparison between left distances
or division by q is hidden in this statement. -/
theorem windowRatio_right_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L s n j : Nat) {p : RatPoly} {c : Q'}
    (I : Interval ((L+1)*(N width)) p c) (hsn : s ≤ n) (hsj : s ≤ j) :
    windowRatio hw0 hw1 K width hK m L n p ≤ windowRatio hw0 hw1 K width hK m L j p +
        mixRate hw0 hw1 width ^ s * (c+c) ∧
      windowRatio hw0 hw1 K width hK m L j p ≤ windowRatio hw0 hw1 K width hK m L n p +
        mixRate hw0 hw1 width ^ s * (c+c) :=
  common_interval _ _ _ _ _
    (windowRatio_later_bounds hw0 hw1 K width hK m L s n I hsn)
    (windowRatio_later_bounds hw0 hw1 K width hK m L s j I hsj)
    (windowBracket_width hw0 hw1 K width hK m L s I)

/-- Every supported polynomial window receives the bound with its computed
cap. No interval, positivity or rate estimate is assumed as a new input. -/
theorem polynomialWindow_right_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L s n j : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) (hsn : s ≤ n) (hsj : s ≤ j) :
    windowRatio hw0 hw1 K width hK m L n p ≤ windowRatio hw0 hw1 K width hK m L j p +
        mixRate hw0 hw1 width ^ s * (polynomialCap p + polynomialCap p) ∧
      windowRatio hw0 hw1 K width hK m L j p ≤ windowRatio hw0 hw1 K width hK m L n p +
        mixRate hw0 hw1 width ^ s * (polynomialCap p + polynomialCap p) :=
  windowRatio_right_commonTail hw0 hw1 K width hK m L s n j
    (polynomialInterval ((L+1)*(N width)) p hp) hsn hsj

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.initialWindowBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.windowBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.windowBracket_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.windowRatio_later_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.windowRatio_right_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket.polynomialWindow_right_commonTail
