/-
# Finite positive linear laws for the actual window ratio

At fixed nome, width, late heat cutoff and boundary lengths, the actual
window ratio is a normalized rational-linear functional of the full
window insertion. All laws retain the SAME positive partition
ell(u_(m+L)*u_n), independent of the probe. Signed homogeneity and
coefficient/Haar-carrier congruence require no support assumption.

Positivity integrates the insertion certificate against the original
half-open action and both actual terminal messages; the last spatial
weight is supplied exactly once by ell. These finite laws feed the
constructed window time limit. Original ambient geometric identification,
consistent stationary cylinder laws and reflected OS positivity are not
asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
import YMGap.Continuum.SU2QuaternionHeadWindowBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr weightedMass_add weightedMass_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks terminalMessage

/-- Full-window Haar-carrier equality survives the actual input, action,
partial integration, final spatial weight and terminal message. Arbitrary
off-carrier insertions are retained; no support premise is discarded. -/
theorem windowRatio_carrier_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p q : RatPoly}
    (h : HaarCarrierEqv ((L+1)*(N width)) p q) :
    windowRatio hw0 hw1 K width hK m L n p ≈
      windowRatio hw0 hw1 K width hK m L n q := by
  have hs := HaarCarrierEqv.mul_right
    (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) L)
    (h.mul_left (terminalMessage w K width m))
  have hsize : (L+1)*(N width) = N width + L*(N width) := by
    rw [Nat.succ_mul]
    omega
  have hm : HaarCarrierEqv (N width)
      (observedMessage w K width m L p) (observedMessage w K width m L q) :=
    partialHaarHeads_carrier (tailBlocks := N width) (headBlocks := L*(N width)) (hsize ▸ hs)
  apply massRatio_congr w K width
    (terminalPair_positive hw0 hw1 K width hK (m+L) n)
    (terminalPair_positive hw0 hw1 K width hK (m+L) n)
  · unfold weightedMass
    exact (HaarCarrierEqv.mul_right (terminalMessage w K width n) hm) (spatialWeight w K width)
  · exact Q'.eqv_refl _

/-- Coefficient equality preserves the finite normalized window ratio. -/
theorem windowRatio_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    windowRatio hw0 hw1 K width hK m L n p ≈
      windowRatio hw0 hw1 K width hK m L n q :=
  windowRatio_carrier_congr hw0 hw1 K width hK m L n (RatPolyCoeffEqv.haarCarrier h)

/-- The unit insertion cancels the SAME original positive window partition. -/
theorem windowRatio_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) :
    windowRatio hw0 hw1 K width hK m L n polyOne ≈ 1 := by
  unfold windowRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (weightedMass_congr w K width
        ((window_unobserved_pin w K width m L).mul_right (terminalMessage w K width n))))
    (Q'.mul_recipPos_eqv _ (terminalPair_positive hw0 hw1 K width hK (m+L) n))

/-- Additivity for arbitrary full-window polynomials, with no support guard. -/
theorem windowRatio_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) (p q : RatPoly) :
    windowRatio hw0 hw1 K width hK m L n (polyAdd p q) ≈
      windowRatio hw0 hw1 K width hK m L n p +
        windowRatio hw0 hw1 K width hK m L n q := by
  have he : RatPolyCoeffEqv
      (polyMul (observedMessage w K width m L (polyAdd p q)) (terminalMessage w K width n))
      (polyAdd
        (polyMul (observedMessage w K width m L p) (terminalMessage w K width n))
        (polyMul (observedMessage w K width m L q) (terminalMessage w K width n))) := by
    simpa only [observedMessage, polyMul_add_left_exact] using
      ((windowMessage_add (N width) (kineticWeight w K width) (spatialWeight w K width)
        L (terminalMessage w K width m) p q).mul_right (terminalMessage w K width n))
  unfold windowRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (weightedMass_congr w K width he) (weightedMass_add w K width _ _)))
    (Q'.add_mul_eqv _ _ _)

/-- Rational homogeneity includes arbitrary signed scales. -/
theorem windowRatio_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) (c : Q') (p : RatPoly) :
    windowRatio hw0 hw1 K width hK m L n (polySmul c p) ≈
      c * windowRatio hw0 hw1 K width hK m L n p := by
  have he := ((windowMessage_smul (N width) (kineticWeight w K width) (spatialWeight w K width)
      L (terminalMessage w K width m) c p).mul_right (terminalMessage w K width n)).trans
    (RatPolyCoeffEqv.polyMul_smul_left c (observedMessage w K width m L p)
      (terminalMessage w K width n))
  unfold windowRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (weightedMass_congr w K width he) (weightedMass_smul w K width c _)))
    (Q'.mul_assoc_eqv _ _ _)

/-- Certified full-window positivity survives integration against the actual
half-open action and both terminal messages, using the unchanged partition.
The support guard records the finite observable carrier. -/
theorem windowRatio_certificate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (P : Certificate ((L+1)*(N width)) p) :
    (0 : Q') ≤ windowRatio hw0 hw1 K width hK m L n p := by
  have H : Certificate (N width) (observedMessage w K width m L p) :=
    windowMessage_certificate (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      (stepWeightCertificate hw0 hw1 K width hK) L
      (terminalMessage_supported w K width m) (terminalMessage_certificate hw0 hw1 K width hK m) P
  unfold windowRatio massRatio
  exact Q'.mul_nonneg _ _
    (weightedMass_nonnegative hw0 hw1 K width hK
      (H.mul (terminalMessage_certificate hw0 hw1 K width hK n)))
    (Q'.le_of_lt (Q'.recipPos_pos _ (terminalPair_positive hw0 hw1 K width hK (m+L) n)))

/-- In particular, every supported square has nonnegative finite expectation. -/
theorem windowRatio_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    (0 : Q') ≤ windowRatio hw0 hw1 K width hK m L n (polyMul p p) :=
  windowRatio_certificate_nonnegative hw0 hw1 K width hK m L n
    (supported_polyMul hp hp) (.square p hp)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_square_nonnegative
