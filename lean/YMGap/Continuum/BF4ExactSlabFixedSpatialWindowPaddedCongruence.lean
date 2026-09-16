/-
# Supported padded congruence for the actual window expectation

The finite numerator is the full-window Haar integral of the left terminal
message, the insertion, and the original K/V chain ending in the right
terminal message. Every factor is supported on that same window. Hence
padded coefficient equality may be removed there without asserting equality
against arbitrary unsupported Haar insertions.

The partition is unchanged. Finite congruence then passes to the existing
polynomialWindowLimit by its existing convergence theorem, even when the
two presentations have different computed polynomial caps and moduli.
No new limiting functional, action, normalization, or analytic premise is
introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks terminalMessage

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- Both terminal messages and every window action factor remain in the
same integral. Reordering the last V does not duplicate or omit it. -/
private theorem numerator_pairing (w : Q') (K width m L n : Nat) (p : RatPoly) :
    quaternionHaar ((L+1)*(N width))
      (polyMul (polyMul (terminalMessage w K width m) p)
        (chain (N width) (kineticWeight w K width) (spatialWeight w K width)
          L (terminalMessage w K width n))) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m L p) (terminalMessage w K width n)) := by
  have hpair := windowMessage_pairing (N width) (kineticWeight w K width)
    (spatialWeight w K width) L (terminalMessage w K width m) p (terminalMessage w K width n)
  change quaternionHaar ((L+1)*(N width)) _ ≈
    quaternionHaar (N width)
      (polyMul (observedMessage w K width m L p)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n))) at hpair
  unfold weightedMass
  exact Q'.eqv_trans _ _ _ hpair
    (haar_of_coeff
      ((RatPolyCoeffEqv.mul_assoc (observedMessage w K width m L p)
        (spatialWeight w K width) (terminalMessage w K width n)).symm.trans
        (((RatPolyCoeffEqv.mul_comm (observedMessage w K width m L p)
          (spatialWeight w K width)).mul_right (terminalMessage w K width n)).trans
          (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width)
            (observedMessage w K width m L p) (terminalMessage w K width n)))))

/-- Padded equality of supported insertions preserves the finite ratio
with its original K/V background and identical positive partition. -/
theorem windowRatio_padded_congr {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((L+1)*(N width)) q)
    (h : PaddedPolynomialCoeffEqv ((L+1)*(N width)) p q) :
    windowRatio hw0 hw1 K width hK m L n p ≈
      windowRatio hw0 hw1 K width hK m L n q := by
  have hb : N width ≤ (L+1)*(N width) := by
    rw [Nat.succ_mul]
    omega
  have hin := support_mono (terminalMessage_supported w K width m) hb
  have hc := chain_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) L (terminalMessage_supported w K width n)
  have hsource :=
    ((PaddedPolynomialCoeffEqv.refl ((L+1)*(N width)) (terminalMessage w K width m)).mul h).mul
      (PaddedPolynomialCoeffEqv.refl ((L+1)*(N width))
        (chain (N width) (kineticWeight w K width) (spatialWeight w K width)
          L (terminalMessage w K width n)))
  have hhaar := hsource.haar
    (supported_polyMul (supported_polyMul hin hp) hc)
    (supported_polyMul (supported_polyMul hin hq) hc)
  have hnum := Q'.eqv_trans _ _ _ (Q'.eqv_symm (numerator_pairing w K width m L n p))
    (Q'.eqv_trans _ _ _ hhaar (numerator_pairing w K width m L n q))
  unfold windowRatio massRatio
  exact Q'.mul_eqv_congr_right _ _ _ hnum

/-- The already-returned constructive limits agree. Their individual caps,
explicit moduli and representative indices need not coincide. -/
theorem windowLimit_padded_congr {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((L+1)*(N width)) q)
    (h : PaddedPolynomialCoeffEqv ((L+1)*(N width)) p q) :
    Equiv (polynomialWindowLimit hw0 hw1 K width hK L p hp)
      (polynomialWindowLimit hw0 hw1 K width hK L q hq) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      windowRatio_padded_congr hw0 hw1 K width hK t L t hp hq h))
    (polynomialWindow_converges hw0 hw1 K width hK L p hp)
    (polynomialWindow_converges hw0 hw1 K width hK L q hq)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence.windowRatio_padded_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence.windowLimit_padded_congr
