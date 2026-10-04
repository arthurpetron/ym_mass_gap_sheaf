/-
# Last-step score from the actual incoming conditional ratio

For a=g_d and an arbitrary supported incoming polynomial phi, keep
A=T a, b=T(a phi), and N=A*T(a phi^2)-b^2. The ORIGINAL one-step
terminal-weighted window constructs N>=0 and Score(A,b)^2<=L(w)^2*A^2*N.
The lower weight is K*V*a, not K*V with an additional a^2 residual.

This is the finite incoming-ratio leg of the original last-step conditional
energy route. It supplies the hypotheses of
QuaternionHaarConditionalScoreGradient.scoreMultiplierCertificate without
an incoming inverse or a T1 multiplier. It does not compare this budget
with the older paired budget, identify a martingale weight with Vbar^2,
or prove a useful relative cost on a changing physical family.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
import YMGap.Continuum.QuaternionHaarConditionalScoreGradient

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
  (blockNoise blockNoise_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
  (original_block_scoreVariance_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff relativeCap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight terminalMessage

/-- The literal last-step conditional noise under K*V*g_d. -/
def lastStepRatioNoise (w : Q') (K width d : Nat) (phi : RatPoly) : RatPoly :=
  blockNoise w K width 1 (terminalMessage w K width d) phi

/-- Actual one-step outputs, not a normalized or substituted transfer. -/
theorem lastStepRatioNoise_pin (w : Q') (K width d : Nat) (phi : RatPoly) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let b := transferStep w K width (polyMul a phi)
    RatPolyCoeffEqv (lastStepRatioNoise w K width d phi)
      (polyAdd (polyMul A (transferStep w K width (polyMul a (polyMul phi phi))))
        (polyNeg (polyMul b b))) :=
  RatPolyCoeffEqv.refl _

/-- Noise positivity is constructed from the complete original window.
The source phi can be signed and may use every original input coordinate. -/
def lastStepRatioNoise_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    Certificate (N width) (lastStepRatioNoise w K width d phi) :=
  blockNoise_certificate hw0 hw1 K width hK 1
    (terminalMessage_supported w K width d) hphi
    (terminalMessage_certificate hw0 hw1 K width hK d)

private theorem shifted_zero (phi : RatPoly) :
    RatPolyCoeffEqv (shifted phi 0) phi :=
  ((RatPolyCoeffEqv.one_smul phi).add
    ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (-0) 0) polyOne).trans
      (RatPolyCoeffEqv.zero_smul polyOne))).trans (RatPolyCoeffEqv.add_zero phi)

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem score_congr (i j : Nat) {A A' b b' : RatPoly}
    (hA : RatPolyCoeffEqv A A') (hb : RatPolyCoeffEqv b b') :
    RatPolyCoeffEqv (conditionalScore i j A b) (conditionalScore i j A' b') :=
  (hA.mul (angularDerivative_congr i j hb)).add
    (RatPolyCoeffEqv.neg (hb.mul (angularDerivative_congr i j hA)))

/-- The last ORIGINAL transition produces the score-square certificate.
Its positive conditional weight is K*V*g_d; both outgoing messages and
the entire original action are retained. No incoming ratio is assumed. -/
def lastStepRatioNoise_score_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (d s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let b := transferStep w K width (polyMul a phi)
    let S := conditionalScore (4*s+i) (4*s+j) A b
    Certificate (N width) (polyAdd
      (polyMul (cap (relativeCap w 32*relativeCap w 32))
        (polyMul (polyMul A A) (lastStepRatioNoise w K width d phi)))
      (polyNeg (polyMul S S))) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let psi := shifted phi 0
  have hp : RatPolyCoeffEqv psi phi := shifted_zero phi
  have hA : RatPolyCoeffEqv (terminalMessage w K width (d+(0+1))) A := by
    change RatPolyCoeffEqv (terminalMessage w K width (d+1))
      (transferStep w K width (terminalMessage w K width d))
    rw [← terminalMessage_next w K width d]
    exact RatPolyCoeffEqv.refl _
  have hb : RatPolyCoeffEqv
      (originalBlockTransfer w K width (0+1) (polyMul a psi)) b :=
    transfer_congr w K width (hp.mul_left a)
  have hH := transfer_congr w K width ((hp.mul hp).mul_left a)
  have hnoise : RatPolyCoeffEqv (blockNoise w K width (0+1) a psi)
      (lastStepRatioNoise w K width d phi) :=
    ((RatPolyCoeffEqv.refl A).mul hH).add (RatPolyCoeffEqv.neg (hb.mul hb))
  have hscore := score_congr (4*s+i) (4*s+j) hA hb
  have P := original_block_scoreVariance_certificate
    hw0 hw1 K width hK d 0 s hs hi hj phi 0 hphi
  exact Certificate.ofCoeff
    ((((hA.mul hA).mul hnoise).mul_left
      (cap (relativeCap w 32*relativeCap w 32))).add
      (RatPolyCoeffEqv.neg (hscore.mul hscore))).symm P

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise.lastStepRatioNoise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise.lastStepRatioNoise_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise.lastStepRatioNoise_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise.lastStepRatioNoise_score_certificate
