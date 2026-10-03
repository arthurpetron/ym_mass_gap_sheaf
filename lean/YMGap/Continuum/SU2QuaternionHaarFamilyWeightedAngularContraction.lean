/-
# Original angular energy contracts under SAME-weight fringe projection

Distinct-block derivative commutation and the actual weighted square
Pythagoras preserve the complete positive surrounding weight. At averaged
blocks the derivative vanishes. Each block and their full sum contract with
coefficient one, including repeated/empty schedules and zero weights.

The consumer is the SECOND-derivative energy of the original projected
source. This does not bound that energy by its first-derivative square,
the surviving norm, or any scaling-uniform quantity.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
import YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras

namespace YMGap.Continuum.SU2QuaternionHaarFamilyWeightedAngularContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
open YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

/-- The complete positive surrounding weight remains on BOTH sides. -/
theorem familyProject_weighted_blockDerivative_square_le
    (blocks : Nat) (ids : List Nat) (hids : ∀ s, s ∈ ids → s < blocks)
    (block i j : Nat) (hb : block < blocks) (hi : i < 4) (hj : j < 4)
    (W f : RatPoly) (P : Certificate blocks W)
    (hf : SupportedQuaternionBlocks blocks f)
    (hW : ∀ s, s ∈ ids → QuaternionBlockIndependent s W) :
    quaternionHaar blocks (polyMul W
      (polyMul (blockAngularDerivative block i j (familyProject ids f))
        (blockAngularDerivative block i j (familyProject ids f)))) ≤
      quaternionHaar blocks (polyMul W
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f))) := by
  have hs : SupportedQuaternionBlocks blocks (blockAngularDerivative block i j f) :=
    angularDerivative_supported_at (by omega) (by omega) hf
  by_cases hm : block ∈ ids
  · have hz := angularDerivative_blockIndependent_zero hi hj
      (familyProject_independent ids f block hm)
    have hzero := ((hz.mul hz).mul_left W).trans (RatPolyCoeffEqv.mul_zero_right W)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hzero))
      (P.mul (.square _ hs)).haar_nonnegative
  · have hd := blockAngularDerivative_familyProject ids block i j hi hj hm f
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hd.mul hd).mul_left W)))
      (familyProject_weighted_square_le blocks ids hids P hs hW)

/-- No discarded weight and no number-of-links penalty in the actual block
energy contraction. It is an energy-to-energy, NOT energy-to-norm bound. -/
theorem familyProject_weighted_blockAngularSquare_le
    (blocks : Nat) (ids : List Nat) (hids : ∀ s, s ∈ ids → s < blocks)
    (block : Nat) (hb : block < blocks) (W f : RatPoly)
    (P : Certificate blocks W) (hf : SupportedQuaternionBlocks blocks f)
    (hW : ∀ s, s ∈ ids → QuaternionBlockIndependent s W) :
    quaternionHaar blocks (polyMul W (blockAngularSquare block (familyProject ids f))) ≤
      quaternionHaar blocks (polyMul W (blockAngularSquare block f)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six blocks W _))
    (Q'.le_trans' _ _ _
      (sixValue_mono _ _ (fun i j hi hj =>
        familyProject_weighted_blockDerivative_square_le blocks ids hids block i j hb hi hj
          W f P hf hW))
      (Q'.ge_of_eqv (haar_six blocks W _)))

theorem familyProject_weighted_angularSum_le
    (blocks : Nat) (ids : List Nat) (hids : ∀ s, s ∈ ids → s < blocks)
    (W f : RatPoly) (P : Certificate blocks W)
    (hf : SupportedQuaternionBlocks blocks f)
    (hW : ∀ s, s ∈ ids → QuaternionBlockIndependent s W) :
    finSum (fun b => quaternionHaar blocks
      (polyMul W (blockAngularSquare b (familyProject ids f)))) blocks ≤
      finSum (fun b => quaternionHaar blocks (polyMul W (blockAngularSquare b f))) blocks :=
  finSum_le_lt _ _ blocks (fun b hb =>
    familyProject_weighted_blockAngularSquare_le blocks ids hids b hb W f P hf hW)

#print axioms familyProject_weighted_blockDerivative_square_le
#print axioms familyProject_weighted_blockAngularSquare_le
#print axioms familyProject_weighted_angularSum_le

end YMGap.Continuum.SU2QuaternionHaarFamilyWeightedAngularContraction
