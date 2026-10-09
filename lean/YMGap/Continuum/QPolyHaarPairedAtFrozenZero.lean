/-
Raw zero jets for a polynomial independent of the selected quaternion block.
All frozen coefficients are multiplied after the actual ordered derivatives.
-/

import YMGap.Continuum.QPolyHaarPairedAtFrozenProduct
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.QPolyHaarPairedAtFrozenZero

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyZero
    quaternionBlockIndependent_polyOne)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (angularDerivative_blockIndependent_zero)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain
  (pairedAt_congr frozenFirstAt)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- The actual paired direction annihilates every raw spectator of its block. -/
theorem pairedAt_independent_zero (block : Nat) (i : Fin 3)
    {p : RatPoly} (hp : QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (pairedDerivativeAt block i p) polyZero := by
  have h (a b : Nat) (ha : a < 4) (hb : b < 4) :
      RatPolyCoeffEqv (blockAngularDerivative block a b p) polyZero :=
    angularDerivative_blockIndependent_zero ha hb hp
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((h 0 1 (by decide) (by decide)).add
      (h 2 3 (by decide) (by decide))).trans (RatPolyCoeffEqv.zero_add polyZero)
  · exact ((h 0 2 (by decide) (by decide)).add
      (RatPolyCoeffEqv.neg (h 1 3 (by decide) (by decide)))).trans
        (RatPolyCoeffEqv.zero_add polyZero)
  · exact ((h 0 3 (by decide) (by decide)).add
      (h 1 2 (by decide) (by decide))).trans (RatPolyCoeffEqv.zero_add polyZero)

/-- The three frozen first jets vanish for a spectator, with arbitrary u. -/
theorem frozenFirstAt_independent_zero (block : Nat) (u : Fin 3 → RatPoly)
    {p : RatPoly} (hp : QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (frozenFirstAt block u p) polyZero := by
  have h (i : Fin 3) : RatPolyCoeffEqv
      (polyMul (u i) (pairedDerivativeAt block i p)) polyZero :=
    ((pairedAt_independent_zero block i hp).mul_left (u i)).trans
      (RatPolyCoeffEqv.mul_zero_right (u i))
  exact threeSum_congr h

/-- All nine ordered frozen second jets vanish for a spectator, with no
derivative acting on u. -/
theorem frozenSecondAt_independent_zero (block : Nat) (u : Fin 3 → RatPoly)
    {p : RatPoly} (hp : QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (frozenSecondAt block u p) polyZero := by
  have h (i j : Fin 3) : RatPolyCoeffEqv
      (pairedDerivativeAt block i (pairedDerivativeAt block j p)) polyZero :=
    (pairedAt_congr block i (pairedAt_independent_zero block j hp)).trans
      (pairedAt_independent_zero block i (quaternionBlockIndependent_polyZero block))
  have hcell (i j : Fin 3) : RatPolyCoeffEqv
      (polyMul (polyMul (u i) (u j))
        (pairedDerivativeAt block i (pairedDerivativeAt block j p))) polyZero :=
    ((h i j).mul_left (polyMul (u i) (u j))).trans
      (RatPolyCoeffEqv.mul_zero_right _)
  exact threeSum_congr (fun i => threeSum_congr (hcell i))

/-- The multiplicative unit is independent of every quaternion block. -/
theorem one_blockIndependent (block : Nat) :
    QuaternionBlockIndependent block polyOne :=
  quaternionBlockIndependent_polyOne block

end YMGap.Continuum.QPolyHaarPairedAtFrozenZero

#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenZero.pairedAt_independent_zero
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenZero.frozenFirstAt_independent_zero
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenZero.frozenSecondAt_independent_zero
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenZero.one_blockIndependent
