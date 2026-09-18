/-
# One-step positivity of the SAME intrinsic Wilson form

The actual signed source is pinned to the balanced bond-reflected window.
Its numerator is the original interacting positive quadratic; its original
positive partition is unchanged. Positivity passes through the already
constructed joint time/cutoff limit and then the spatial limit. The extra
slice in the displayed intrinsic chart is removed ONLY at the joint-limit
level by WilsonOddWindow.oddJointLimits_oneStep_converge.

This supplies one-step positivity on the current small-nome SU(2) intrinsic
Wilson form, not a new state or an assumed abstract form. The completed
carrier is a separate consumer. No strict estimate, physical spacing limit,
continuous-time Hamiltonian or continuum QFT theorem is proved here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSourceReversal
import YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSourceReversal
open YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence (windowRatio_padded_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSliceReversal
open YMGap.Continuum.SU2QuaternionHeadWindowReversal (lift_padded)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem support_mono {a b : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks a p) (hab : a ≤ b) : SupportedQuaternionBlocks b p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hab)

/-- Complete source pin before Haar integration: no unsupported variables
are removed by the common-padding congruence. -/
theorem oddWindowRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {width : Nat} (hK : headCutoff w ≤ K) (t R : Nat)
    (e : WindowExpression width) (he : Within R e) :
    (0 : Q') ≤ windowRatio hw0 hw1 K width hK t (2*R+1) t
      (sourcePolynomial (oddPair R e)) := by
  have hp := source_supported R e he
  have hr := reversePolynomial_supported (N width) R (sourcePolynomial e)
  have hrr := source_supported R (reverse R e) (reverse_within R e)
  have hsize : (R+1)*(N width)+(R+1)*(N width)=(2*R+1+1)*(N width) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hupper : SupportedQuaternionBlocks ((2*R+1+1)*(N width))
      (liftBoundary ((R+1)*(N width)) (reversePolynomial (N width) R (sourcePolynomial e))) := by
    simpa only [hsize] using lift_supported hr ((R+1)*(N width))
  have hlower := support_mono hp (Nat.mul_le_mul_right (N width) (by omega : R+1 ≤ 2*R+1+1))
  have hsource : PaddedPolynomialCoeffEqv ((2*R+1+1)*(N width))
      (sourcePolynomial (oddPair R e))
      (polyMul (sourcePolynomial e)
        (liftBoundary ((R+1)*(N width)) (reversePolynomial (N width) R (sourcePolynomial e)))) :=
    (oddPair_source _ R e).trans ((PaddedPolynomialCoeffEqv.refl _ (sourcePolynomial e)).mul
      (lift_padded ((R+1)*(N width)) hrr hr (source_reverse R e he)))
  have hpin := windowRatio_padded_congr hw0 hw1 K width hK t (2*R+1) t
    (source_supported (2*R+1) (oddPair R e) (oddPair_within R e he))
    (supported_polyMul hlower hupper) hsource
  exact Q'.le_trans' _ _ _ (reversed_windowRatio_nonnegative hw0 hw1 K width hK t R
    (sourcePolynomial e) hp) (Q'.ge_of_eqv hpin)

/-- The original finiteValue, with its unchanged full action and partition. -/
theorem originalOddScalar_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (R : Nat) (e : WindowExpression width) (he : Within R e)
    (stage t : Nat) :
    (0 : Q') ≤ originalWindowScalar hw0 hw1 (2*R+1) (oddPair R e) stage t t :=
  Q'.le_trans' _ _ _
    (oddWindowRatio_nonnegative hw0 hw1 (headCutoff w+stage) (Nat.le_add_right _ _) t R e he)
    (Q'.ge_of_eqv (originalWindowScalar_pin hw0 hw1 (2*R+1) (oddPair R e)
      (oddPair_within R e he) stage t t))

/-- Both heat cutoff and balanced external time depths recede through
the previously constructed explicit original joint Cauchy sequence. -/
theorem originalJoint_odd_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (R : Nat) (e : WindowExpression width) (he : Within R e) :
    leEv (ofQ' 0) (originalJointLimit hw0 hw1 (2*R+1) (oddPair R e)
      (oddPair_within R e he)) := by
  let c := originalJointCauchy hw0 hw1 (2*R+1) (oddPair R e) (oddPair_within R e he)
  exact leEv_ofQ'_of_approx_ge (fun k => originalOddScalar_nonnegative hw0 hw1 R e he
    (QMhat _ c k) (QMhat _ c k))

/-- One-step positivity of the CURRENT intrinsic Wilson form, retaining
the actual small-nome guards used to construct its spatial limit. -/
theorem intrinsicForm_oneStep_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (x : IntrinsicExpression base) :
    leEv (ofQ' 0) (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance 1 x)) := by
  apply leEv_of_convergesTo_le (convergesTo_const (ofQ' 0))
    (oddJointLimits_oneStep_converge hw0 hw1 hsmall hd hs hb x)
  intro r
  simpa only [centered_oddPair] using originalJoint_odd_nonnegative hw0 hw1 x.radius
    (centeredExpression r x.expression) ((centered_within r x.radius _).mpr x.within)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive.oddWindowRatio_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive.originalOddScalar_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive.originalJoint_odd_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive.intrinsicForm_oneStep_nonnegative
