/-
# Local paired-score moment on the SAME last-step action

A density independent of the selected upper output block lets the three
paired derivatives of q*P differentiate P
alone. A coefficient pin q*P=W then identifies its residual moment with the
already checked original two-source score. Frozen output coefficients pull
through the head integral only AFTER each derivative is evaluated.

The factor pin is structural data for the actual original density and kinetic
product. This leaf supplies no factorization c=a*phi, conditional Hessian sign,
source-error bound, or physical estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
import YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepPairedResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
  (lastStepAction paired_score_integral_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (angularDerivative_blockIndependent_zero partialHaarHeads_add)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
  (partialHaarHeads_congr partialHaarHeads_mul_lift)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (pairedScorePlus)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem plane_product_pin (width s j k : Nat) (hj : j < 4) (hk : k < 4)
    (q P : RatPoly) (hq : QuaternionBlockIndependent (N width+s) q) :
    RatPolyCoeffEqv
      (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) (polyMul q P))
      (polyMul q (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) P)) := by
  have hz : RatPolyCoeffEqv
      (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) q) polyZero := by
    exact angularDerivative_blockIndependent_zero hj hk hq
  have hrest : RatPolyCoeffEqv
      (polyAdd (polyMul
        (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) q) P)
        (polyMul q (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) P)))
      (polyMul q (angularDerivative (4*(N width+s)+j) (4*(N width+s)+k) P)) :=
    (((hz.mul_right P).trans (RatPolyCoeffEqv.mul_zero_left P)).add
      (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)
  exact (angularDerivative_mul _ _ q P).trans hrest

private theorem paired_product_pin (width s : Nat) (i : Fin 3)
    (q P : RatPoly) (hq : QuaternionBlockIndependent (N width+s) q) :
    RatPolyCoeffEqv
      (pairedDerivativeAt (N width+s) i (polyMul q P))
      (polyMul q (pairedDerivativeAt (N width+s) i P)) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    change RatPolyCoeffEqv
      (polyAdd (blockAngularDerivative (N width+s) 0 1 (polyMul q P))
        (blockAngularDerivative (N width+s) 2 3 (polyMul q P)))
      (polyMul q (polyAdd (blockAngularDerivative (N width+s) 0 1 P)
        (blockAngularDerivative (N width+s) 2 3 P)))
    exact ((plane_product_pin width s 0 1 (by decide) (by decide) q P hq).add
      (plane_product_pin width s 2 3 (by decide) (by decide) q P hq)).trans
        (RatPolyCoeffEqv.mul_add_right q _ _).symm
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      change RatPolyCoeffEqv
        (polyAdd (blockAngularDerivative (N width+s) 0 2 (polyMul q P))
          (polyNeg (blockAngularDerivative (N width+s) 1 3 (polyMul q P))))
        (polyMul q (polyAdd (blockAngularDerivative (N width+s) 0 2 P)
          (polyNeg (blockAngularDerivative (N width+s) 1 3 P))))
      refine ((plane_product_pin width s 0 2 (by decide) (by decide) q P hq).add
        (RatPolyCoeffEqv.neg
          (plane_product_pin width s 1 3 (by decide) (by decide) q P hq))).trans ?_
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => q
          | 1 => blockAngularDerivative (N width+s) 0 2 P
          | _ => blockAngularDerivative (N width+s) 1 3 P)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      change RatPolyCoeffEqv
        (polyAdd (blockAngularDerivative (N width+s) 0 3 (polyMul q P))
          (blockAngularDerivative (N width+s) 1 2 (polyMul q P)))
        (polyMul q (polyAdd (blockAngularDerivative (N width+s) 0 3 P)
          (blockAngularDerivative (N width+s) 1 2 P)))
      exact ((plane_product_pin width s 0 3 (by decide) (by decide) q P hq).add
        (plane_product_pin width s 1 2 (by decide) (by decide) q P hq)).trans
          (RatPolyCoeffEqv.mul_add_right q _ _).symm

private theorem paired_congr (block : Nat) (i : Fin 3) {P Q : RatPoly}
    (h : RatPolyCoeffEqv P Q) :
    RatPolyCoeffEqv (pairedDerivativeAt block i P) (pairedDerivativeAt block i Q) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      exact (angularDerivative_congr _ _ h).add
        (RatPolyCoeffEqv.neg (angularDerivative_congr _ _ h))
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)

/-- The local density and the actual residual yield the SAME two-source
paired output score, provided their product is the literal full action. -/
theorem local_paired_score_integral_pin (w : Q') (K width s : Nat) (i : Fin 3)
    (q P : RatPoly) (hq : QuaternionBlockIndependent (N width+s) q)
    (hfactor : RatPolyCoeffEqv (polyMul q P) (lastStepAction w K width))
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (polyMul q (pairedDerivativeAt (N width+s) i P))
        (lastStepPairedResidual w K width a c)))
      (pairedScorePlus s (transferStep w K width a) (transferStep w K width c) i) := by
  let X := lastStepPairedResidual w K width a c
  have h : RatPolyCoeffEqv
      (polyMul q (pairedDerivativeAt (N width+s) i P))
      (pairedDerivativeAt (N width+s) i (lastStepAction w K width)) :=
    (paired_product_pin width s i q P hq).symm.trans
      (paired_congr (N width+s) i hfactor)
  exact (partialHaarHeads_congr (N width) (h.mul_right X)).trans
    (paired_score_integral_pin w K width s i ha hc)

private theorem integrate_threeSum (heads : Nat) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads heads (threeSum f))
      (threeSum (fun i => partialHaarHeads heads (f i))) := by
  unfold threeSum
  rw [partialHaarHeads_add, partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

/-- A frozen output coefficient is pulled past the same head integration;
it is never differentiated. -/
private theorem frozen_term_integral_pin (w : Q') (K width s : Nat) (i : Fin 3)
    (q P : RatPoly) (hq : QuaternionBlockIndependent (N width+s) q)
    (hfactor : RatPolyCoeffEqv (polyMul q P) (lastStepAction w K width))
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (u : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (polyMul q (polyMul (liftBoundary (N width) u)
          (pairedDerivativeAt (N width+s) i P)))
        (lastStepPairedResidual w K width a c)))
      (polyMul u (pairedScorePlus s
        (transferStep w K width a) (transferStep w K width c) i)) := by
  let D := pairedDerivativeAt (N width+s) i P
  let X := lastStepPairedResidual w K width a c
  have hmove : RatPolyCoeffEqv
      (polyMul (polyMul q (polyMul (liftBoundary (N width) u) D)) X)
      (polyMul (polyMul (polyMul q D) X) (liftBoundary (N width) u)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.var 1))
      (by decide) (fun
        | 0 => q | 1 => liftBoundary (N width) u | 2 => D | _ => X)
  exact (partialHaarHeads_congr (N width) hmove).trans
    ((partialHaarHeads_mul_lift (N width) (polyMul (polyMul q D) X) u).trans
      ((local_paired_score_integral_pin w K width s i q P hq hfactor ha hc).mul_right u |>.trans
        (RatPolyCoeffEqv.mul_comm _ u)))

/-- The actual three-component frozen first jet has exactly the output-score
moment under the unchanged original action and paired residual. -/
theorem local_frozen_score_integral_pin (w : Q') (K width s : Nat)
    (q P : RatPoly) (hq : QuaternionBlockIndependent (N width+s) q)
    (hfactor : RatPolyCoeffEqv (polyMul q P) (lastStepAction w K width))
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (polyMul q (firstJet (fun i => liftBoundary (N width) (u i))
          (fun i => pairedDerivativeAt (N width+s) i P)))
        (lastStepPairedResidual w K width a c)))
      (firstJet u (pairedScorePlus s
        (transferStep w K width a) (transferStep w K width c))) := by
  let D := fun i => pairedDerivativeAt (N width+s) i P
  let X := lastStepPairedResidual w K width a c
  have hsplit : RatPolyCoeffEqv
      (polyMul (polyMul q (firstJet (fun i => liftBoundary (N width) (u i)) D)) X)
      (threeSum (fun i => polyMul
        (polyMul q (polyMul (liftBoundary (N width) (u i)) (D i))) X)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0)
        (.add (.mul (.var 1) (.var 2))
          (.add (.mul (.var 3) (.var 4)) (.mul (.var 5) (.var 6))))) (.var 7))
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 7))
        (.add (.mul (.mul (.var 0) (.mul (.var 3) (.var 4))) (.var 7))
          (.mul (.mul (.var 0) (.mul (.var 5) (.var 6))) (.var 7))))
      (by decide) (fun
        | 0 => q | 1 => liftBoundary (N width) (u 0) | 2 => D 0
        | 3 => liftBoundary (N width) (u 1) | 4 => D 1
        | 5 => liftBoundary (N width) (u 2) | 6 => D 2 | _ => X)
  exact (partialHaarHeads_congr (N width) hsplit).trans
    ((integrate_threeSum (N width) _).trans
      ((frozen_term_integral_pin w K width s 0 q P hq hfactor ha hc (u 0)).add
        ((frozen_term_integral_pin w K width s 1 q P hq hfactor ha hc (u 1)).add
          (frozen_term_integral_pin w K width s 2 q P hq hfactor ha hc (u 2)))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin.local_paired_score_integral_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin.local_frozen_score_integral_pin
