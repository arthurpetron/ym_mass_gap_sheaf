/-
The literal original full-window score wedge.  All input/intermediate
spatial factors remain in halfOpenAction, all surviving coordinates are
shared, and the output is the vacuum-subtracted angular score A db-b dA.
The dyadic specialization uses the original chronological OWN center at n,
not a stationary center or a center newly chosen at n+t.  No sign, noise
upper estimate, relative filtered budget, or changing-family result follows.
-/
import YMGap.Continuum.SU2QuaternionMultiHeadScoreReplica
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionMultiHeadScoreReplica
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add middleRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4DyadicWilsonSquare (paddedSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Original finite window, with its actual terminal input and no final V. -/
def blockWindowWeight (w : Q') (K width n t : Nat) : RatPoly :=
  polyMul (terminalMessage w K width n)
    (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t)

/-- Literal signed source on two complete input histories and ONE output tail. -/
def blockScoreReplica (w : Q') (K width n t block i j : Nat) (f : RatPoly) : RatPoly :=
  scoreReplica (t*(N width)) block i j (blockWindowWeight w K width n t) f

private theorem integral_pin (w : Q') (K width n t : Nat) (f : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)) (polyMul (blockWindowWeight w K width n t) f))
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) f)) := by
  unfold blockWindowWeight
  refine (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun
        | 0 => terminalMessage w K width n
        | 1 => halfOpenAction (N width) (kineticWeight w K width)
            (spatialWeight w K width) t
        | _ => f))).trans ?_
  exact windowMessage_iterate (N width) (kineticWeight w K width)
    (spatialWeight w K width) t (terminalMessage w K width n) f

private theorem mass_pin (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (terminalMessage w K width (n+t)) := by
  have hm : RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (originalBlockTransfer w K width t (terminalMessage w K width n)) :=
    (partialHaarHeads_congr (t*(N width))
      ((RatPolyCoeffEqv.mul_one (terminalMessage w K width n)).symm.mul_right
        (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t))).trans
      (windowMessage_one (N width) (kineticWeight w K width)
        (spatialWeight w K width) t (terminalMessage w K width n))
  have ht : originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
    unfold originalBlockTransfer terminalMessage
    exact (iterateStep_add (N width) (kineticWeight w K width)
      (spatialWeight w K width) n t polyOne).symm
  exact ht ▸ hm

private theorem support_heads {width t : Nat} {f : RatPoly}
    (ht : 1 ≤ t) (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (t*(N width)) f := by
  have hN : N width ≤ t*(N width) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N width) ht
  exact fun term hterm => Nat.le_trans (hf term hterm) (Nat.mul_le_mul_left 4 hN)

/-- Exact original block score.  Center cancellation is integrated first;
the RHS still uses the literal centered transfer at the original depth n. -/
theorem original_block_scoreReplica (w : Q') (K width n t block i j : Nat)
    (f : RatPoly) (c : Q') (ht : 1 ≤ t) (hi : i < 4) (hj : j < 4)
    (hf : SupportedQuaternionBlocks (N width) f) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t
      (polyMul (terminalMessage w K width n) (shifted f c))
    let score := polyAdd (polyMul A (angularDerivative (4*block+i) (4*block+j) b))
      (polyNeg (polyMul b (angularDerivative (4*block+i) (4*block+j) A)))
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)+t*(N width))
      (blockScoreReplica w K width n t block i j f)) (polyAdd score score) := by
  let W := blockWindowWeight w K width n t
  have hA := mass_pin w K width n t
  have hb := integral_pin w K width n t (shifted f c)
  have hc : RatPolyCoeffEqv (conditionalScore (t*(N width)) block i j W (shifted f c))
      (polyAdd
        (polyMul (terminalMessage w K width (n+t))
          (angularDerivative (4*block+i) (4*block+j)
            (originalBlockTransfer w K width t
              (polyMul (terminalMessage w K width n) (shifted f c)))))
        (polyNeg (polyMul
          (originalBlockTransfer w K width t
            (polyMul (terminalMessage w K width n) (shifted f c)))
          (angularDerivative (4*block+i) (4*block+j)
            (terminalMessage w K width (n+t)))))) :=
    (hA.mul (angularDerivative_congr _ _ hb)).add
      (RatPolyCoeffEqv.neg (hb.mul (angularDerivative_congr _ _ hA)))
  exact (scoreReplica_identity (t*(N width)) block i j W f hi hj
    (support_heads ht hf)).trans
      (((conditionalScore_shifted (t*(N width)) block i j W f c).symm.add
        (conditionalScore_shifted (t*(N width)) block i j W f c).symm).trans
          (hc.add hc))

/-- The actual padded Wilson square with its OWN chronological mean at n.
There is no identification of this mean with the mean at n+t. -/
theorem paddedSquare_own_block_scoreReplica {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t scale block i j : Nat) (hwidth : 2^scale < width)
    (ht : 1 ≤ t) (hi : i < 4) (hj : j < 4) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t
      (polyMul (terminalMessage w K width n) (shifted f c))
    let score := polyAdd (polyMul A (angularDerivative (4*block+i) (4*block+j) b))
      (polyNeg (polyMul b (angularDerivative (4*block+i) (4*block+j) A)))
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)+t*(N width))
      (blockScoreReplica w K width n t block i j f)) (polyAdd score score) :=
  original_block_scoreReplica w K width n t block i j _ _ ht hi hj
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)

#print axioms original_block_scoreReplica
#print axioms paddedSquare_own_block_scoreReplica

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica
