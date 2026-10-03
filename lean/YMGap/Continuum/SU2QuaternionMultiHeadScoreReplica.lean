/-
The signed two-copy score wedge, with every surviving tail coordinate shared.
Its head integral is exactly twice A db-b dA.  A head-supported test has
zero tail derivative; constants in that test cancel after integration.
This is an exact original polynomial identity, not a score/noise upper bound,
positivity assertion, division by A, or changing-family survival estimate.
-/
import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.SU2QuaternionMultiHeadScoreReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (copy copy_mul replica_product)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (supported_upper_independent)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)

/-- The literal signed output score; no inverse or logarithm of the weight. -/
def conditionalScore (heads block i j : Nat) (W f : RatPoly) : RatPoly :=
  let A := partialHaarHeads heads W
  let b := partialHaarHeads heads (polyMul W f)
  polyAdd (polyMul A (angularDerivative (4*block+i) (4*block+j) b))
    (polyNeg (polyMul b (angularDerivative (4*block+i) (4*block+j) A)))

/-- Both head copies retain the SAME output tail and its angular derivative. -/
def scoreReplica (heads block i j : Nat) (W f : RatPoly) : RatPoly :=
  let DW := angularDerivative (4*heads+(4*block+i)) (4*heads+(4*block+j)) W
  polyMul (polyAdd (copy heads f) (polyNeg (liftBoundary heads f)))
    (polyAdd (polyMul (copy heads DW) (liftBoundary heads W))
      (polyNeg (polyMul (copy heads W) (liftBoundary heads DW))))

private def expansion (heads : Nat) (W f DW : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (copy heads (polyMul DW f)) (liftBoundary heads W))
      (polyMul (copy heads W) (liftBoundary heads (polyMul DW f))))
    (polyNeg
      (polyAdd (polyMul (copy heads (polyMul W f)) (liftBoundary heads DW))
        (polyMul (copy heads DW) (liftBoundary heads (polyMul W f)))))

private theorem replica_expansion (heads block i j : Nat) (W f : RatPoly) :
    RatPolyCoeffEqv (scoreReplica heads block i j W f)
      (expansion heads W f
        (angularDerivative (4*heads+(4*block+i)) (4*heads+(4*block+j)) W)) := by
  dsimp only [scoreReplica, expansion]
  simp only [copy_mul, lift_product]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 2) (.neg (.var 3)))
      (.add (.mul (.var 4) (.var 1))
        (.neg (.mul (.var 0) (.var 5)))))
    (.add
      (.add (.mul (.mul (.var 4) (.var 2)) (.var 1))
        (.mul (.var 0) (.mul (.var 5) (.var 3))))
      (.neg
        (.add (.mul (.mul (.var 0) (.var 2)) (.var 5))
          (.mul (.var 4) (.mul (.var 1) (.var 3))))))
    (by decide)
    (fun
      | 0 => copy heads W
      | 1 => liftBoundary heads W
      | 2 => copy heads f
      | 3 => liftBoundary heads f
      | 4 => copy heads (angularDerivative (4*heads+(4*block+i))
          (4*heads+(4*block+j)) W)
      | _ => liftBoundary heads (angularDerivative (4*heads+(4*block+i))
          (4*heads+(4*block+j)) W))

private theorem derivative_weighted (heads block i j : Nat) (W f : RatPoly)
    (hi : i < 4) (hj : j < 4) (hf : SupportedQuaternionBlocks heads f) :
    RatPolyCoeffEqv
      (angularDerivative (4*heads+(4*block+i)) (4*heads+(4*block+j)) (polyMul W f))
      (polyMul (angularDerivative (4*heads+(4*block+i))
        (4*heads+(4*block+j)) W) f) := by
  have hz : RatPolyCoeffEqv
      (angularDerivative (4*heads+(4*block+i)) (4*heads+(4*block+j)) f) polyZero := by
    simpa only [Nat.mul_add, Nat.add_assoc] using
      angularDerivative_blockIndependent_zero hi hj (supported_upper_independent hf block)
  exact (angularDerivative_mul _ _ W f).trans
    (((RatPolyCoeffEqv.refl _).add
      ((hz.mul_left W).trans (RatPolyCoeffEqv.mul_zero_right W))).trans
        (RatPolyCoeffEqv.add_zero _))

/-- Exact signed covariance identity on the entire surviving polynomial carrier.
The input test is supported on the integrated heads, not on an independent tail. -/
theorem scoreReplica_identity (heads block i j : Nat) (W f : RatPoly)
    (hi : i < 4) (hj : j < 4) (hf : SupportedQuaternionBlocks heads f) :
    RatPolyCoeffEqv (partialHaarHeads (heads+heads) (scoreReplica heads block i j W f))
      (polyAdd (conditionalScore heads block i j W f)
        (conditionalScore heads block i j W f)) := by
  let DW := angularDerivative (4*heads+(4*block+i)) (4*heads+(4*block+j)) W
  have hb : RatPolyCoeffEqv
      (angularDerivative (4*block+i) (4*block+j)
        (partialHaarHeads heads (polyMul W f)))
      (partialHaarHeads heads (polyMul DW f)) :=
    (angularDerivative_partialHaarHeads heads _ _ (polyMul W f)).trans
      (partialHaarHeads_congr heads (derivative_weighted heads block i j W f hi hj hf))
  have hA := angularDerivative_partialHaarHeads heads (4*block+i) (4*block+j) W
  refine (partialHaarHeads_congr (heads+heads)
    (replica_expansion heads block i j W f)).trans ?_
  change RatPolyCoeffEqv (partialHaarHeads (heads+heads) (expansion heads W f DW)) _
  dsimp only [expansion]
  rw [partialHaarHeads_add, partialHaarHeads_add]
  have hm := (partialHaarHeads_neg (heads+heads)
    (polyAdd (polyMul (copy heads (polyMul W f)) (liftBoundary heads DW))
      (polyMul (copy heads DW) (liftBoundary heads (polyMul W f))))).trans
    (by
      rw [partialHaarHeads_add]
      exact RatPolyCoeffEqv.neg ((replica_product heads (polyMul W f) DW).add
        (replica_product heads DW (polyMul W f))))
  refine (((replica_product heads (polyMul DW f) W).add
    (replica_product heads W (polyMul DW f))).add hm).trans ?_
  have hr : RatPolyCoeffEqv _
      (polyAdd
        (polyAdd (polyMul (partialHaarHeads heads W) (partialHaarHeads heads (polyMul DW f)))
          (polyNeg (polyMul (partialHaarHeads heads (polyMul W f)) (partialHaarHeads heads DW))))
        (polyAdd (polyMul (partialHaarHeads heads W) (partialHaarHeads heads (polyMul DW f)))
          (polyNeg (polyMul (partialHaarHeads heads (polyMul W f)) (partialHaarHeads heads DW))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 2) (.var 0)) (.mul (.var 0) (.var 2)))
        (.neg (.add (.mul (.var 1) (.var 3)) (.mul (.var 3) (.var 1)))))
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))) (by decide)
      (fun
        | 0 => partialHaarHeads heads W
        | 1 => partialHaarHeads heads (polyMul W f)
        | 2 => partialHaarHeads heads (polyMul DW f)
        | _ => partialHaarHeads heads DW)
  have hc := (hb.symm.mul_left (partialHaarHeads heads W)).add
    (RatPolyCoeffEqv.neg (hA.symm.mul_left (partialHaarHeads heads (polyMul W f))))
  exact hr.trans (hc.add hc)

private theorem product_shift (W f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (polyMul W (shifted f c))
      (polyAdd (polyMul W f) (polySmul (-c) W)) := by
  have hs := ((RatPolyCoeffEqv.one_smul f).add
    (RatPolyCoeffEqv.refl (polySmul (-c) polyOne))).mul_left W
  exact hs.trans ((RatPolyCoeffEqv.mul_add_right W f (polySmul (-c) polyOne)).trans
    ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.polyMul_smul_right (-c) W polyOne).trans
        ((RatPolyCoeffEqv.mul_one W).smul (-c)))))

/-- The actual center cancels in the output score, for every rational center. -/
theorem conditionalScore_shifted (heads block i j : Nat) (W f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (conditionalScore heads block i j W (shifted f c))
      (conditionalScore heads block i j W f) := by
  let A := partialHaarHeads heads W
  let b := partialHaarHeads heads (polyMul W f)
  have hb : RatPolyCoeffEqv (partialHaarHeads heads (polyMul W (shifted f c)))
      (polyAdd b (polySmul (-c) A)) := by
    refine (partialHaarHeads_congr heads (product_shift W f c)).trans ?_
    rw [partialHaarHeads_add]
    exact (RatPolyCoeffEqv.refl b).add (partialHaarHeads_smul heads (-c) W)
  have hd := (angularDerivative_congr (4*block+i) (4*block+j) hb).trans
    ((angularDerivative_add _ _ b (polySmul (-c) A)).trans
      ((RatPolyCoeffEqv.refl _).add (angularDerivative_smul _ _ (-c) A)))
  change RatPolyCoeffEqv (polyAdd (polyMul A _)
    (polyNeg (polyMul _ (angularDerivative (4*block+i) (4*block+j) A)))) _
  refine ((hd.mul_left A).add (RatPolyCoeffEqv.neg (hb.mul_right _))).trans ?_
  have hca (p : RatPoly) : RatPolyCoeffEqv (polySmul (-c) p)
      (polyMul (polySmul (-c) polyOne) p) :=
    ((RatPolyCoeffEqv.polyMul_smul_left (-c) polyOne p).trans
      ((RatPolyCoeffEqv.one_mul p).smul (-c))).symm
  refine ((((RatPolyCoeffEqv.refl _).add (hca _)).mul_left A).add
    (RatPolyCoeffEqv.neg (((RatPolyCoeffEqv.refl b).add (hca A)).mul_right _))).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 2) (.mul (.var 4) (.var 3))))
      (.neg (.mul (.add (.var 1) (.mul (.var 4) (.var 0))) (.var 3))))
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
    (by decide)
    (fun
      | 0 => A
      | 1 => b
      | 2 => angularDerivative (4*block+i) (4*block+j) b
      | 3 => angularDerivative (4*block+i) (4*block+j) A
      | _ => polySmul (-c) polyOne)

/-- Centering the head test leaves the integrated signed replica unchanged. -/
theorem scoreReplica_shifted (heads block i j : Nat) (W f : RatPoly) (c : Q')
    (hi : i < 4) (hj : j < 4) (hf : SupportedQuaternionBlocks heads f) :
    RatPolyCoeffEqv (partialHaarHeads (heads+heads)
      (scoreReplica heads block i j W (shifted f c)))
      (partialHaarHeads (heads+heads) (scoreReplica heads block i j W f)) :=
  (scoreReplica_identity heads block i j W (shifted f c) hi hj
    (shifted_supported hf c)).trans
    (((conditionalScore_shifted heads block i j W f c).add
      (conditionalScore_shifted heads block i j W f c)).trans
      (scoreReplica_identity heads block i j W f hi hj hf).symm)

#print axioms copy_mul
#print axioms scoreReplica_identity
#print axioms conditionalScore_shifted
#print axioms scoreReplica_shifted

end YMGap.Continuum.SU2QuaternionMultiHeadScoreReplica
