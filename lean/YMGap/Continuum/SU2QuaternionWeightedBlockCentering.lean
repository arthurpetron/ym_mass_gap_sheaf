/-
# Exact weighted centering on the original quaternion polynomial carrier

For the actual conditional Haar projection P_i, the polynomial
  R = (P_i a)*f - P_i(a*f)
satisfies P_i(a*R)=0 coefficientwise, with every spectator retained.
There is no division by P_i a and no replacement of the original weight.
The exact weighted pairing and quadratic identities also remain polynomial.

This supplies an actual weighted-centered input for local temporal estimates.
It assumes no positivity and proves no spectral or interacting coercivity bound.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.SU2QuaternionWeightedBlockCentering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate

/-- A division-free residual centered against the supplied ORIGINAL weight. -/
def weightedResidual (block : Nat) (a f : RatPoly) : RatPoly :=
  polyAdd (polyMul (project block a) f) (polyNeg (project block (polyMul a f)))

theorem weightedResidual_supported {blocks : Nat} (block : Nat) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (weightedResidual block a f) := by
  apply supported_add (supported_polyMul (project_supported block ha) hf)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact project_supported block (supported_polyMul ha hf) s hs

private theorem project_sub (block : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (project block (polyAdd p (polyNeg q)))
      (polyAdd (project block p) (polyNeg (project block q))) := by
  rw [project_add]
  exact (RatPolyCoeffEqv.refl _).add (project_neg block q)

private theorem sub_self (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg p)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => p)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)

/-- Exact conditional weighted centering; no support or positivity premise. -/
theorem project_weightedResidual_zero (block : Nat) (a f : RatPoly) :
    RatPolyCoeffEqv (project block (polyMul a (weightedResidual block a f))) polyZero := by
  let A := project block a
  let M := project block (polyMul a f)
  have hraw : RatPolyCoeffEqv (polyMul a (weightedResidual block a f))
      (polyAdd (polyMul A (polyMul a f)) (polyNeg (polyMul M a))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.mul (.var 2) (.var 1)) (.neg (.var 3))))
      (.add (.mul (.var 2) (.mul (.var 0) (.var 1)))
        (.neg (.mul (.var 3) (.var 0)))) (by decide)
      (fun | 0 => a | 1 => f | 2 => A | _ => M)
  exact (project_congr block hraw).trans
    ((project_sub block _ _).trans
      (((project_mul_of_independent block A (polyMul a f) (project_independent block a)).add
        (RatPolyCoeffEqv.neg
          ((project_mul_of_independent block M a (project_independent block (polyMul a f))).trans
            (RatPolyCoeffEqv.mul_comm M A)))).trans (sub_self (polyMul A M))))

/-- The residual's pairing with an arbitrary polynomial is an exact weighted
conditional covariance numerator. No spectator is integrated away. -/
theorem weightedResidual_pairing (block : Nat) (a f g : RatPoly) :
    RatPolyCoeffEqv (project block (polyMul a (polyMul (weightedResidual block a f) g)))
      (polyAdd
        (polyMul (project block a) (project block (polyMul a (polyMul f g))))
        (polyNeg (polyMul (project block (polyMul a f)) (project block (polyMul a g))))) := by
  let A := project block a
  let M := project block (polyMul a f)
  have hraw : RatPolyCoeffEqv (polyMul a (polyMul (weightedResidual block a f) g))
      (polyAdd (polyMul A (polyMul a (polyMul f g))) (polyNeg (polyMul M (polyMul a g)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 3) (.var 1)) (.neg (.var 4))) (.var 2)))
      (.add (.mul (.var 3) (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.neg (.mul (.var 4) (.mul (.var 0) (.var 2))))) (by decide)
      (fun | 0 => a | 1 => f | 2 => g | 3 => A | _ => M)
  exact (project_congr block hraw).trans
    ((project_sub block _ _).trans
      ((project_mul_of_independent block A _ (project_independent block a)).add
        (RatPolyCoeffEqv.neg
          (project_mul_of_independent block M _ (project_independent block (polyMul a f))))))

/-- The weighted square is the conditional mass times the same weighted
variance determinant, still coefficientwise and without any reciprocal. -/
theorem weightedResidual_quadratic (block : Nat) (a f : RatPoly) :
    let A := project block a
    let M := project block (polyMul a f)
    RatPolyCoeffEqv
      (project block (polyMul a (polyMul (weightedResidual block a f) (weightedResidual block a f))))
      (polyMul A (polyAdd (polyMul A (project block (polyMul a (polyMul f f))))
        (polyNeg (polyMul M M)))) := by
  let A := project block a
  let M := project block (polyMul a f)
  let r := weightedResidual block a f
  have hcross : RatPolyCoeffEqv (project block (polyMul a (polyMul f r)))
      (polyAdd (polyMul A (project block (polyMul a (polyMul f f))))
        (polyNeg (polyMul M M))) :=
    (project_congr block ((RatPolyCoeffEqv.mul_comm f r).mul_left a)).trans
      (weightedResidual_pairing block a f f)
  have hz : RatPolyCoeffEqv
      (polyMul M (project block (polyMul a r))) polyZero :=
    ((project_weightedResidual_zero block a f).mul_left M).trans
      (RatPolyCoeffEqv.mul_zero_right M)
  have htail : RatPolyCoeffEqv (polyNeg (polyMul M (project block (polyMul a r)))) polyZero :=
    RatPolyCoeffEqv.neg hz
  exact (weightedResidual_pairing block a f r).trans
    (((hcross.mul_left A).add htail).trans (RatPolyCoeffEqv.add_zero _))

end YMGap.Continuum.SU2QuaternionWeightedBlockCentering

#print axioms YMGap.Continuum.SU2QuaternionWeightedBlockCentering.weightedResidual
#print axioms YMGap.Continuum.SU2QuaternionWeightedBlockCentering.weightedResidual_supported
#print axioms YMGap.Continuum.SU2QuaternionWeightedBlockCentering.project_weightedResidual_zero
#print axioms YMGap.Continuum.SU2QuaternionWeightedBlockCentering.weightedResidual_pairing
#print axioms YMGap.Continuum.SU2QuaternionWeightedBlockCentering.weightedResidual_quadratic
