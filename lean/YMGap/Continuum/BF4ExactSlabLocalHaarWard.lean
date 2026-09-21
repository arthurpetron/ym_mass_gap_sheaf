/-
# Exact selected-link Ward identity for the original finite slab action

Move an actual physical link to the first quaternion block with the existing
Haar-preserving transposition. A is its incident heat product and R is the
ENTIRE complementary heat product. The original numerator is pinned to this
same R*A weight. Only A is differentiated: independence of R at the selected
link is proved by the existing link-locality theorem, not presumed.

The identity holds at every finite heat cutoff and rational nome. There is
no estimate uniform in nome or spacing, no change of measure, no conditional
normalizer inverse, and no assertion of a transfer or Hamiltonian gap.
-/

import YMGap.Continuum.SU2QuaternionHaarAngularIBP
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.BF4ExactSlabLocalHaarWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

variable (w : Q') (K extent : Nat) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)

/-- SAME original action and numerator, in the selected-link coordinate
frame. Every factor of the complement is still present. -/
theorem fullAction_pair_pin (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p) :
    quaternionHaar (blocks extent)
      (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))) ≈
    quaternionHaar (blocks extent)
      (polyMul R (polyMul A (reindexQuaternionPolynomial swap p))) := by
  have hc : RatPolyCoeffEqv
      (polyMul p (polyMul (incidentHeat w K extent link) (complementHeat w K extent link)))
      (polyMul (complementHeat w K extent link) (polyMul (incidentHeat w K extent link) p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 1) (.var 0))) (by decide)
      (fun n => if n = 0 then p else if n = 1 then incidentHeat w K extent link else complementHeat w K extent link)
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (heatProduct_partition w K extent link)).trans hc)) ?_
  have hs := quaternionHaar_reindex swap
    (polyMul (complementHeat w K extent link) (polyMul (incidentHeat w K extent link) p))
    (supported_polyMul (complementHeat_supported w K extent link)
      (supported_polyMul (incidentHeat_supported w K extent link) hp))
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul] at hs
  exact Q'.eqv_symm hs

/-- The complete complement has zero derivative in the actual selected
link. Dependence on all OTHER shared links is allowed. -/
theorem complement_angular_zero {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (angularDerivative i j R) polyZero :=
  angularDerivative_independent_zero hi hj R (complementHeat_headIndependent w K extent link hl)

/-- Exact local weighted Haar identity for any polynomial test in the
selected-link frame. No incident factor or complementary interaction is
deleted. Positivity is not needed for this finite identity. -/
theorem fullAction_local_ward {i j : Nat} (hi : i < 4) (hj : j < 4) (f : RatPoly) :
    quaternionHaar (blocks extent)
      (polyMul R
        (polyAdd (polyMul (angularDerivative i j A) f)
          (polyMul A (angularDerivative i j f)))) ≈ 0 := by
  have hb := List.idxOf_lt_length_of_mem hl
  have hn : blocks extent - 1 + 1 = blocks extent := by dsimp only [blocks]; omega
  have h := quaternionHaar_retained_background (blocks extent - 1) hi hj R A f
    (complementHeat_headIndependent w K extent link hl)
  rw [hn] at h
  exact h

/-- A polynomial score requiring no inverse of the incident heat weight.
Its extra factor A is local; the complementary action never enters it. -/
def localScore (i j : Nat) (g : RatPoly) : RatPoly :=
  polyAdd (polyMul A (angularDerivative i j g))
    (polySmul 2 (polyMul (angularDerivative i j A) g))

/-- A mean-zero dual-test identity under the SAME full R*A weight.
It follows by differentiating A^2*g*f*R. The remaining response and score
norm must still be estimated; this theorem makes no such estimate. -/
theorem fullAction_score_identity {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) :
    quaternionHaar (blocks extent)
      (polyMul R (polyMul A
        (polyAdd (polyMul f (localScore w K extent link hl i j g))
          (polyMul (polyMul A g) (angularDerivative i j f))))) ≈ 0 := by
  have hd : RatPolyCoeffEqv (angularDerivative i j (polyMul A (polyMul g f)))
      (polyAdd (polyMul (angularDerivative i j A) (polyMul g f))
        (polyMul A (polyAdd (polyMul (angularDerivative i j g) f)
          (polyMul g (angularDerivative i j f))))) :=
    (angularDerivative_mul i j A (polyMul g f)).trans
      ((RatPolyCoeffEqv.refl _).add ((angularDerivative_mul i j g f).mul_left A))
  have hc : RatPolyCoeffEqv
      (polyAdd (polyMul (angularDerivative i j A) (polyMul A (polyMul g f)))
        (polyMul A
          (polyAdd (polyMul (angularDerivative i j A) (polyMul g f))
            (polyMul A (polyAdd (polyMul (angularDerivative i j g) f)
              (polyMul g (angularDerivative i j f)))))))
      (polyMul A
        (polyAdd (polyMul f (localScore w K extent link hl i j g))
          (polyMul (polyMul A g) (angularDerivative i j f)))) := by
    let env : Nat → RatPoly := fun n =>
      if n = 0 then A else if n = 1 then angularDerivative i j A
      else if n = 2 then g else if n = 3 then angularDerivative i j g
      else if n = 4 then f else angularDerivative i j f
    have h := coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 4))))
        (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 2) (.var 4)))
          (.mul (.var 0) (.add (.mul (.var 3) (.var 4)) (.mul (.var 2) (.var 5)))))))
      (.mul (.var 0) (.add
        (.mul (.var 4) (.add (.mul (.var 0) (.var 3))
          (.mul (.const 2) (.mul (.var 1) (.var 2)))))
        (.mul (.mul (.var 0) (.var 2)) (.var 5)))) (by decide) env
    -- The normalizer represents a scalar as multiplication by a constant
    -- polynomial; identify it with the existing rational smul operation.
    exact h.trans ((RatPolyCoeffEqv.refl A).mul
      (((RatPolyCoeffEqv.refl f).mul
        ((RatPolyCoeffEqv.refl _).add
          (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left 2 _))).add
        (RatPolyCoeffEqv.refl _)))
  have he := (((RatPolyCoeffEqv.refl _).add (hd.mul_left A)).trans hc).mul_left R
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he.symm)
    (fullAction_local_ward w K extent link hl hi hj (polyMul A (polyMul g f)))

/-- The constructed local score has exactly zero mean under the complete
finite action in the selected-link frame. -/
theorem fullAction_score_mean_zero {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g : RatPoly) :
    quaternionHaar (blocks extent)
      (polyMul R (polyMul A (localScore w K extent link hl i j g))) ≈ 0 := by
  have hz := angularDerivative_independent_zero hi hj polyOne (hasQuaternionBlockDegree_one 0)
  have he : RatPolyCoeffEqv
      (polyAdd (polyMul polyOne (localScore w K extent link hl i j g))
        (polyMul (polyMul A g) (angularDerivative i j polyOne)))
      (localScore w K extent link hl i j g) :=
    ((RatPolyCoeffEqv.one_mul _).add
      ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))).trans
      (RatPolyCoeffEqv.add_zero _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((he.mul_left A).mul_left R).symm)
    (fullAction_score_identity w K extent link hl hi hj g polyOne)

end YMGap.Continuum.BF4ExactSlabLocalHaarWard

#print axioms YMGap.Continuum.BF4ExactSlabLocalHaarWard.fullAction_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalHaarWard.complement_angular_zero
#print axioms YMGap.Continuum.BF4ExactSlabLocalHaarWard.fullAction_local_ward
#print axioms YMGap.Continuum.BF4ExactSlabLocalHaarWard.fullAction_score_identity
#print axioms YMGap.Continuum.BF4ExactSlabLocalHaarWard.fullAction_score_mean_zero
