/-
# Algebra of the constructed block inverse approximants

The finite inverse iteration is linear and commutes, coefficientwise, with
right multiplication by a supplied supported polynomial.  These are facts
about the actual detached-background polynomial carrier, not a multiplication
operation on its completed quotient.
-/

import YMGap.Continuum.BF4ExactSlabBlockCompletedInverse

namespace YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "s" => HKConv.divPos 1 (blockUpper w links.length)

/-- Product of two supported source polynomials in the same background
carrier. No quotient multiplication is asserted. -/
def productVector (a t : (G).V) : (G).V :=
  ⟨polyMul a.val t.val, supported_polyMul a.property t.property⟩

theorem productVector_add (a b t : (G).V) :
    (G).veq (productVector hw0 hw1 K extent hK links ((G).add a b) t)
      ((G).add (productVector hw0 hw1 K extent hK links a t)
        (productVector hw0 hw1 K extent hK links b t)) := by
  change RatPolyCoeffEqv (polyMul (polyAdd a.val b.val) t.val)
    (polyAdd (polyMul a.val t.val) (polyMul b.val t.val))
  rw [polyMul_add_left_exact]
  exact RatPolyCoeffEqv.refl _

theorem productVector_smul (c : Q') (a t : (G).V) :
    (G).veq (productVector hw0 hw1 K extent hK links ((G).smul c a) t)
      ((G).smul c (productVector hw0 hw1 K extent hK links a t)) :=
  RatPolyCoeffEqv.polyMul_smul_left c a.val t.val

theorem productVector_sub (a b t : (G).V) :
    (G).veq (productVector hw0 hw1 K extent hK links ((G).sub a b) t)
      ((G).sub (productVector hw0 hw1 K extent hK links a t)
        (productVector hw0 hw1 K extent hK links b t)) := by
  change RatPolyCoeffEqv
    (polyMul (polyAdd a.val (polySmul (-1) b.val)) t.val)
    (polyAdd (polyMul a.val t.val) (polySmul (-1) (polyMul b.val t.val)))
  rw [polyMul_add_left_exact]
  exact RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
    (RatPolyCoeffEqv.polyMul_smul_left (-1) b.val t.val)

theorem normalizerMap_add (a b : (G).V) :
    (G).veq (M ((G).add a b)) ((G).add (M a) (M b)) := by
  change RatPolyCoeffEqv
    (polyMul (polyAdd a.val b.val) (normalizer w K extent links))
    (polyAdd (polyMul a.val (normalizer w K extent links))
      (polyMul b.val (normalizer w K extent links)))
  rw [polyMul_add_left_exact]
  exact RatPolyCoeffEqv.refl _

theorem normalizerMap_product_right (a t : (G).V) :
    (G).veq (M (productVector hw0 hw1 K extent hK links a t))
      (productVector hw0 hw1 K extent hK links (M a) t) := by
  change RatPolyCoeffEqv
    (polyMul (polyMul a.val t.val) (normalizer w K extent links))
    (polyMul (polyMul a.val (normalizer w K extent links)) t.val)
  exact (RatPolyCoeffEqv.mul_assoc a.val t.val
    (normalizer w K extent links)).trans
    (((RatPolyCoeffEqv.mul_comm t.val (normalizer w K extent links)).mul_left a.val).trans
      (RatPolyCoeffEqv.mul_assoc a.val (normalizer w K extent links) t.val).symm)

/-- Every finite inverse approximant commutes with a fixed supported right
factor, at coefficient equivalence on the actual background source. -/
theorem approximateInverse_mul_right (r t : (G).V) : ∀ n : Nat,
    (G).veq (A (productVector hw0 hw1 K extent hK links r t) n)
      (productVector hw0 hw1 K extent hK links (A r n) t)
  | 0 => by
      change RatPolyCoeffEqv (polySmul 0 polyOne)
        (polyMul (polySmul 0 polyOne) t.val)
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans
        (((RatPolyCoeffEqv.zero_smul polyOne).mul_right t.val).trans
          (RatPolyCoeffEqv.mul_zero_left t.val)).symm
  | n+1 => by
      let rt := productVector hw0 hw1 K extent hK links r t
      let ar := A r n
      let art := A rt n
      have hprev : (G).veq art
          (productVector hw0 hw1 K extent hK links ar t) :=
        approximateInverse_mul_right r t n
      have hM : (G).veq (M art)
          (productVector hw0 hw1 K extent hK links (M ar) t) := by
        exact (hprev.mul_right (normalizer w K extent links)).trans
          (normalizerMap_product_right hw0 hw1 K extent hK links ar t)
      have hres : (G).veq ((G).sub rt (M art))
          (productVector hw0 hw1 K extent hK links ((G).sub r (M ar)) t) := by
        exact ((G).add_congr ((G).veq_refl rt) ((G).neg_congr hM)).trans
          (productVector_sub hw0 hw1 K extent hK links r (M ar) t).symm
      have hscaled : (G).veq ((G).smul s ((G).sub rt (M art)))
          (productVector hw0 hw1 K extent hK links
            ((G).smul s ((G).sub r (M ar))) t) :=
        ((G).smul_congr s hres).trans
          (productVector_smul hw0 hw1 K extent hK links s ((G).sub r (M ar)) t).symm
      exact ((G).add_congr hprev hscaled).trans
        (productVector_add hw0 hw1 K extent hK links ar
          ((G).smul s ((G).sub r (M ar))) t).symm

private theorem smul_add_vector (c : Q') (a b : (G).V) :
    (G).veq ((G).smul c ((G).add a b))
      ((G).add ((G).smul c a) ((G).smul c b)) :=
  RatPolyCoeffEqv.smul_add c a.val b.val

/-- The finite inverse iteration is additive; the result is a source-carrier
equivalence, not a completed inverse operator on arbitrary quotient vectors. -/
theorem approximateInverse_add (r t : (G).V) : ∀ n : Nat,
    (G).veq (A ((G).add r t) n) ((G).add (A r n) (A t n))
  | 0 => (G).veq_symm ((G).zero_add (G).zero)
  | n+1 => by
      let ar := A r n
      let ta := A t n
      let art := A ((G).add r t) n
      have hprev : (G).veq art ((G).add ar ta) :=
        approximateInverse_add r t n
      have hM : (G).veq (M art) ((G).add (M ar) (M ta)) := by
        exact (hprev.mul_right (normalizer w K extent links)).trans
          (normalizerMap_add hw0 hw1 K extent hK links ar ta)
      have hres : (G).veq
          ((G).sub ((G).add r t) (M art))
          ((G).add ((G).sub r (M ar)) ((G).sub t (M ta))) := by
        exact ((G).add_congr ((G).veq_refl ((G).add r t))
          ((G).neg_congr hM)).trans
          ((G).sub_sub_distrib r t (M ar) (M ta))
      have hscaled : (G).veq
          ((G).smul s ((G).sub ((G).add r t) (M art)))
          ((G).add ((G).smul s ((G).sub r (M ar)))
            ((G).smul s ((G).sub t (M ta)))) :=
        ((G).smul_congr s hres).trans
          (smul_add_vector hw0 hw1 K extent hK links s _ _)
      exact ((G).add_congr hprev hscaled).trans
        ((G).add_add_add_comm ar ta
          ((G).smul s ((G).sub r (M ar)))
          ((G).smul s ((G).sub t (M ta))))

private theorem smul_sub_vector (c : Q') (a b : (G).V) :
    (G).veq ((G).smul c ((G).sub a b))
      ((G).sub ((G).smul c a) ((G).smul c b)) := by
  change RatPolyCoeffEqv
    (polySmul c (polyAdd a.val (polySmul (-1) b.val)))
    (polyAdd (polySmul c a.val) (polySmul (-1) (polySmul c b.val)))
  refine (RatPolyCoeffEqv.smul_add c a.val (polySmul (-1) b.val)).trans ?_
  apply RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
  exact (RatPolyCoeffEqv.smul_assoc c (-1) b.val).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) b.val).trans
      (RatPolyCoeffEqv.smul_assoc (-1) c b.val).symm)

private theorem sub_sub_rearrange (a b c d : (G).V) :
    (G).veq ((G).sub ((G).sub a b) ((G).sub c d))
      ((G).sub ((G).sub a c) ((G).sub b d)) := by
  exact ((G).add_congr ((G).veq_refl ((G).sub a b))
    ((G).neg_add_distrib c ((G).neg d))).trans
    (((G).add_add_add_comm a ((G).neg b) ((G).neg c) ((G).neg ((G).neg d))).trans
      ((G).add_congr ((G).veq_refl ((G).sub a c))
        ((G).veq_symm ((G).neg_add_distrib b ((G).neg d)))))

/-- Subtraction compatibility needed for the explicit covariance numerator. -/
theorem approximateInverse_sub (r t : (G).V) : ∀ n : Nat,
    (G).veq (A ((G).sub r t) n) ((G).sub (A r n) (A t n))
  | 0 => by
      change RatPolyCoeffEqv (polySmul 0 polyOne)
        (polyAdd (polySmul 0 polyOne) (polySmul (-1) (polySmul 0 polyOne)))
      have hright : RatPolyCoeffEqv
          (polyAdd (polySmul 0 polyOne) (polySmul (-1) (polySmul 0 polyOne)))
          polyZero :=
        (((RatPolyCoeffEqv.zero_smul polyOne).add
          ((RatPolyCoeffEqv.zero_smul polyOne).smul (-1))).trans
          ((RatPolyCoeffEqv.refl polyZero).add
            (RatPolyCoeffEqv.smul_zero (-1)))).trans
          (RatPolyCoeffEqv.zero_add polyZero)
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans hright.symm
  | n+1 => by
      let ar := A r n
      let ta := A t n
      let art := A ((G).sub r t) n
      have hprev : (G).veq art ((G).sub ar ta) :=
        approximateInverse_sub r t n
      have hM : (G).veq (M art) ((G).sub (M ar) (M ta)) := by
        exact (hprev.mul_right (normalizer w K extent links)).trans
          (normalizerMap_sub hw0 hw1 K extent hK links ar ta)
      have hres : (G).veq
          ((G).sub ((G).sub r t) (M art))
          ((G).sub ((G).sub r (M ar)) ((G).sub t (M ta))) := by
        exact ((G).add_congr ((G).veq_refl ((G).sub r t))
          ((G).neg_congr hM)).trans
          (sub_sub_rearrange hw0 hw1 K extent hK links r t (M ar) (M ta))
      have hscaled : (G).veq
          ((G).smul s ((G).sub ((G).sub r t) (M art)))
          ((G).sub ((G).smul s ((G).sub r (M ar)))
            ((G).smul s ((G).sub t (M ta)))) :=
        ((G).smul_congr s hres).trans
          (smul_sub_vector hw0 hw1 K extent hK links s _ _)
      exact ((G).add_congr hprev hscaled).trans
        ((G).sub_sub_distrib ar
          ((G).smul s ((G).sub r (M ar))) ta
          ((G).smul s ((G).sub t (M ta)))).symm

#print axioms productVector
#print axioms productVector_add
#print axioms productVector_smul
#print axioms productVector_sub
#print axioms normalizerMap_add
#print axioms normalizerMap_product_right
#print axioms approximateInverse_mul_right
#print axioms approximateInverse_add
#print axioms approximateInverse_sub

end YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
