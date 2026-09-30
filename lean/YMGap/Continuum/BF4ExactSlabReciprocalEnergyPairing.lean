/-
# Exact reciprocal-corrected conditional energy pairings

The finite pairing loss on the ORIGINAL full-action space is the actual
conditional variance numerator times the finite reciprocal, plus its
normalization defect times the inserted square. Ordered-head Fubini pins
the first term to the two-head replica square with the SAME exterior.
No limiting division, cross-exterior path comparison or coercivity is
asserted here.
-/

import YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional
import YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm

namespace YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.BF4ExactSlabStarReciprocalInverse
open YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional
open YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "D" => normalizer w K extent link hl
local notation "B" => exterior w K extent link hl
local notation "N" p => insertedNormalizer w K extent link hl p
local notation "G" k => headReciprocal hw0 hw1 K extent link hl k
local notation "E" k => polyAdd polyOne (polyNeg (polyMul D (G k)))
local notation "A" => inPlaceApproximation hw0 hw1 K extent hK link

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: ts => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 _) (haar_neg n ts))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_sub_product (n : Nat) (p q r : RatPoly) :
    quaternionHaar n (polyMul (polyAdd p (polyNeg q)) r) ≈
      quaternionHaar n (polyMul p r) + -(quaternionHaar n (polyMul q r)) := by
  rw [polyMul_add_left_exact]
  apply Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
  apply Q'.add_eqv_congr' (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => q | _ => r))) (haar_neg n _)

/-- Actual dense pairing with the literal in-place conditional approximant. -/
theorem approximation_pairing_pin (p : (F).V) (k : Nat) :
    (F).B p (A p k) ≈ quaternionHaar (blocks extent-1)
      (polyMul (polyMul (polyMul (N p.val) (N p.val)) (G k)) B) := by
  let r := reciprocalApproximation hw0 hw1 K extent hK link hl
    (numeratorMap hw0 hw1 K extent hK link hl p) k
  let J := probeMap hw0 hw1 K extent hK link hl r
  have hpin : (F).B p (A p k) ≈ (F).B p J :=
    haar_of_carrier (HaarCarrierEqv.mul_right
      (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
      (HaarCarrierEqv.mul_left p.val
        (approximation_head_pin hw0 hw1 K extent hK link hl p k)))
  exact Q'.eqv_trans _ _ _ hpin
    (Q'.eqv_trans _ _ _ ((F).B_symm p J)
      (Q'.eqv_trans _ _ _ (probeMap_test hw0 hw1 K extent hK link hl r p)
        (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 0))
          (.mul (.mul (.var 0) (.var 0)) (.var 1))
          (by decide) (fun | 0 => N p.val | _ => G k)).mul_right B))))

def lossPolynomial (p : (F).V) (k : Nat) : RatPoly :=
  polyAdd (N (polyMul p.val p.val))
    (polyNeg (polyMul (polyMul (N p.val) (N p.val)) (G k)))

def finiteLoss (p : (F).V) (k : Nat) : Q' :=
  (F).B p p + -((F).B p (A p k))

/-- Every original action factor remains in the exact finite loss. -/
theorem finiteLoss_pairing_pin (p : (F).V) (k : Nat) :
    finiteLoss hw0 hw1 K extent hK link p k ≈
      quaternionHaar (blocks extent-1)
        (polyMul (lossPolynomial hw0 hw1 K extent hK link hl p k) B) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (original_norm_pin hw0 hw1 K extent hK ⟨link,hl⟩ p)
      (Q'.neg_eqv_congr _ _ (approximation_pairing_pin hw0 hw1 K extent hK link hl p k)))
    (Q'.eqv_symm (haar_sub_product _ _ _ _))

/-- The normalization error is kept, with its actual positive sign. -/
theorem lossPolynomial_split (p : (F).V) (k : Nat) :
    RatPolyCoeffEqv (lossPolynomial hw0 hw1 K extent hK link hl p k)
      (polyAdd
        (polyMul (varianceNumerator w K extent link hl p.val) (G k))
        (polyMul (E k) (N (polyMul p.val p.val)))) := by
  exact ((RatPolyCoeffEqv.one_mul _).symm.add (.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 4) (.var 1))
        (.neg (.mul (.mul (.var 2) (.var 2)) (.var 3))))
      (.add
        (.mul (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.var 2) (.var 2)))) (.var 3))
        (.mul (.add (.var 4) (.neg (.mul (.var 0) (.var 3)))) (.var 1)))
      (by decide)
      (fun | 0 => D | 1 => N (polyMul p.val p.val) | 2 => N p.val
           | 3 => G k | _ => polyOne))

def varianceEnergy (p : (F).V) (k : Nat) : Q' :=
  quaternionHaar (blocks extent-1)
    (polyMul (polyMul (varianceNumerator w K extent link hl p.val) (G k)) B)

def normalizationError (p : (F).V) (k : Nat) : Q' :=
  quaternionHaar (blocks extent-1)
    (polyMul (E k) (polyMul (N (polyMul p.val p.val)) B))

/-- Finite loss equals the normalized-variance approximant plus the retained
normalization defect; neither summand is silently discarded. -/
theorem finiteLoss_split (p : (F).V) (k : Nat) :
    finiteLoss hw0 hw1 K extent hK link p k ≈
      varianceEnergy hw0 hw1 K extent hK link hl p k +
        normalizationError hw0 hw1 K extent hK link hl p k := by
  apply Q'.eqv_trans _ _ _ (finiteLoss_pairing_pin hw0 hw1 K extent hK link hl p k)
  apply Q'.eqv_trans _ _ _ (haar_of_coeff
    ((lossPolynomial_split hw0 hw1 K extent hK link hl p k).mul_right B))
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)))

/-- The actual two-head replica square, with the original exterior and
finite reciprocal lifted into those same coordinates. -/
def replicaIntegral (p : (F).V) (k : Nat) : Q' :=
  quaternionHaar ((blocks extent-1)+2)
    (polyMul (replicaEnergy (headWeight w K extent link hl)
      (headInput extent link hl p.val)) (liftBoundary 2 (polyMul (G k) B)))

/-- This duplicates ONLY the selected head link and retains its original
exterior. It is not yet the cross-exterior path insertion identity. -/
theorem replicaIntegral_pin (p : (F).V) (k : Nat) :
    replicaIntegral hw0 hw1 K extent hK link hl p k ≈
      varianceEnergy hw0 hw1 K extent hK link hl p k +
        varianceEnergy hw0 hw1 K extent hK link hl p k := by
  apply Q'.eqv_trans _ _ _ (head_pairing (blocks extent-1) 2 _ _)
  have h := varianceNumerator_replica w K extent link hl p.val
  have ht := haar_of_carrier (HaarCarrierEqv.mul_right (polyMul (G k) B) h)
  apply Q'.eqv_trans _ _ _ ht
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.add_eqv_congr'
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm))

#print axioms approximation_pairing_pin
#print axioms lossPolynomial
#print axioms finiteLoss
#print axioms finiteLoss_pairing_pin
#print axioms lossPolynomial_split
#print axioms varianceEnergy
#print axioms normalizationError
#print axioms finiteLoss_split
#print axioms replicaIntegral
#print axioms replicaIntegral_pin

end YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
