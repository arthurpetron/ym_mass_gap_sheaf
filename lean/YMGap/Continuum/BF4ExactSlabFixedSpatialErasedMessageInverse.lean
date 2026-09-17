/-
# Constructed polynomial reciprocals of the actual erased message

For the original terminal weight, d is the one-factor erased message.
The proved window ell<=d<=C has ell>0. Set alpha=1/C,
rho=1-alpha*ell and R=alpha*d-1. Then G_k=alpha*corrector(R,k)
is an explicit polynomial, independent of the erased coordinate, and
  d*G_k + residual(R,k) = 1,
  1-(d*G_k)^2 >= 0,       |d*G_k-1| <= rho^k.
The last two bounds are certificates on the original Haar carrier, not
pointwise substitutes. A rational tolerance has a computed cutoff.

The construction radius depends on w,K,width,n through the full terminal
mass. It is NOT a spatially uniform gap. Its consumer is the actual-marginal
dual estimate, where this approximation error must be removed completely.
No rational function is inserted into the polynomial observable algebra.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow
import YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (a : Q') :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change (-(a*1))*weight []+0 ≈ ((-a)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1))) (Q'.eqv_refl _)

private theorem cap_sub (a b : Q') :
    RatPolyCoeffEqv (cap (a + -b)) (polyAdd (cap a) (polyNeg (cap b))) :=
  (cap_add a (-b)).symm.trans ((RatPolyCoeffEqv.refl _).add (cap_neg b).symm)

private theorem smul_sub (a : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polySmul a (polyAdd p (polyNeg q)))
      (polyAdd (polySmul a p) (polyNeg (polySmul a q))) :=
  (cap_mul_left a _).symm.trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => cap a | 1 => p | _ => q)).trans
      ((cap_mul_left a p).add (RatPolyCoeffEqv.neg (cap_mul_left a q))))

private def normalized (alpha : Q') (d : RatPoly) : RatPoly :=
  polyAdd (polySmul alpha d) (polyNeg polyOne)

private theorem normalized_support {blocks : Nat} {d : RatPoly}
    (hd : SupportedQuaternionBlocks blocks d) (alpha : Q') :
    SupportedQuaternionBlocks blocks (normalized alpha d) :=
  supported_add (support_smul hd alpha) (support_neg (supported_one _))

private def normalizedNegative {blocks : Nat} {d : RatPoly} {alpha C : Q'}
    (ha : (0 : Q') ≤ alpha) (hC : alpha*C ≈ 1)
    (P : Certificate blocks (polyAdd (cap C) (polyNeg d))) :
    Certificate blocks (polyNeg (normalized alpha d)) := by
  have he : RatPolyCoeffEqv (polySmul alpha (polyAdd (cap C) (polyNeg d)))
      (polyAdd polyOne (polyNeg (polySmul alpha d))) :=
    (smul_sub alpha _ _).trans
      (((RatPolyCoeffEqv.smul_assoc alpha C polyOne).trans
        ((RatPolyCoeffEqv.smul_coefficient hC polyOne).trans (RatPolyCoeffEqv.one_smul polyOne))).add (.refl _))
  exact .ofCoeff
    ((coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.neg (.const 1))))
      (.add (.const 1) (.neg (.var 0))) (by decide) (fun _ => polySmul alpha d)).trans he.symm)
    (P.smul alpha ha)

private def normalizedInterval {blocks : Nat} {d : RatPoly} {alpha ell : Q'}
    (hd : SupportedQuaternionBlocks blocks d) (ha : (0 : Q') ≤ alpha)
    (heta : alpha*ell ≤ (1 : Q'))
    (P : Certificate blocks (polyAdd d (polyNeg (cap ell))))
    (Q : Certificate blocks (polyNeg (normalized alpha d))) :
    Interval blocks (normalized alpha d) (1 + -(alpha*ell)) := by
  have h0 := Q'.sub_nonneg_of_le heta
  refine ⟨normalized_support hd alpha, h0, (Certificate.constant blocks _ h0).add Q, ?_⟩
  have he : RatPolyCoeffEqv
      (polyAdd (cap (1 + -(alpha*ell))) (normalized alpha d))
      (polySmul alpha (polyAdd d (polyNeg (cap ell)))) :=
    (((cap_sub 1 (alpha*ell)).trans
      ((RatPolyCoeffEqv.one_smul polyOne).add (.refl _))).add (.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.const 1) (.neg (.var 0))) (.add (.var 1) (.neg (.const 1))))
        (.add (.var 1) (.neg (.var 0))) (by decide)
        (fun | 0 => cap (alpha*ell) | _ => polySmul alpha d)).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
          (RatPolyCoeffEqv.smul_assoc alpha ell polyOne).symm)).trans (smul_sub alpha d (cap ell)).symm))
  exact .ofCoeff he (P.smul alpha ha)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

def scale : Q' := Q'.recipPos (upper hw0 hw1 K width n) (upper_positive hw0 hw1 K width hK n)

theorem scale_positive : (0 : Q') < scale hw0 hw1 K width hK n := Q'.recipPos_pos _ _

private theorem scale_upper : scale hw0 hw1 K width hK n * upper hw0 hw1 K width n ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

private theorem scaled_lower_le_one : scale hw0 hw1 K width hK n * lower hw0 hw1 K width n ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (lower_le_upper hw0 hw1 K width hK n)
      (Q'.le_of_lt (scale_positive hw0 hw1 K width hK n)))
    (Q'.le_of_eqv (scale_upper hw0 hw1 K width hK n))

/-- Finite construction radius; all original parameter dependence is retained. -/
def radius : Q' := 1 + -(scale hw0 hw1 K width hK n * lower hw0 hw1 K width n)

theorem radius_nonnegative : (0 : Q') ≤ radius hw0 hw1 K width hK n :=
  Q'.sub_nonneg_of_le (scaled_lower_le_one hw0 hw1 K width hK n)

theorem radius_lt_one : radius hw0 hw1 K width hK n < (1 : Q') :=
  PositiveContractionResidual.rate_lt_one
    (Q'.mul_pos (scale_positive hw0 hw1 K width hK n) (lower_positive hw0 hw1 K width hK n))

def remainder (i : Nat) : RatPoly := normalized (scale hw0 hw1 K width hK n) (conditionalMessage w K width n i)

theorem remainder_supported (i : Nat) : SupportedQuaternionBlocks (N width) (remainder hw0 hw1 K width hK n i) :=
  normalized_support (conditionalMessage_supported w K width n i) _

theorem remainder_independent (i : Nat) (hi : i ∈ activeBlocks width) :
    QuaternionBlockIndependent i (remainder hw0 hw1 K width hK n i) :=
  quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polySmul _ (conditionalMessage_independent w K width n i hi))
    (quaternionBlockIndependent_polyNeg (quaternionBlockIndependent_polyOne i))

def remainderNegative (i : Nat) (hi : i ∈ activeBlocks width) :
    Certificate (N width) (polyNeg (remainder hw0 hw1 K width hK n i)) :=
  normalizedNegative (Q'.le_of_lt (scale_positive hw0 hw1 K width hK n)) (scale_upper hw0 hw1 K width hK n)
    (upperCertificate hw0 hw1 K width hK n i hi)

def remainderInterval (i : Nat) (hi : i ∈ activeBlocks width) :
    Interval (N width) (remainder hw0 hw1 K width hK n i) (radius hw0 hw1 K width hK n) :=
  normalizedInterval (conditionalMessage_supported w K width n i)
    (Q'.le_of_lt (scale_positive hw0 hw1 K width hK n)) (scaled_lower_le_one hw0 hw1 K width hK n)
    (lowerCertificate hw0 hw1 K width hK n i hi) (remainderNegative hw0 hw1 K width hK n i hi)

/-- An actual finite polynomial, not a rational-function observable. -/
def reciprocal (i k : Nat) : RatPoly :=
  polySmul (scale hw0 hw1 K width hK n) (corrector (remainder hw0 hw1 K width hK n i) k)

theorem reciprocal_supported (i k : Nat) :
    SupportedQuaternionBlocks (N width) (reciprocal hw0 hw1 K width hK n i k) :=
  support_smul (corrector_supported (remainder_supported hw0 hw1 K width hK n i) k) _

theorem reciprocal_independent (i : Nat) (hi : i ∈ activeBlocks width) (k : Nat) :
    QuaternionBlockIndependent i (reciprocal hw0 hw1 K width hK n i k) :=
  quaternionBlockIndependent_polySmul _
    (corrector_independent (remainder_independent hw0 hw1 K width hK n i hi) k)

private theorem multiplier_pin (i k : Nat) :
    RatPolyCoeffEqv (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k))
      (corrected (remainder hw0 hw1 K width hK n i) k) := by
  let a := scale hw0 hw1 K width hK n
  let d := conditionalMessage w K width n i
  let r := remainder hw0 hw1 K width hK n i
  have hp : RatPolyCoeffEqv (polyAdd polyOne r) (polySmul a d) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.add (.var 0) (.neg (.const 1))))
      (.var 0) (by decide) (fun _ => polySmul a d)
  exact (RatPolyCoeffEqv.polyMul_smul_right a d (corrector r k)).trans
    ((RatPolyCoeffEqv.polyMul_smul_left a d (corrector r k)).symm.trans
      (hp.symm.mul (.refl _)))

theorem reciprocal_cancellation (i k : Nat) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k))
        (residual (remainder hw0 hw1 K width hK n i) k)) polyOne :=
  ((multiplier_pin hw0 hw1 K width hK n i k).add (.refl _)).trans (cancellation _ k)

/-- Sharp unit square cap for d*G_k, with no width/depth loss. -/
def multiplierSquareCertificate (i : Nat) (hi : i ∈ activeBlocks width) (k : Nat) :
    Certificate (N width) (polyAdd polyOne (polyNeg (polyMul
      (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k))
      (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k))))) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
    ((multiplier_pin hw0 hw1 K width hK n i k).mul (multiplier_pin hw0 hw1 K width hK n i k))))
    (correctedSquareCertificate (remainderInterval hw0 hw1 K width hK n i hi)
      (remainderNegative hw0 hw1 K width hK n i hi) (Q'.le_of_lt (radius_lt_one hw0 hw1 K width hK n)) k)

def multiplierErrorInterval (i : Nat) (hi : i ∈ activeBlocks width) (k : Nat) :
    Interval (N width) (polyAdd
      (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k)) (polyNeg polyOne))
      ((radius hw0 hw1 K width hK n)^k) :=
  .ofCoeff (supported_add
    (supported_polyMul (conditionalMessage_supported w K width n i) (reciprocal_supported hw0 hw1 K width hK n i k))
    (support_neg (supported_one _)))
    ((multiplier_pin hw0 hw1 K width hK n i k).add (.refl _))
    (correctedErrorInterval (remainderInterval hw0 hw1 K width hK n i hi) k)

/-- Explicit tolerance modulus, not a Prop-level existence witness. -/
def approximationCutoff (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (radius hw0 hw1 K width hK n) 1 epsilon

def approximationInterval (i : Nat) (hi : i ∈ activeBlocks width)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff hw0 hw1 K width hK n epsilon ≤ k) :
    Interval (N width) (polyAdd
      (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k)) (polyNeg polyOne)) epsilon :=
  (multiplierErrorInterval hw0 hw1 K width hK n i hi k).weaken
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound (radius_nonnegative hw0 hw1 K width hK n)
        (radius_lt_one hw0 hw1 K width hK n) Q'.zero_le_one hepsilon k hk))

end YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.scale_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.radius_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.radius_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.remainderNegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.remainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.reciprocal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.reciprocal_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.reciprocal_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.reciprocal_cancellation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.multiplierSquareCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.multiplierErrorInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.approximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse.approximationInterval
