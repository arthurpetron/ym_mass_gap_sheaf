/-
# Lossless integrated order reflection through a positive Haar window

Finite positive reciprocal polynomials remove an unwanted positive multiplier
from a Haar expectation, with an explicit geometric error. Sending this error
to zero uses rational Archimedean order only. The theorem does NOT claim that
the uncancelled polynomial has a finite sum-of-squares certificate.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

local infix:50 " ≈ " => Q'.eqv

/-- The geometric corrector is genuinely nonnegative when `-R` is; this is
stronger than its two-sided interval estimate. -/
def correctorCertificate {blocks : Nat} {R : RatPoly}
    (N : Certificate blocks (polyNeg R)) :
    (k : Nat) → Certificate blocks (corrector R k)
  | 0 => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | k+1 => (Certificate.one blocks).add (N.mul (correctorCertificate N k))

/-- Every finite positive-window reciprocal is a certified nonnegative
polynomial. -/
def reciprocalCertificate {blocks : Nat} {p : RatPoly} {u : Q'}
    (hu : (0 : Q') < u)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) (k : Nat) :
    Certificate blocks (reciprocal p u hu k) := by
  unfold reciprocal
  exact (correctorCertificate (remainderNegative hu U) k).smul
    (scale u hu) (Q'.le_of_lt (scale_positive u hu))

/-- The corrected insertion is nonnegative whenever the original windowed
insertion is.  This is the finite positivity input for scalar order
reflection; it does not claim certificate-level division. -/
def correctedInsertionCertificate {blocks : Nat} {background p q : RatPoly}
    {u : Q'} (B : Certificate blocks background) (hu : (0 : Q') < u)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (PQ : Certificate blocks (polyMul p q)) (k : Nat) :
    Certificate blocks
      (polyMul background
        (polyMul (reciprocal p u hu k) (polyMul p q))) :=
  B.mul ((reciprocalCertificate hu U k).mul PQ)

/-- The explicit cutoff inherited from the existing positive-window inverse.
At or beyond this stage its multiplier error has the requested tolerance. -/
def reflectionCutoff (ell u : Q') (hu : (0 : Q') < u)
    (epsilon : Q') : Nat := approximationCutoff ell u hu epsilon

/-- Finite loss is only the inverse approximation error, not an inverse-floor
factor in the final order conclusion. All background variables are retained. -/
theorem reflection_with_error {blocks : Nat} {background p q : RatPoly}
    {ell u c : Q'} (hp : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks p)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (B : Certificate blocks background) (Q : Interval blocks q c)
    (PQ : Certificate blocks (polyMul p q))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : reflectionCutoff ell u hu epsilon ≤ k) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul background q) +
      (epsilon*c)*quaternionHaar blocks background := by
  let g := reciprocal p u hu k
  let e := polyAdd (polyMul p g) (polyNeg polyOne)
  have hpos := (correctedInsertionCertificate B hu U PQ k).haar_nonnegative
  have herr := ((approximationInterval hp hell hu hle L U epsilon hepsilon k hk).mul Q).weighted_haar_bound B
  have he : quaternionHaar blocks (polyMul background (polyMul g (polyMul p q))) ≈
      quaternionHaar blocks (polyMul background q) +
        quaternionHaar blocks (polyMul background (polyMul e q)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.var 3))
        (.mul (.var 0) (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.const 1))) (.var 3))))
      (by decide) (fun | 0 => background | 1 => g | 2 => p | _ => q)))
      (quaternionHaar_append blocks _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) herr))

private theorem cost_plus_one_pos (cost : Q') (hc : (0 : Q') ≤ cost) :
    (0 : Q') < cost+1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 cost hc)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- A computed inner tolerance paying an arbitrary nonnegative error cost. -/
def costTolerance (cost : Q') (hc : (0 : Q') ≤ cost) (epsilon : Q') : Q' :=
  epsilon * Q'.recipPos (cost+1) (cost_plus_one_pos cost hc)

theorem costTolerance_pos (cost : Q') (hc : (0 : Q') ≤ cost)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < costTolerance cost hc epsilon :=
  Q'.mul_pos hepsilon (Q'.recipPos_pos _ _)

theorem costTolerance_pays (cost : Q') (hc : (0 : Q') ≤ cost)
    (epsilon : Q') (hepsilon : (0 : Q') ≤ epsilon) :
    costTolerance cost hc epsilon * cost ≤ epsilon := by
  let r := Q'.recipPos (cost+1) (cost_plus_one_pos cost hc)
  have hr : r*(cost+1) ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  have hrc : r*cost ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_self_of_nonneg cost 1 Q'.zero_le_one) (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_of_eqv hr)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv epsilon r cost))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ epsilon hrc hepsilon)
      (Q'.le_of_eqv (Q'.mul_one_eqv epsilon)))

/-- Cancel a strictly positive certified polynomial multiplier in the SAME
Haar expectation, with no residual floor loss and no certificate-level division. -/
theorem haar_nonnegative_of_positive_multiplier
    {blocks : Nat} {background p q : RatPoly} {ell u : Q'}
    (hp : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks p)
    (hq : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks q)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (B : Certificate blocks background) (PQ : Certificate blocks (polyMul p q)) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul background q) := by
  let Q := polynomialInterval blocks q hq
  let cost := polynomialCap q * quaternionHaar blocks background
  have hc : (0 : Q') ≤ cost := Q'.mul_nonneg _ _ Q.nonnegative B.haar_nonnegative
  apply Q'.le_of_le_add_mul_invSucc 0 _ 1
  intro N
  let epsilon := Q'.invSucc N
  let inner := costTolerance cost hc epsilon
  have hi : (0 : Q') < inner := costTolerance_pos cost hc epsilon (Q'.invSucc_pos N)
  let k := reflectionCutoff ell u hu inner
  have h := reflection_with_error hp hell hu hle L U B Q PQ inner hi k (Nat.le_refl _)
  have hpay : (inner * polynomialCap q) * quaternionHaar blocks background ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (costTolerance_pays cost hc epsilon (Q'.le_of_lt (Q'.invSucc_pos N)))
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add_left _ _ _
    (Q'.le_trans' _ _ _ hpay (Q'.ge_of_eqv (Q'.one_mul_eqv epsilon))))

end YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection

#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.correctorCertificate
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.reciprocalCertificate
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.correctedInsertionCertificate
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.reflection_with_error
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.costTolerance
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.costTolerance_pos
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.costTolerance_pays
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection.haar_nonnegative_of_positive_multiplier
