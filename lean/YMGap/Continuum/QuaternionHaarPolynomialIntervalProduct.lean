/-
# Multiplicative interval certificates on shared quaternion variables

Two-sided bounds multiply without losing the small factors:
2(ab-pq)=(a-p)(b+q)+(a+p)(b-q), and likewise for the other sign.
Every term is an existing positive-certificate product. No independence is
assumed. This supplies delta^n for products of n signed heat remainders,
including after multiplication by an arbitrary positive background.
-/

import YMGap.Continuum.QuaternionHaarPolynomialInterval
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.QuaternionHaarPolynomialInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

private def halve {blocks : Nat} {p q : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd p p) q) (Q : Certificate blocks q) : Certificate blocks p := by
  have he : RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p :=
    (RatPolyCoeffEqv.smul_add _ _ _).trans ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide) p).trans (RatPolyCoeffEqv.one_smul p)))
  exact .ofCoeff he.symm (.smul HalfPow.half HalfPow.half_nonneg (.ofCoeff h Q))

private def minus (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def twice (p : PolyExpr) : PolyExpr := .add p p
private def env4 (a b p q : RatPoly) : Nat → RatPoly
  | 0 => a | 1 => b | 2 => p | _ => q

namespace Interval

def constant (blocks : Nat) (c : Q') (hc : (0 : Q') ≤ c) : Interval blocks (cap c) c where
  support := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact supported_one blocks s hs
  nonnegative := hc
  upper := .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (minus (.var 0) (.var 0)) (.const 0)
    (by decide) (fun _ => cap c))
    (.constant blocks 0 (Q'.le_refl' _))
  lower := .ofCoeff (cap_add c c) (.constant blocks (c+c) (Q'.zero_le_add _ _ hc hc))

def one (blocks : Nat) : Interval blocks polyOne 1 :=
  ofCoeff (supported_one blocks) (RatPolyCoeffEqv.one_smul polyOne).symm (constant blocks 1 Q'.zero_le_one)

def mul {blocks : Nat} {p q : RatPoly} {a b : Q'} (P : Interval blocks p a) (Q : Interval blocks q b) :
    Interval blocks (polyMul p q) (a*b) where
  support := supported_polyMul P.support Q.support
  nonnegative := Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative
  upper := .ofCoeff (((cap_mul a b).symm).add (RatPolyCoeffEqv.refl _))
    (halve (coeffEvalExpr_eqv_of_normalize_eq
      (twice (minus (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))))
      (.add (.mul (minus (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (.mul (.add (.var 0) (.var 2)) (minus (.var 1) (.var 3))))
      (by decide) (env4 (cap a) (cap b) p q)) (.add (P.upper.mul Q.lower) (P.lower.mul Q.upper)))
  lower := .ofCoeff (((cap_mul a b).symm).add (RatPolyCoeffEqv.refl _))
    (halve (coeffEvalExpr_eqv_of_normalize_eq
      (twice (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))))
      (.add (.mul (minus (.var 0) (.var 2)) (minus (.var 1) (.var 3)))
        (.mul (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))))
      (by decide) (env4 (cap a) (cap b) p q)) (.add (P.upper.mul Q.upper) (P.lower.mul Q.lower)))

/-- One retained small factor per list entry, even with shared coordinates. -/
def productUniform {A : Type} {blocks : Nat} (f : A → RatPoly) (d : Q') :
    (ids : List A) → (∀ id, id ∈ ids → Interval blocks (f id) d) →
    Interval blocks (polynomialProduct f ids) (d^ids.length)
  | [], _ => one blocks
  | id :: ids, h => (h id List.mem_cons_self).mul
      (productUniform f d ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    Q'.eqv (quaternionHaar blocks (polyNeg p)) (-(quaternionHaar blocks p))
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_cap_product (blocks : Nat) (c : Q') (p : RatPoly) :
    Q'.eqv (quaternionHaar blocks (polyMul p (cap c))) (c*quaternionHaar blocks p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm p (cap c)).trans (cap_mul_left c p)))
    (quaternionHaar_polySmul blocks c p)

/-- Absolute bound relative to the SAME positive background integral. -/
theorem weighted_haar_bound {blocks : Nat} {p r : RatPoly} {d : Q'}
    (R : Interval blocks r d) (P : Certificate blocks p) :
    Q'.abs (quaternionHaar blocks (polyMul p r)) ≤ d*quaternionHaar blocks p := by
  have hu := (P.mul R.upper).haar_nonnegative
  have hl := (P.mul R.lower).haar_nonnegative
  have eu : Q'.eqv (quaternionHaar blocks (polyMul p (polyAdd (cap d) (polyNeg r))))
      (d*quaternionHaar blocks p + -(quaternionHaar blocks (polyMul p r))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (minus (.var 1) (.var 2)))
      (minus (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (env4 p (cap d) r polyZero)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (haar_cap_product _ _ _) (haar_neg _ _)))
  have el : Q'.eqv (quaternionHaar blocks (polyMul p (polyAdd (cap d) r)))
      (quaternionHaar blocks (polyMul p r) + d*quaternionHaar blocks p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 1)))
      (by decide) (env4 p (cap d) r polyZero)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_cap_product _ _ _)))
  exact Q'.abs_le_of_bounds
    (Q'.neg_le_of_zero_le_add (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv el)))
    (Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv eu)))

private theorem haar_one (blocks : Nat) : Q'.eqv (quaternionHaar blocks polyOne) 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

theorem haar_bound {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) :
    Q'.abs (quaternionHaar blocks p) ≤ c := by
  have h := P.weighted_haar_bound (Certificate.one blocks)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul p)))))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv c))))

end Interval
end YMGap.Continuum.QuaternionHaarPolynomialInterval

#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.constant
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.one
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.mul
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.productUniform
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.weighted_haar_bound
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.haar_bound
