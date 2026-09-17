/-
# Both channels of the original heat acting on two head-linear polynomials

The shared input coordinate occurs twice. Its trace-free quadratic part
is transmitted by w^8, while its conditional Haar contraction is retained
with coefficient 1-w^8. The result is an explicit polynomial on the tail.
All retained coefficient polynomials may depend on the first tail block,
which is the target of the heat kernel, and on each other.

The complete relative heat prefix is used, with the substantive K>=2 guard.
Radius replacement is only under original quaternion Haar, never a free
polynomial identity. No other factor depending on the source head can be
discarded. This is not a full spatial-action or terminal cross-energy bound.
-/

import YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
import YMGap.Continuum.SU2QuaternionHeadLinearHaar
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.SU2QuaternionQuadraticHeatProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion (lifted_independent)
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum (heat_vacuum)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
  (coordinatePair radius quadratic quadratic_trace_decomposition quadratic_heat_transmission)
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
  (coordinateMoment atom linear gramRow gram four liftHead_mul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

private def pair (n : Nat) (p r : RatPoly) : Q' :=
  quaternionHaar n (polyMul p r)

private def heatPair (n : Nat) (w : Q') (K : Nat) (p r : RatPoly) : Q' :=
  quaternionHaar (n+1) (polyMul (polyMul (relativeHeat w K) p) (liftHead r))

private theorem pair_congr (n : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q)
    (r : RatPoly) : pair n p r ≈ pair n q r := haar_of_coeff (h.mul_right r)

private theorem heat_congr (n : Nat) (w : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) (r : RatPoly) : heatPair n w K p r ≈ heatPair n w K q r :=
  haar_of_coeff ((h.mul_left (relativeHeat w K)).mul_right (liftHead r))

private theorem pair_add (n : Nat) (p q r : RatPoly) :
    pair n (polyAdd p q) r ≈ pair n p r + pair n q r := by
  unfold pair
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append n _ _

private theorem pair_smul (n : Nat) (c : Q') (p r : RatPoly) :
    pair n (polySmul c p) r ≈ c * pair n p r :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

private theorem heat_add (n : Nat) (w : Q') (K : Nat) (p q r : RatPoly) :
    heatPair n w K (polyAdd p q) r ≈ heatPair n w K p r + heatPair n w K q r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_add_right (relativeHeat w K) p q).mul_right (liftHead r)))
    (pair_add (n+1) _ _ _)

private theorem heat_smul (n : Nat) (w : Q') (K : Nat) (c : Q') (p r : RatPoly) :
    heatPair n w K (polySmul c p) r ≈ c * heatPair n w K p r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (((RatPolyCoeffEqv.polyMul_smul_right c (relativeHeat w K) p).mul_right
      (liftHead r)).trans (RatPolyCoeffEqv.polyMul_smul_left c _ _)))
    (quaternionHaar_polySmul (n+1) c _)

private theorem radius_coeff : RatPolyCoeffEqv radius (quaternionRadiusPolynomial 0) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem radius_pair (n : Nat) (hn : 0 < n) (r : RatPoly) :
    pair n radius r ≈ quaternionHaar n r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_comm radius r).trans (radius_coeff.mul_left r)))
    (quaternionHaar_mul_radius n 0 hn r)

private theorem swap_last (p q r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p q) r) (polyMul (polyMul p r) q) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1))
    (by decide) (fun | 0 => p | 1 => q | _ => r)

private theorem heat_radius (n : Nat) (hn : 0 < n) (w : Q') (K : Nat) (r : RatPoly) :
    heatPair n w K radius r ≈ quaternionHaar n r := by
  have hlift : quaternionHaar (n+1) (liftHead r) ≈ quaternionHaar n r :=
    haar_liftBoundary 1 n r
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((swap_last (relativeHeat w K) radius (liftHead r)).trans
      (radius_coeff.mul_left _)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_mul_radius (n+1) 0 (by omega) _)
      (Q'.eqv_trans _ _ _ (heat_vacuum n hn w K (liftHead r) (lifted_independent r)) hlift))

private theorem trace_balance (l d q z : Q') :
    l*q+d*z ≈ l*(q+d*z)+(1 + -l)*(d*z) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (.add (.mul (.var 0) (.add (.var 2) (.mul (.var 1) (.var 3))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 1) (.var 3))))
    (by decide) (fun | 0 => l | 1 => d | 2 => q | _ => z)

/-- Full coordinate-pair transmission, including its exact trace term.
The insertion can involve the target quaternion and every other tail block. -/
theorem coordinatePair_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (coordinatePair i j)) (liftHead r)) ≈
      qpow w 8 * quaternionHaar tailBlocks (polyMul (coordinatePair i j) r) +
        (1 + -(qpow w 8)) * (coordinateMoment i j * quaternionHaar tailBlocks r) := by
  let d := coordinateMoment i j
  have hd : RatPolyCoeffEqv (polyAdd (quadratic i j) (polySmul d radius))
      (coordinatePair i j) := quadratic_trace_decomposition i j
  have ht : pair tailBlocks (coordinatePair i j) r ≈
      pair tailBlocks (quadratic i j) r + d * quaternionHaar tailBlocks r :=
    Q'.eqv_trans _ _ _ (pair_congr tailBlocks hd.symm r)
      (Q'.eqv_trans _ _ _ (pair_add tailBlocks _ _ r)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (pair_smul tailBlocks d radius r)
            (Q'.mul_eqv_congr_left d _ _ (radius_pair tailBlocks hb r)))))
  have hh : heatPair tailBlocks w K (coordinatePair i j) r ≈
      qpow w 8 * pair tailBlocks (quadratic i j) r + d * quaternionHaar tailBlocks r :=
    Q'.eqv_trans _ _ _ (heat_congr tailBlocks w K hd.symm r)
      (Q'.eqv_trans _ _ _ (heat_add tailBlocks w K _ _ r)
        (Q'.add_eqv_congr'
          (quadratic_heat_transmission tailBlocks hb w K hK i j r)
          (Q'.eqv_trans _ _ _ (heat_smul tailBlocks w K d radius r)
            (Q'.mul_eqv_congr_left d _ _ (heat_radius tailBlocks hb w K r)))))
  exact Q'.eqv_trans _ _ _ hh
    (Q'.eqv_trans _ _ _ (trace_balance (qpow w 8) d _ _)
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ht)) (Q'.eqv_refl _)))

/-- Substitute the source head by the first retained head. Coefficient
polynomials are left unchanged, even when they use that retained head. -/
def retainedLinear : List (Fin 4 × RatPoly) → RatPoly
  | [] => polyZero
  | (i,p)::xs => polyAdd (polyMul (polyVar i.val) p) (retainedLinear xs)

/-- The explicitly computed quadratic and singlet output channels. -/
def linearProductImage (w : Q') (xs ys : List (Fin 4 × RatPoly)) : RatPoly :=
  polyAdd (polySmul (qpow w 8) (polyMul (retainedLinear xs) (retainedLinear ys)))
    (polySmul (1 + -(qpow w 8)) (gram xs ys))

private theorem atom_input (k a p b q r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul k (polyMul (polyMul a p) (polyMul b q))) r)
      (polyMul (polyMul k (polyMul a b)) (polyMul (polyMul p q) r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))) (.var 5))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.mul (.var 2) (.var 4)) (.var 5)))
    (by decide) (fun | 0 => k | 1 => a | 2 => p | 3 => b | 4 => q | _ => r)

private theorem atom_output (a p b q r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul a p) (polyMul b q)) r)
      (polyMul (polyMul a b) (polyMul (polyMul p q) r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.mul (.var 1) (.var 3)) (.var 4)))
    (by decide) (fun | 0 => a | 1 => p | 2 => b | 3 => q | _ => r)

private theorem atom_transmission (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (hK : 2 ≤ K) (i j : Fin 4) (p q r : RatPoly) :
    heatPair n w K (polyMul (atom i p) (atom j q)) r ≈
      qpow w 8 * pair n (polyMul (polyMul (polyVar i.val) p) (polyMul (polyVar j.val) q)) r +
        (1 + -(qpow w 8)) * pair n (polySmul (coordinateMoment i j) (polyMul p q)) r := by
  have hi : heatPair n w K (polyMul (atom i p) (atom j q)) r ≈
      heatPair n w K (coordinatePair i j) (polyMul (polyMul p q) r) := by
    unfold heatPair atom coordinatePair
    rw [liftHead_mul, liftHead_mul]
    exact haar_of_coeff (atom_input _ _ _ _ _ _)
  have ho : pair n (polyMul (polyMul (polyVar i.val) p) (polyMul (polyVar j.val) q)) r ≈
      pair n (coordinatePair i j) (polyMul (polyMul p q) r) :=
    haar_of_coeff (atom_output _ _ _ _ _)
  exact Q'.eqv_trans _ _ _ hi
    (Q'.eqv_trans _ _ _ (coordinatePair_transmission n hn w K hK i j (polyMul (polyMul p q) r))
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (pair_smul n (coordinateMoment i j) _ r)))))

private theorem mix_add (l m a b c d : Q') :
    (l*a+m*b)+(l*c+m*d) ≈ l*(a+c)+m*(b+d) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5))))
    (.add (.mul (.var 0) (.add (.var 2) (.var 4)))
      (.mul (.var 1) (.add (.var 3) (.var 5))))
    (by decide) (fun | 0 => l | 1 => m | 2 => a | 3 => b | 4 => c | _ => d)

private theorem heat_zero (n : Nat) (w : Q') (K : Nat) (r : RatPoly) :
    heatPair n w K polyZero r ≈ 0 :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_zero_right (relativeHeat w K)).mul_right (liftHead r))

private theorem zero_mix (l m : Q') : (0 : Q') ≈ l*0+m*0 :=
  Q'.eqv_symm (Q'.add_eqv_congr' (Q'.mul_zero_eqv l) (Q'.mul_zero_eqv m))

private theorem atom_linear_transmission (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (hK : 2 ≤ K) (i : Fin 4) (p r : RatPoly) : ∀ ys : List (Fin 4 × RatPoly),
    heatPair n w K (polyMul (atom i p) (linear ys)) r ≈
      qpow w 8 * pair n (polyMul (polyMul (polyVar i.val) p) (retainedLinear ys)) r +
        (1 + -(qpow w 8)) * pair n (gramRow i p ys) r
  | [] => by
      have hz := pair_congr n (RatPolyCoeffEqv.mul_zero_right (polyMul (polyVar i.val) p)) r
      exact Q'.eqv_trans _ _ _ (heat_congr n w K (RatPolyCoeffEqv.mul_zero_right (atom i p)) r)
        (Q'.eqv_trans _ _ _ (heat_zero n w K r)
          (Q'.eqv_trans _ _ _ (zero_mix (qpow w 8) (1 + -(qpow w 8)))
            (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hz)) (Q'.eqv_refl _))))
  | (j,q)::ys => by
      have ho := Q'.eqv_trans _ _ _
        (pair_congr n (RatPolyCoeffEqv.mul_add_right (polyMul (polyVar i.val) p)
          (polyMul (polyVar j.val) q) (retainedLinear ys)) r)
        (pair_add n _ _ r)
      have hg := pair_add n (polySmul (coordinateMoment i j) (polyMul p q)) (gramRow i p ys) r
      exact Q'.eqv_trans _ _ _
        (heat_congr n w K (RatPolyCoeffEqv.mul_add_right (atom i p) (atom j q) (linear ys)) r)
        (Q'.eqv_trans _ _ _ (heat_add n w K _ _ r)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (atom_transmission n hn w K hK i j p q r)
              (atom_linear_transmission n hn w K hK i p r ys))
            (Q'.eqv_trans _ _ _ (mix_add (qpow w 8) (1 + -(qpow w 8)) _ _ _ _)
              (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
                (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg))))))

private theorem linear_transmission (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (hK : 2 ≤ K) (r : RatPoly) : ∀ xs ys : List (Fin 4 × RatPoly),
    heatPair n w K (polyMul (linear xs) (linear ys)) r ≈
      qpow w 8 * pair n (polyMul (retainedLinear xs) (retainedLinear ys)) r +
        (1 + -(qpow w 8)) * pair n (gram xs ys) r
  | [], _ => Q'.eqv_trans _ _ _ (heat_zero n w K r)
      (zero_mix (qpow w 8) (1 + -(qpow w 8)))
  | (i,p)::xs, ys => by
      have ho := pair_add n (polyMul (polyMul (polyVar i.val) p) (retainedLinear ys))
        (polyMul (retainedLinear xs) (retainedLinear ys)) r
      have hg := pair_add n (gramRow i p ys) (gram xs ys) r
      change heatPair n w K (polyMul (polyAdd (atom i p) (linear xs)) (linear ys)) r ≈ _
      rw [polyMul_add_left_exact]
      have ht := Q'.eqv_trans _ _ _ (heat_add n w K _ _ r)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (atom_linear_transmission n hn w K hK i p r ys)
            (linear_transmission n hn w K hK r xs ys))
          (Q'.eqv_trans _ _ _ (mix_add (qpow w 8) (1 + -(qpow w 8)) _ _ _ _)
            (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg)))))
      simpa only [retainedLinear, gram, polyMul_add_left_exact] using ht

/-- Exact computed output for every finite pair of head-linear inputs.
No support bound or target-head independence is imposed on their coefficients. -/
theorem linear_product_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (xs ys : List (Fin 4 × RatPoly)) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (polyMul (linear xs) (linear ys))) (liftHead r)) ≈
      quaternionHaar tailBlocks (polyMul (linearProductImage w xs ys) r) := by
  have hi : pair tailBlocks (linearProductImage w xs ys) r ≈
      qpow w 8 * pair tailBlocks (polyMul (retainedLinear xs) (retainedLinear ys)) r +
        (1 + -(qpow w 8)) * pair tailBlocks (gram xs ys) r :=
    Q'.eqv_trans _ _ _ (pair_add tailBlocks _ _ r)
    (Q'.add_eqv_congr' (pair_smul tailBlocks (qpow w 8) _ r)
      (pair_smul tailBlocks (1 + -(qpow w 8)) _ r))
  exact Q'.eqv_trans _ _ _ (linear_transmission tailBlocks hb w K hK r xs ys) (Q'.eqv_symm hi)

end YMGap.Continuum.SU2QuaternionQuadraticHeatProduct

#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatProduct.coordinatePair_transmission
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatProduct.retainedLinear
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatProduct.linearProductImage
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatProduct.linear_product_transmission
