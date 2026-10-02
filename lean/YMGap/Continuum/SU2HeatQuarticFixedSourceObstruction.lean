/-
# One original signed Haar source obstructs every later heat cutoff

The computed source degree depends on the strict nome and affine multiplier,
NOT on the heat cutoff or constant error. Its explicit original one-link
Haar norm is one. At every cutoff beyond that degree plus two, the actual
relative-kernel residual has a negative two-link Haar quadratic value.

This joins the full-coefficient obstruction to the original harmonic source:
the failure is not confined to a moving prefix-edge test. It does not refute
a bound for the particular interacting Wilson source or its OWN variance,
and does not assert an uncut operator, scaling or continuum theorem.
-/

import YMGap.Continuum.SU2HeatQuarticFullCoefficientObstruction
import YMGap.Continuum.SU2HeatQuarticSignedHaarObstruction

namespace YMGap.Continuum.SU2HeatQuarticFixedSourceObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionHeatQuarticMoment
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatQuarticSignedHaarObstruction
open YMGap.Continuum.SU2HeatQuarticFullCoefficientObstruction
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BondMovingStep (coeffW)

local infix:50 " ≈ " => Q'.eqv

/-- Once both neighbours on each side are retained, the ORIGINAL finite
quartic coefficient is exactly its full-sequence coefficient. -/
theorem quarticCoeff_interior (q : Q') (K j : Nat) (hj : 2 ≤ j)
    (hK : j+2 ≤ K) : quarticCoeff (cutCoeff q K) j = quarticCoeff (coeffW q) j := by
  have he : j = (j-2)+2 := by omega
  rw [he]
  simp only [quarticCoeff, cutCoeff,
    if_pos (show j-2+2 ≤ K by omega),
    if_pos (show j-2+1 ≤ K by omega),
    if_pos (show j-2+3 ≤ K by omega),
    if_pos (show j-2 ≤ K by omega),
    if_pos (show j-2+4 ≤ K by omega)]

private theorem response_sum_pin (a : Nat → Q') (N n : Nat) :
    Q'.ofNat (n+1) * finSum (fun j => a j * gamma n j) N ≈
      (if n < N then a n else 0) := by
  have hr : insertion 1 polyOne (endpoint n) (characterRow a N) ≈
      finSum (fun j => a j * gamma n j) N :=
    Q'.eqv_trans _ _ _ (insertion_sum_range 1 polyOne (endpoint n) _ N)
      (finSum_eqv_congr _ _ (fun j => insertion_smul 1 polyOne (endpoint n) _ (a j)) N)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hr))
    (characterRow_quadratic_pin a N n)

private theorem prefix_pin (q : Q') (K n : Nat) (hn : n ≤ K) :
    Q'.ofNat (n+1) * insertion 1 polyOne (endpoint n) (heatPrefix q K relativeScalar) ≈
      coeffW q n := by
  have h := characterRow_quadratic_pin (coeffW q) (K+1) n
  rw [if_pos (show n < K+1 by omega)] at h
  exact h

private theorem quartic_pin (q : Q') (K n : Nat) (hn : n < K+3) :
    Q'.ofNat (n+1) * insertion 1 polyOne (endpoint n)
      (polyMul (polyMul (defect relativeScalar) (defect relativeScalar))
        (heatPrefix q K relativeScalar)) ≈ quarticCoeff (cutCoeff q K) n := by
  have h := response_sum_pin (quarticCoeff (cutCoeff q K)) (K+3) n
  rw [if_pos hn] at h
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (quartic_value_regrouped 1 polyOne (endpoint n) relativeScalar q K)) h

private theorem constant_pin (n : Nat) (hn : 0 < n) (e : Q') :
    Q'.ofNat (n+1) * insertion 1 polyOne (endpoint n) (cap e) ≈ 0 := by
  have h := characterRow_quadratic_pin (fun _ => e) 1 n
  rw [if_neg (show ¬ n < 1 by omega)] at h
  have hc : RatPolyCoeffEqv (characterRow (fun _ => e) 1) (cap e) :=
    RatPolyCoeffEqv.add_zero _
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (insertion_coeff 1 polyOne (endpoint n) hc))) h

private theorem insertion_negative (a p : RatPoly) :
    insertion 1 polyOne a (polyNeg p) ≈ -(insertion 1 polyOne a p) := by
  have hp : RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p) :=
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => p)).trans (cap_mul_left (-1) p)
  exact Q'.eqv_trans _ _ _ (insertion_coeff _ _ _ hp)
    (Q'.eqv_trans _ _ _ (insertion_smul _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- Exact ORIGINAL Haar value at any retained positive interior mode. -/
theorem affine_interior_pin (q : Q') (K n : Nat) (hn : 2 ≤ n)
    (hK : n+2 ≤ K) (c e : Q') :
    Q'.ofNat (n+1) * insertion 1 polyOne (endpoint n) (affineResidual q K c e) ≈
      c * coeffW (q*q) n - quarticCoeff (coeffW q) n := by
  let H := insertion 1 polyOne (endpoint n) (heatPrefix (q*q) K relativeScalar)
  let C := insertion 1 polyOne (endpoint n) (cap e)
  let P := insertion 1 polyOne (endpoint n)
    (polyMul (polyMul (defect relativeScalar) (defect relativeScalar))
      (heatPrefix q K relativeScalar))
  have hr : insertion 1 polyOne (endpoint n) (affineResidual q K c e) ≈
      (c*H+C)+ -P :=
    Q'.eqv_trans _ _ _ (insertion_add _ _ _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (insertion_add _ _ _ _ _)
          (Q'.add_eqv_congr' (insertion_smul _ _ _ _ _) (Q'.eqv_refl _)))
        (insertion_negative _ _))
  have hp := quartic_pin q K n (by omega)
  rw [quarticCoeff_interior q K n hn hK] at hp
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) ?_
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.add (.mul (.var 1) (.var 2)) (.var 3)) (.neg (.var 4))))
    (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.var 3))) (.neg (.mul (.var 0) (.var 4))))
    (by decide)
    (fun
      | 0 => Q'.ofNat (n+1)
      | 1 => c
      | 2 => H
      | 3 => C
      | _ => P)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left c _ _ (prefix_pin (q*q) K n (by omega)))
        (constant_pin n (by omega) e)) (Q'.neg_eqv_congr _ _ hp))
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The explicit source depends on q,c only, never on K or the error e. -/
def fixedSource (q c : Q') : RatPoly := endpoint (fullCoefficientCutoff q c)

theorem fixedSource_supported (q c : Q') : SupportedQuaternionBlocks 1 (fixedSource q c) :=
  endpoint_supported _

theorem fixedSource_norm (q c : Q') :
    quaternionHaar 1 (polyMul (fixedSource q c) (fixedSource q c)) ≈ 1 :=
  endpoint_norm _

private theorem difference_negative {a b : Q'} (h : a < b) : a-b < (0 : Q') := by
  change a.num*(b.den : Int) < b.num*(a.den : Int) at h
  change (a-b).num*1 < 0*((a-b).den : Int)
  change (a.num*(b.den : Int)+(-b.num)*(a.den : Int))*1 < 0*((a-b).den : Int)
  simp only [Int.mul_one, Int.zero_mul, Int.neg_mul]
  omega

private theorem product_negative {d x : Q'} (hd : (0 : Q') < d)
    (hprod : d*x < (0 : Q')) : x < (0 : Q') := by
  have hn : (0 : Int) < d.num := Q'.num_pos_of_pos hd
  have hp : d.num*x.num < 0 := by
    change (d*x).num*1 < 0*((d*x).den : Int) at hprod
    simpa only [Int.mul_one, Int.zero_mul] using hprod
  have hx : x.num < 0 := by
    by_cases h : x.num < 0
    · exact h
    · have hm := Int.mul_nonneg (Int.le_of_lt hn) (show 0 ≤ x.num by omega)
      omega
  change x.num*1 < 0*(x.den : Int)
  simpa only [Int.mul_one, Int.zero_mul] using hx

/-- The SAME fixed original norm-one signed source gives a negative actual
Haar quadratic at EVERY later cutoff, for EVERY constant error. -/
theorem fixedSource_negative_all_later {q c : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hc : (0 : Q') ≤ c) (K : Nat)
    (hK : fullCoefficientCutoff q c + 2 ≤ K) (e : Q') :
    insertion 1 polyOne (fixedSource q c) (affineResidual q K c e) < (0 : Q') := by
  let n := fullCoefficientCutoff q c
  have hn : 2 ≤ n := by unfold n fullCoefficientCutoff; omega
  have h := affine_interior_pin q K n hn hK c e
  exact product_negative (Q'.ofNat_succ_pos n)
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv h)
      (difference_negative (full_quartic_coefficient_gt hq0 hq1 hc n (Nat.le_refl n))))

#print axioms quarticCoeff_interior
#print axioms affine_interior_pin
#print axioms fixedSource
#print axioms fixedSource_supported
#print axioms fixedSource_norm
#print axioms fixedSource_negative_all_later

end YMGap.Continuum.SU2HeatQuarticFixedSourceObstruction
