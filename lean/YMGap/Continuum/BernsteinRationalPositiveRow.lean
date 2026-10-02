/-
# Computed positive Bernstein rows of an actual rational polynomial

The source is the original low-to-high rational coefficient list p.
Every row, denominator branch, coefficient tolerance and common finite
cutoff is computed from that list and the requested strict margin eta.
The unnormalised row reconstructs p exactly on ALL rational arguments.
Above the computed cutoff its normalized coefficients approximate p at
the original rational grid within eta/2. A strict interval margin then
proves nonnegativity of the ACTUAL reconstructed row.

This is finite coefficient algebra. No row positivity, reconstruction or
degree-elevation witness is assumed. No original Haar Certificate is
returned here; its algebraic compilation remains a separate step.
-/

import YMGap.Continuum.BernsteinNormalizedMonomialCoefficient
import YMGap.Constructive.QPolyCoefficient

namespace YMGap.Continuum.BernsteinRationalPositiveRow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient (coeff)
open YMGap.Constructive.QPolyWeightedL1 (weightedL1 weightedL1_nonnegative)
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinFallingProductError
open YMGap.Continuum.BernsteinNormalizedFallingProductError
open YMGap.Continuum.BernsteinNormalizedMonomialCoefficient
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Total actual quotient computation; all contributing branches are proved
to select the positive quotient above the common computed cutoff. -/
def safeProduct (n j r : Nat) : Q' :=
  if hn : denominatorCutoff r ≤ n then normalizedProduct n j r hn else 0

theorem safeProduct_pin (n j r : Nat) (hn : denominatorCutoff r ≤ n) :
    safeProduct n j r ≈ normalizedProduct n j r hn := by
  rw [safeProduct, dif_pos hn]
  exact Q'.eqv_refl _

def normalizedRow (p : Poly) (n j : Nat) : Q' :=
  finSum (fun r => coeff p r*safeProduct n j r) p.length

def unnormalizedRow (p : Poly) (n j : Nat) : Q' :=
  finSum (fun r => coeff p r*Q'.ofNat (elevatedMonoCoeff (n+1) r j)) p.length

private theorem ring_swap (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- The finite power sum is exactly the original Horner polynomial. -/
theorem coefficient_power_sum : ∀ (p : Poly) (w : Q'),
    finSum (fun r => coeff p r*w^r) p.length ≈ eval p w
  | [], _ => Q'.eqv_refl 0
  | c::p, w => by
      refine Q'.eqv_trans _ _ _ (finSum_peel_left _ p.length) ?_
      have ht : finSum (fun r => coeff (c::p) (r+1)*w^(r+1)) p.length ≈
          w*eval p w := by
        refine Q'.eqv_trans _ _ _
          (finSum_eqv_congr _ (fun r => w*(coeff p r*w^r))
            (fun r => ring_swap (coeff p r) w (w^r)) p.length) ?_
        exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (const_mul_finSum _ w p.length))
          (Q'.mul_eqv_congr_left w _ _ (coefficient_power_sum p w))
      exact QPoly.q_add_congr (Q'.mul_one_eqv c) ht

private theorem coefficient_abs_sum : ∀ p : Poly,
    finSum (fun r => Q'.abs (coeff p r)) p.length ≈ weightedL1 1 p
  | [] => Q'.eqv_refl 0
  | c::p => Q'.eqv_trans _ _ _ (finSum_peel_left _ p.length)
      (Q'.add_eqv_congr_left (Q'.abs c) _ _
        (Q'.eqv_trans _ _ _ (coefficient_abs_sum p)
          (Q'.eqv_symm (Q'.one_mul_eqv _))))

/-- Exact rational row reconstruction; only the actual degree must fit. -/
theorem unnormalizedRow_reconstruction (p : Poly) (n : Nat)
    (hdegree : p.length ≤ n+1) (w : Q') :
    finSum (fun j => unnormalizedRow p n j*bernsteinBasis (n+1) w j) (n+2) ≈ eval p w := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _
      (fun j => finSum (fun r => (coeff p r*Q'.ofNat (elevatedMonoCoeff (n+1) r j))*
        bernsteinBasis (n+1) w j) p.length)
      (fun j => finSum_mul_const _ _ p.length) (n+2)) ?_
  refine Q'.eqv_trans _ _ _ (finSum_swap _ (n+2) p.length) ?_
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ p.length ?_)
    (coefficient_power_sum p w)
  intro r hr
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _
      (fun j => coeff p r*(Q'.ofNat (elevatedMonoCoeff (n+1) r j)*bernsteinBasis (n+1) w j))
      (fun j => Q'.mul_assoc_eqv _ _ _) (n+2)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (const_mul_finSum _ (coeff p r) (n+2))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (elevatedMonoEval_eqv_pow (n+1) r w (by omega))

private theorem normPlusOne_positive (p : Poly) : (0 : Q') < 1+weightedL1 1 p :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 _ (weightedL1_nonnegative 1 (by decide) p))

/-- Per-order tolerance computed from the actual rational coefficient norm. -/
def rowTolerance (p : Poly) (eta : Q') : Q' :=
  Q'.divPos (HalfPow.half*eta) (1+weightedL1 1 p) (normPlusOne_positive p)

theorem rowTolerance_positive (p : Poly) (eta : Q') (he : (0 : Q') < eta) :
    (0 : Q') < rowTolerance p eta :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos (by decide) he)

private def cutoffPrefix (p : Poly) (eta : Q') : Nat → Nat
  | 0 => p.length
  | d+1 => max (cutoffPrefix p eta d) (toleranceCutoff d (rowTolerance p eta))

/-- Explicit finite maximum over the actual coefficient list. -/
def rowCutoff (p : Poly) (eta : Q') : Nat := cutoffPrefix p eta p.length

private theorem cutoffPrefix_degree (p : Poly) (eta : Q') : ∀ d,
    p.length ≤ cutoffPrefix p eta d
  | 0 => Nat.le_refl _
  | d+1 => Nat.le_trans (cutoffPrefix_degree p eta d) (Nat.le_max_left _ _)

private theorem cutoffPrefix_order (p : Poly) (eta : Q') : ∀ d r,
    r<d → toleranceCutoff r (rowTolerance p eta) ≤ cutoffPrefix p eta d
  | 0, _, h => by omega
  | d+1, r, h => by
      by_cases hr : r<d
      · exact Nat.le_trans (cutoffPrefix_order p eta d r hr) (Nat.le_max_left _ _)
      · have heq : r=d := by omega
        subst r
        exact Nat.le_max_right _ _

theorem rowCutoff_degree (p : Poly) (eta : Q') : p.length ≤ rowCutoff p eta :=
  cutoffPrefix_degree p eta _

theorem rowCutoff_order (p : Poly) (eta : Q') (r : Nat) (hr : r<p.length) :
    toleranceCutoff r (rowTolerance p eta) ≤ rowCutoff p eta :=
  cutoffPrefix_order p eta _ r hr

/-- The ACTUAL unnormalised row is the binomial-weighted normalized row. -/
theorem unnormalizedRow_pin (p : Poly) (eta : Q') (n j : Nat)
    (hn : rowCutoff p eta ≤ n) (hj : j≤n+1) :
    unnormalizedRow p n j ≈ Q'.ofNat (YMGap.RG.binom (n+1) j)*normalizedRow p n j := by
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ p.length ?_)
    (Q'.eqv_symm (const_mul_finSum _ _ p.length))
  intro r hr
  have htol := Nat.le_trans (rowCutoff_order p eta r hr) hn
  have hden : denominatorCutoff r≤n := Nat.le_trans (Nat.le_max_left _ _) htol
  have hdeg := Nat.le_trans (rowCutoff_degree p eta) hn
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (elevatedMonoCoeff_eqv_normalizedProduct n r j (by omega) hj hden)) ?_
  refine Q'.eqv_trans _ _ _ (ring_swap _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (safeProduct_pin n j r hden)))

private theorem sum_abs_sub_bound (f g b : Nat → Q') : ∀ d,
    (∀ r, r<d → Q'.abs (f r + -(g r)) ≤ b r) →
      Q'.abs (finSum f d + -(finSum g d)) ≤ finSum b d
  | 0, _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | d+1, hb => by
      have hring : (finSum f (d+1) + -(finSum g (d+1))) ≈
          (finSum f d + -(finSum g d))+(f d + -(g d)) :=
        poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
          (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
          (by decide) (fun | 0 => finSum f d | 1 => f d | 2 => finSum g d | _ => g d)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hring))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.add_le_add (sum_abs_sub_bound f g b d (fun r hr => hb r (by omega)))
            (hb d (by omega))))

private theorem rowTolerance_budget (p : Poly) (eta : Q') (he : (0 : Q')<eta) :
    weightedL1 1 p*rowTolerance p eta ≤ HalfPow.half*eta := by
  have ht : (0 : Q')≤rowTolerance p eta := Q'.le_of_lt (rowTolerance_positive p eta he)
  have hn : weightedL1 1 p ≤ 1+weightedL1 1 p :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hn ht)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.divPos_mul_eqv _ _ (normPlusOne_positive p))))

/-- Explicit uniform coefficient error for the computed actual row. -/
theorem normalizedRow_error (p : Poly) (eta : Q') (he : (0 : Q')<eta)
    (n j : Nat) (hn : rowCutoff p eta≤n) (hj : j≤n+1) :
    Q'.abs (normalizedRow p n j + -(eval p (grid n j))) ≤ HalfPow.half*eta := by
  let delta := rowTolerance p eta
  have hs : Q'.abs (normalizedRow p n j +
      -(finSum (fun r => coeff p r*grid n j^r) p.length)) ≤
        finSum (fun r => Q'.abs (coeff p r)*delta) p.length := by
    apply sum_abs_sub_bound
    intro r hr
    have htol := Nat.le_trans (rowCutoff_order p eta r hr) hn
    have hden : denominatorCutoff r≤n := Nat.le_trans (Nat.le_max_left _ _) htol
    have hc := normalizedProduct_close r delta (rowTolerance_positive p eta he) n htol j hj
    have hclose : Q'.abs (safeProduct n j r + -(grid n j^r)) ≤ delta :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_eqv_congr
          (QPoly.q_add_congr (safeProduct_pin n j r hden) (Q'.eqv_refl _))))
        (CReal.abs_sub_le_of_bounds hc.1 hc.2)
    have hdiff : coeff p r*safeProduct n j r + -(coeff p r*grid n j^r) ≈
        coeff p r*(safeProduct n j r + -(grid n j^r)) :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
        (fun | 0 => coeff p r | 1 => safeProduct n j r | _ => grid n j^r)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hdiff))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hclose (Q'.abs_nonneg _)))
  have heval := coefficient_power_sum p (grid n j)
  have htransport : Q'.abs (normalizedRow p n j + -(eval p (grid n j))) ≈
      Q'.abs (normalizedRow p n j + -(finSum (fun r => coeff p r*grid n j^r) p.length)) :=
    ExpNeg.abs_eqv_congr (QPoly.q_add_congr (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm heval)))
  have hsum : finSum (fun r => Q'.abs (coeff p r)*delta) p.length ≈ weightedL1 1 p*delta :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (finSum_mul_const _ delta p.length))
      (Q'.mul_eqv_congr_right _ _ delta (coefficient_abs_sum p))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport)
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) (rowTolerance_budget p eta he)))

private theorem eval_le_row_add (p : Poly) (eta : Q') (he : (0 : Q')<eta)
    (n j : Nat) (hn : rowCutoff p eta≤n) (hj : j≤n+1) :
    eval p (grid n j) ≤ normalizedRow p n j+HalfPow.half*eta := by
  let B := normalizedRow p n j
  let P := eval p (grid n j)
  have hdiff : P + -B ≈ -(B + -P) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 1)))
      (.neg (.add (.var 1) (.neg (.var 0)))) (by decide) (fun | 0 => P | _ => B)
  have h := Q'.le_trans' _ _ _ (Q'.le_of_eqv hdiff)
    (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (normalizedRow_error p eta he n j hn hj))
  have ha := Q'.add_le_add_right _ _ B h
  have hr : (P + -B)+B ≈ P :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => P | _ => B)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hr)
    (Q'.le_trans' _ _ _ ha (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- A strict margin of the ORIGINAL rational polynomial constructs a
positive normalized row; the premise is tested only at actual grid points. -/
theorem normalizedRow_half_margin (p : Poly) (eta : Q') (he : (0 : Q')<eta)
    (hmargin : ∀ y : Q', (0 : Q')≤y → y≤1 → eta≤eval p y)
    (n j : Nat) (hn : rowCutoff p eta≤n) (hj : j≤n+1) :
    HalfPow.half*eta ≤ normalizedRow p n j := by
  have hm := hmargin (grid n j) (grid_nonnegative n j) (grid_le_one n j hj)
  have h := Q'.add_le_add_right _ _ (-(HalfPow.half*eta))
    (Q'.le_trans' _ _ _ hm (eval_le_row_add p eta he n j hn hj))
  have heq : eta + -(HalfPow.half*eta) ≈ HalfPow.half*eta :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (by decide)
        (fun | 0 => eta | _ => HalfPow.half))
      (Q'.mul_eqv_congr_right _ _ eta (by decide : (1 : Q') + -HalfPow.half ≈ HalfPow.half))
  have hcancel : (normalizedRow p n j+HalfPow.half*eta)+ -(HalfPow.half*eta) ≈ normalizedRow p n j :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun | 0 => normalizedRow p n j | _ => HalfPow.half*eta)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hcancel))

/-- Nonnegativity of the ACTUAL exact unnormalised reconstruction row. -/
theorem unnormalizedRow_nonnegative (p : Poly) (eta : Q') (he : (0 : Q')<eta)
    (hmargin : ∀ y : Q', (0 : Q')≤y → y≤1 → eta≤eval p y)
    (n j : Nat) (hn : rowCutoff p eta≤n) (hj : j≤n+1) :
    (0 : Q')≤unnormalizedRow p n j := by
  have hb : (0 : Q')≤normalizedRow p n j := Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt he))
    (normalizedRow_half_margin p eta he hmargin n j hn hj)
  exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) hb)
    (Q'.ge_of_eqv (unnormalizedRow_pin p eta n j hn hj))

#print axioms safeProduct
#print axioms safeProduct_pin
#print axioms normalizedRow
#print axioms unnormalizedRow
#print axioms coefficient_power_sum
#print axioms unnormalizedRow_reconstruction
#print axioms rowTolerance
#print axioms rowTolerance_positive
#print axioms rowCutoff
#print axioms rowCutoff_degree
#print axioms rowCutoff_order
#print axioms unnormalizedRow_pin
#print axioms normalizedRow_error
#print axioms normalizedRow_half_margin
#print axioms unnormalizedRow_nonnegative

end YMGap.Continuum.BernsteinRationalPositiveRow
