/-
# Positive-polynomial Cauchy products in the ten-Haar carrier

This file supplies the exact finite algebra needed to regroup two ordinary
positive polynomial Taylor factors.  The proof is the polynomial-carrier
analogue of `Constructive.ExpAddConv`: weighted Cauchy coefficients satisfy
the same first-order factorial recurrence as the Taylor coefficient of the
sum.  All identities are taken in `TenHaarCarrierEqv`, so every statement is
valid after an arbitrary ten-holonomy insertion.

The analytic Mertens corner and its explicit modulus are built after the
finite coefficient collapse.

## Axiom gate

Finite lists, exact `Q'` algebra, and `Quot.sound` only.  No classical choice,
excluded middle, native reduction, custom axiom, or noncomputable definition.
-/

import YMGap.Continuum.BF4GroupedThreeFactorCofinal
import YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
import YMGap.Constructive.CornerBoundAdd

namespace YMGap.Continuum.BF4PositivePolynomialCauchyMertens

set_option maxRecDepth 12000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionExponentialShift
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionShiftedExponential
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedCarrierMertens
open YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
open YMGap.Continuum.BF4GroupedHolonomyPositiveLimit
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4GroupedPhysicalActionShift
open YMGap.Continuum.BF4GroupedThreeFactorCofinal
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite polynomial sums in the Haar carrier -/

/-- Left-associated finite sum of carrier polynomials. -/
def carrierPolyFinSum (family : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | terms + 1 => polyAdd (carrierPolyFinSum family terms) (family terms)

theorem TenHaarCarrierEqv.zero :
    TenHaarCarrierEqv polyZero polyZero :=
  TenHaarCarrierEqv.refl polyZero

private theorem polyMul_zero_right_local :
    ∀ polynomial : RatPoly,
      polyMul polynomial polyZero = polyZero
  | [] => rfl
  | _ :: rest => by
      simp [polyMul, polyZero]

/-- Exchange the two middle summands in a four-term carrier sum. -/
theorem tenHaarCarrierEqv_add_four_swap
    (first second third fourth : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd (polyAdd first second) (polyAdd third fourth))
      (polyAdd (polyAdd first third) (polyAdd second fourth)) := by
  intro insertion
  refine Q'.eqv_trans _
    ((quaternionHaar 10 (polyMul insertion first) +
        quaternionHaar 10 (polyMul insertion second)) +
      (quaternionHaar 10 (polyMul insertion third) +
        quaternionHaar 10 (polyMul insertion fourth))) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right 10 insertion
        (polyAdd first second) (polyAdd third fourth))
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_add_right 10 insertion first second)
        (quaternionHaar_polyMul_add_right 10 insertion third fourth))
  · refine Q'.eqv_trans _
      ((quaternionHaar 10 (polyMul insertion first) +
          quaternionHaar 10 (polyMul insertion third)) +
        (quaternionHaar 10 (polyMul insertion second) +
          quaternionHaar 10 (polyMul insertion fourth))) _
      (Q'.add_swap_inner _ _ _ _) ?_
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right 10 insertion
          (polyAdd first third) (polyAdd second fourth))
        (Q'.add_eqv_congr'
          (quaternionHaar_polyMul_add_right 10 insertion first third)
          (quaternionHaar_polyMul_add_right 10 insertion second fourth)))

/-- Pointwise carrier equivalence survives finite summation. -/
theorem carrierPolyFinSum_congr
    {left right : Nat → RatPoly}
    (h : ∀ index, TenHaarCarrierEqv (left index) (right index)) :
    ∀ terms,
      TenHaarCarrierEqv
        (carrierPolyFinSum left terms)
        (carrierPolyFinSum right terms)
  | 0 => TenHaarCarrierEqv.refl polyZero
  | terms + 1 =>
      TenHaarCarrierEqv.add_congr
        (carrierPolyFinSum_congr h terms)
        (h terms)

/-- Bounded-index version of finite-sum congruence. -/
theorem carrierPolyFinSum_congr_lt
    {left right : Nat → RatPoly}
    (h : ∀ index, index < terms →
      TenHaarCarrierEqv (left index) (right index)) :
    TenHaarCarrierEqv
      (carrierPolyFinSum left terms)
      (carrierPolyFinSum right terms) := by
  induction terms with
  | zero => exact TenHaarCarrierEqv.refl polyZero
  | succ terms induction =>
      exact TenHaarCarrierEqv.add_congr
        (induction (fun index hindex =>
          h index (Nat.lt_trans hindex (Nat.lt_succ_self terms))))
        (h terms (Nat.lt_succ_self terms))

/-- Finite summation distributes over carrier addition. -/
theorem carrierPolyFinSum_add
    (left right : Nat → RatPoly) :
    ∀ terms,
      TenHaarCarrierEqv
        (carrierPolyFinSum
          (fun index => polyAdd (left index) (right index)) terms)
        (polyAdd
          (carrierPolyFinSum left terms)
          (carrierPolyFinSum right terms))
  | 0 => by
      simp [carrierPolyFinSum, polyAdd, polyZero]
      exact TenHaarCarrierEqv.refl polyZero
  | terms + 1 => by
      change TenHaarCarrierEqv
        (polyAdd
          (carrierPolyFinSum
            (fun index => polyAdd (left index) (right index)) terms)
          (polyAdd (left terms) (right terms)))
        (polyAdd
          (polyAdd (carrierPolyFinSum left terms) (left terms))
          (polyAdd (carrierPolyFinSum right terms) (right terms)))
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.add_right
          (carrierPolyFinSum_add left right terms)
          (polyAdd (left terms) (right terms))) ?_
      exact tenHaarCarrierEqv_add_four_swap
        (carrierPolyFinSum left terms)
        (carrierPolyFinSum right terms)
        (left terms) (right terms)

/-- A common scalar may be pulled through a finite carrier sum. -/
theorem carrierPolyFinSum_smul
    (scale : Q') (family : Nat → RatPoly) :
    ∀ terms,
      TenHaarCarrierEqv
        (polySmul scale (carrierPolyFinSum family terms))
        (carrierPolyFinSum
          (fun index => polySmul scale (family index)) terms)
  | 0 => by
      simp [carrierPolyFinSum, polySmul, polyZero]
      exact TenHaarCarrierEqv.refl polyZero
  | terms + 1 => by
      change TenHaarCarrierEqv
        (polySmul scale
          (polyAdd (carrierPolyFinSum family terms) (family terms)))
        (polyAdd
          (carrierPolyFinSum
            (fun index => polySmul scale (family index)) terms)
          (polySmul scale (family terms)))
      have hsplit :
          polySmul scale
              (polyAdd (carrierPolyFinSum family terms) (family terms)) =
            polyAdd
              (polySmul scale (carrierPolyFinSum family terms))
              (polySmul scale (family terms)) := by
        simp [polySmul, polyAdd]
      rw [hsplit]
      exact TenHaarCarrierEqv.add_congr
        (carrierPolyFinSum_smul scale family terms)
        (TenHaarCarrierEqv.refl _)

/-- Left multiplication distributes through a finite carrier sum. -/
theorem carrierPolyFinSum_mul_left
    (factor : RatPoly) (family : Nat → RatPoly) :
    ∀ terms,
      TenHaarCarrierEqv
        (polyMul factor (carrierPolyFinSum family terms))
        (carrierPolyFinSum
          (fun index => polyMul factor (family index)) terms)
  | 0 => by
      change TenHaarCarrierEqv
        (polyMul factor polyZero) polyZero
      rw [polyMul_zero_right_local]
      exact TenHaarCarrierEqv.refl polyZero
  | terms + 1 => by
      change TenHaarCarrierEqv
        (polyMul factor
          (polyAdd (carrierPolyFinSum family terms) (family terms)))
        (polyAdd
          (carrierPolyFinSum
            (fun index => polyMul factor (family index)) terms)
          (polyMul factor (family terms)))
      exact TenHaarCarrierEqv.trans
        (tenHaarCarrierEqv_polyMul_add_right factor
          (carrierPolyFinSum family terms) (family terms))
        (TenHaarCarrierEqv.add_congr
          (carrierPolyFinSum_mul_left factor family terms)
          (TenHaarCarrierEqv.refl _))

/-- Head-peel reindexing for the left-associated finite polynomial sum. -/
theorem carrierPolyFinSum_head_peel
    (family : Nat → RatPoly) :
    ∀ terms,
      TenHaarCarrierEqv
        (carrierPolyFinSum family (terms + 1))
        (polyAdd (family 0)
          (carrierPolyFinSum (fun index => family (index + 1)) terms))
  | 0 => by
      change TenHaarCarrierEqv
        (polyAdd polyZero (family 0))
        (polyAdd (family 0) polyZero)
      intro insertion
      simp [polyAdd, polyZero, polyMul]
      exact Q'.eqv_refl _
  | terms + 1 => by
      change TenHaarCarrierEqv
        (polyAdd (carrierPolyFinSum family (terms + 1))
          (family (terms + 1)))
        (polyAdd (family 0)
          (polyAdd
            (carrierPolyFinSum (fun index => family (index + 1)) terms)
            (family (terms + 1))))
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.add_right
          (carrierPolyFinSum_head_peel family terms)
          (family (terms + 1))) ?_
      intro insertion
      simp only [polyAdd, List.append_assoc]
      exact Q'.eqv_refl _

theorem tenHaarCarrierEqv_add_zero_left
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd polyZero polynomial) polynomial := by
  change TenHaarCarrierEqv polynomial polynomial
  exact TenHaarCarrierEqv.refl polynomial

theorem tenHaarCarrierEqv_add_zero_right
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd polynomial polyZero) polynomial := by
  intro insertion
  simp [polyAdd, polyZero]
  exact Q'.eqv_refl _

/-- A zero scalar is the zero object in the carrier quotient. -/
theorem tenHaarCarrierEqv_smul_zero
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polySmul 0 polynomial) polyZero := by
  intro insertion
  refine Q'.eqv_trans _
    ((0 : Q') * quaternionHaar 10 (polyMul insertion polynomial)) _
    (quaternionHaar_polyMul_smul_right 10 0 insertion polynomial) ?_
  refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) ?_
  rw [polyMul_zero_right_local]
  exact Q'.eqv_refl _

/-- Scalar addition distributes over a polynomial in the Haar quotient. -/
theorem tenHaarCarrierEqv_smul_add
    (leftScale rightScale : Q') (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polySmul (leftScale + rightScale) polynomial)
      (polyAdd
        (polySmul leftScale polynomial)
        (polySmul rightScale polynomial)) := by
  intro insertion
  refine Q'.eqv_trans _
    ((leftScale + rightScale) *
      quaternionHaar 10 (polyMul insertion polynomial)) _
    (quaternionHaar_polyMul_smul_right
      10 (leftScale + rightScale) insertion polynomial) ?_
  refine Q'.eqv_trans _
    (leftScale * quaternionHaar 10 (polyMul insertion polynomial) +
      rightScale * quaternionHaar 10 (polyMul insertion polynomial)) _
    (Q'.add_mul_eqv leftScale rightScale _) ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right 10 insertion
        (polySmul leftScale polynomial)
        (polySmul rightScale polynomial))
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_smul_right
          10 leftScale insertion polynomial)
        (quaternionHaar_polyMul_smul_right
          10 rightScale insertion polynomial)))
/-- A positive rational scalar cancels in the arbitrary-insertion Haar
quotient. -/
theorem tenHaarCarrierEqv_smul_cancel_of_pos
    {scale : Q'} (hscale : (0 : Q') < scale)
    {left right : RatPoly}
    (h : TenHaarCarrierEqv
      (polySmul scale left) (polySmul scale right)) :
    TenHaarCarrierEqv left right := by
  intro insertion
  have hscaled := h insertion
  have hleft := quaternionHaar_polyMul_smul_right
    10 scale insertion left
  have hright := quaternionHaar_polyMul_smul_right
    10 scale insertion right
  exact Q'.mul_left_cancel_of_pos hscale
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm hleft)
      (Q'.eqv_trans _ _ _ hscaled hright))

/-- Specialize arbitrary-insertion carrier equivalence to the bare tenfold
Haar contraction. -/
theorem tenHaarCarrierEqv_to_haar
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    quaternionHaar 10 left ≈ quaternionHaar 10 right := by
  have hone : ∀ polynomial : RatPoly,
      quaternionHaar 10 (polyMul polyOne polynomial) ≈
        quaternionHaar 10 polynomial := by
    intro polynomial
    exact Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm 10 polyOne polynomial)
      (quaternionHaar_polyMul_one_right 10 polynomial)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (hone left))
    (Q'.eqv_trans _ _ _ (h polyOne) (hone right))

/-! ## 2. Positive Taylor coefficient recurrence -/

/-- Multiplication by the degree clears the next factorial coefficient in
the polynomial Taylor term. -/
theorem positivePolynomialTaylorTerm_weighted
    (polynomial : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (polySmul (Q'.ofNat (degree + 1))
        (positivePolynomialTaylorTerm polynomial (degree + 1)))
      (polyMul polynomial
        (positivePolynomialTaylorTerm polynomial degree)) := by
  let nextPower := polynomialPower polynomial (degree + 1)
  let currentPower := polynomialPower polynomial degree
  have hscale :
      (Q'.ofNat (degree + 1) * ExpNeg.termAbs 1 (degree + 1)) ≈
        ExpNeg.termAbs 1 degree := by
    exact Q'.eqv_trans _ _ _
      (YMGap.Constructive.ofNat_succ_mul_termAbs 1 degree)
      (Q'.one_mul_eqv _)
  unfold positivePolynomialTaylorTerm
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_assoc
      (Q'.ofNat (degree + 1))
      (ExpNeg.termAbs 1 (degree + 1)) nextPower) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_coefficient hscale nextPower) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.smul (ExpNeg.termAbs 1 degree)
      (by
        change TenHaarCarrierEqv
          (polynomialPower polynomial (degree + 1))
          (polyMul polynomial currentPower)
        refine TenHaarCarrierEqv.trans
          (by
            rw [show degree + 1 = 1 + degree by omega]
            exact tenHaarCarrierEqv_power_add polynomial 1 degree) ?_
        have hone :
            TenHaarCarrierEqv
              (polynomialPower polynomial 1) polynomial := by
          change TenHaarCarrierEqv
            (polyMul polyOne polynomial) polynomial
          exact TenHaarCarrierEqv.trans
            (tenHaarCarrierEqv_mul_comm polyOne polynomial)
            (tenHaarCarrierEqv_mul_one polynomial)
        exact TenHaarCarrierEqv.mul_congr hone
          (TenHaarCarrierEqv.refl currentPower))) ?_
  exact TenHaarCarrierEqv.symm
    (tenHaarCarrierEqv_polyMul_smul_right
      (ExpNeg.termAbs 1 degree) polynomial currentPower)

/-! ## 3. Cauchy coefficients -/

/-- The `index`-th term in the total-degree `degree` Cauchy coefficient. -/
def positivePolynomialConvTerm
    (left right : RatPoly) (degree index : Nat) : RatPoly :=
  polyMul
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorTerm right (degree - index))

/-- Total-degree positive-polynomial Cauchy coefficient. -/
def positivePolynomialConv
    (left right : RatPoly) (degree : Nat) : RatPoly :=
  carrierPolyFinSum
    (positivePolynomialConvTerm left right degree)
    (degree + 1)

/-! ## 4. Weighted halves -/

/-- The index-weighted half of the next Cauchy coefficient. -/
def positivePolynomialConvIWeighted
    (left right : RatPoly) (degree index : Nat) : RatPoly :=
  polySmul (Q'.ofNat index)
    (positivePolynomialConvTerm left right (degree + 1) index)

/-- The complementary-index-weighted half. -/
def positivePolynomialConvJWeighted
    (left right : RatPoly) (degree index : Nat) : RatPoly :=
  polySmul (Q'.ofNat ((degree + 1) - index))
    (positivePolynomialConvTerm left right (degree + 1) index)

private theorem positivePolynomialConvIWeighted_zero
    (left right : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialConvIWeighted left right degree 0)
      polyZero := by
  unfold positivePolynomialConvIWeighted
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_coefficient
      Q'.ofNat_zero_eqv _) ?_
  exact tenHaarCarrierEqv_smul_zero _

private theorem positivePolynomialConvIWeighted_shift
    (left right : RatPoly) (degree index : Nat)
    (hindex : index < degree + 1) :
    TenHaarCarrierEqv
      (positivePolynomialConvIWeighted
        left right degree (index + 1))
      (polyMul left
        (positivePolynomialConvTerm left right degree index)) := by
  have hsub :
      (degree + 1) - (index + 1) = degree - index := by omega
  unfold positivePolynomialConvIWeighted
    positivePolynomialConvTerm
  rw [hsub]
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_polyMul_smul_left
        (Q'.ofNat (index + 1))
        (positivePolynomialTaylorTerm left (index + 1))
        (positivePolynomialTaylorTerm right (degree - index)))) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_congr
      (positivePolynomialTaylorTerm_weighted left index)
      (TenHaarCarrierEqv.refl _)) ?_
  exact tenHaarCarrierEqv_mul_assoc left
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorTerm right (degree - index))

/-- The index-weighted half collapses to left multiplication of the previous
Cauchy coefficient. -/
theorem positivePolynomial_iWeighted
    (left right : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (carrierPolyFinSum
        (positivePolynomialConvIWeighted left right degree)
        (degree + 2))
      (polyMul left (positivePolynomialConv left right degree)) := by
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_head_peel
      (positivePolynomialConvIWeighted left right degree)
      (degree + 1)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_congr
      (positivePolynomialConvIWeighted_zero left right degree)
      (carrierPolyFinSum_congr_lt
        (terms := degree + 1)
        (fun index hindex =>
          positivePolynomialConvIWeighted_shift
            left right degree index hindex))) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_add_zero_left _)
    (TenHaarCarrierEqv.symm
      (carrierPolyFinSum_mul_left left
        (positivePolynomialConvTerm left right degree)
        (degree + 1)))

private theorem positivePolynomialConvJWeighted_term
    (left right : RatPoly) (degree index : Nat)
    (hindex : index < degree + 1) :
    TenHaarCarrierEqv
      (positivePolynomialConvJWeighted left right degree index)
      (polyMul right
        (positivePolynomialConvTerm left right degree index)) := by
  let complement := degree - index
  have hsub : (degree + 1) - index = complement + 1 := by omega
  unfold positivePolynomialConvJWeighted
    positivePolynomialConvTerm
  rw [hsub]
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_polyMul_smul_right
        (Q'.ofNat (complement + 1))
        (positivePolynomialTaylorTerm left index)
        (positivePolynomialTaylorTerm right (complement + 1)))) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_congr
      (TenHaarCarrierEqv.refl _)
      (positivePolynomialTaylorTerm_weighted right complement)) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_comm
      (positivePolynomialTaylorTerm left index)
      (polyMul right
        (positivePolynomialTaylorTerm right complement))) ?_
  exact TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_assoc right
      (positivePolynomialTaylorTerm right complement)
      (positivePolynomialTaylorTerm left index))
    (TenHaarCarrierEqv.mul_left right
      (tenHaarCarrierEqv_mul_comm
        (positivePolynomialTaylorTerm right complement)
        (positivePolynomialTaylorTerm left index)))

private theorem positivePolynomialConvJWeighted_last
    (left right : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialConvJWeighted
        left right degree (degree + 1))
      polyZero := by
  unfold positivePolynomialConvJWeighted
  rw [Nat.sub_self]
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_coefficient
      Q'.ofNat_zero_eqv _) ?_
  exact tenHaarCarrierEqv_smul_zero _

/-- The complementary-index half collapses to right multiplication of the
previous Cauchy coefficient. -/
theorem positivePolynomial_jWeighted
    (left right : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (carrierPolyFinSum
        (positivePolynomialConvJWeighted left right degree)
        (degree + 2))
      (polyMul right (positivePolynomialConv left right degree)) := by
  change TenHaarCarrierEqv
    (polyAdd
      (carrierPolyFinSum
        (positivePolynomialConvJWeighted left right degree)
        (degree + 1))
      (positivePolynomialConvJWeighted
        left right degree (degree + 1)))
    (polyMul right (positivePolynomialConv left right degree))
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_congr
      (carrierPolyFinSum_congr_lt
        (terms := degree + 1)
        (fun index hindex =>
          positivePolynomialConvJWeighted_term
            left right degree index hindex))
      (positivePolynomialConvJWeighted_last
        left right degree)) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_add_zero_right _)
    (TenHaarCarrierEqv.symm
      (carrierPolyFinSum_mul_left right
        (positivePolynomialConvTerm left right degree)
        (degree + 1)))

/-! ## 5. Weighted recurrence and coefficient collapse -/

private theorem positivePolynomial_weight_split
    (left right : RatPoly) (degree index : Nat)
    (hindex : index < degree + 2) :
    TenHaarCarrierEqv
      (polySmul (Q'.ofNat (degree + 1))
        (positivePolynomialConvTerm left right (degree + 1) index))
      (polyAdd
        (positivePolynomialConvIWeighted left right degree index)
        (positivePolynomialConvJWeighted left right degree index)) := by
  have hle : index ≤ degree + 1 := Nat.lt_succ_iff.mp hindex
  have hnat : index + ((degree + 1) - index) = degree + 1 := by omega
  have hscale :
      Q'.ofNat (degree + 1) ≈
        Q'.ofNat index + Q'.ofNat ((degree + 1) - index) := by
    have h := Q'.ofNat_add_eqv index ((degree + 1) - index)
    rw [hnat] at h
    exact h
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_coefficient hscale _)
    (tenHaarCarrierEqv_smul_add
      (Q'.ofNat index)
      (Q'.ofNat ((degree + 1) - index)) _)

private theorem positivePolynomial_sum_mul_left
    (left right factor : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd (polyMul left factor) (polyMul right factor))
      (polyMul (polyAdd left right) factor) := by
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_congr
      (tenHaarCarrierEqv_mul_comm left factor)
      (tenHaarCarrierEqv_mul_comm right factor)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_polyMul_add_right factor left right)) ?_
  exact tenHaarCarrierEqv_mul_comm factor (polyAdd left right)

/-- `(degree+1)` times the next Cauchy coefficient is multiplication of the
previous coefficient by the sum polynomial. -/
theorem positivePolynomialConv_weighted
    (left right : RatPoly) (degree : Nat) :
    TenHaarCarrierEqv
      (polySmul (Q'.ofNat (degree + 1))
        (positivePolynomialConv left right (degree + 1)))
      (polyMul (polyAdd left right)
        (positivePolynomialConv left right degree)) := by
  unfold positivePolynomialConv
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_smul
      (Q'.ofNat (degree + 1))
      (positivePolynomialConvTerm left right (degree + 1))
      (degree + 2)) ?_
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_congr_lt
      (terms := degree + 2)
      (fun index hindex =>
        positivePolynomial_weight_split
          left right degree index hindex)) ?_
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_add
      (positivePolynomialConvIWeighted left right degree)
      (positivePolynomialConvJWeighted left right degree)
      (degree + 2)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_congr
      (positivePolynomial_iWeighted left right degree)
      (positivePolynomial_jWeighted left right degree)) ?_
  exact positivePolynomial_sum_mul_left left right
    (carrierPolyFinSum
      (positivePolynomialConvTerm left right degree)
      (degree + 1))

theorem positivePolynomialTaylorTerm_zero_eqv_one
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (positivePolynomialTaylorTerm polynomial 0) polyOne := by
  unfold positivePolynomialTaylorTerm
  change TenHaarCarrierEqv (polySmul 1 polyOne) polyOne
  exact tenHaarCarrierEqv_smul_one polyOne

/-- **Finite positive-polynomial Cauchy coefficient collapse.**  The complete
total-degree coefficient of `exp(left) exp(right)` is the matching Taylor
coefficient of `exp(left+right)` under every arbitrary ten-Haar insertion. -/
theorem positivePolynomialConv_eq_term
    (left right : RatPoly) :
    ∀ degree,
      TenHaarCarrierEqv
        (positivePolynomialConv left right degree)
        (positivePolynomialTaylorTerm
          (polyAdd left right) degree)
  | 0 => by
      unfold positivePolynomialConv
      change TenHaarCarrierEqv
        (polyAdd polyZero
          (positivePolynomialConvTerm left right 0 0))
        (positivePolynomialTaylorTerm (polyAdd left right) 0)
      refine TenHaarCarrierEqv.trans
        (tenHaarCarrierEqv_add_zero_left _)
        (TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.mul_congr
            (positivePolynomialTaylorTerm_zero_eqv_one left)
            (positivePolynomialTaylorTerm_zero_eqv_one right))
          (TenHaarCarrierEqv.trans
            (tenHaarCarrierEqv_mul_one polyOne)
            (TenHaarCarrierEqv.symm
              (positivePolynomialTaylorTerm_zero_eqv_one
                (polyAdd left right)))))
  | degree + 1 => by
      have hrec := positivePolynomialConv_weighted left right degree
      have hinduction := positivePolynomialConv_eq_term left right degree
      have hweighted :
          TenHaarCarrierEqv
            (polySmul (Q'.ofNat (degree + 1))
              (positivePolynomialConv left right (degree + 1)))
            (polySmul (Q'.ofNat (degree + 1))
              (positivePolynomialTaylorTerm
                (polyAdd left right) (degree + 1))) := by
        refine TenHaarCarrierEqv.trans hrec ?_
        refine TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.mul_left (polyAdd left right) hinduction) ?_
        exact TenHaarCarrierEqv.symm
          (positivePolynomialTaylorTerm_weighted
            (polyAdd left right) degree)
      exact tenHaarCarrierEqv_smul_cancel_of_pos
        (Q'.ofNat_succ_pos degree) hweighted

/-! ## 6. Rectangle, triangle, and the positive Mertens corner -/

theorem positivePolynomialTaylorPartial_eq_finSum
    (polynomial : RatPoly) :
    ∀ terms,
      positivePolynomialTaylorPartial polynomial terms =
        carrierPolyFinSum
          (positivePolynomialTaylorTerm polynomial) terms
  | 0 => rfl
  | terms + 1 => by
      change
        polyAdd
            (positivePolynomialTaylorPartial polynomial terms)
            (positivePolynomialTaylorTerm polynomial terms) =
          polyAdd
            (carrierPolyFinSum
              (positivePolynomialTaylorTerm polynomial) terms)
            (positivePolynomialTaylorTerm polynomial terms)
      rw [positivePolynomialTaylorPartial_eq_finSum polynomial terms]

theorem carrierPolyFinSum_mul_right
    (family : Nat → RatPoly) (factor : RatPoly) (terms : Nat) :
    TenHaarCarrierEqv
      (polyMul (carrierPolyFinSum family terms) factor)
      (carrierPolyFinSum
        (fun index => polyMul (family index) factor) terms) := by
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_comm
      (carrierPolyFinSum family terms) factor) ?_
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_mul_left factor family terms) ?_
  exact carrierPolyFinSum_congr
    (fun index => tenHaarCarrierEqv_mul_comm
      factor (family index)) terms

theorem tenHaarCarrierEqv_add_assoc
    (first second third : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd (polyAdd first second) third)
      (polyAdd first (polyAdd second third)) := by
  intro insertion
  simp only [polyAdd, List.append_assoc]
  exact Q'.eqv_refl _

/-- One triangular row in the rectangle, containing total degrees below the
current cutoff. -/
def positivePolynomialTriangleTerm
    (left right : RatPoly) (terms index : Nat) : RatPoly :=
  polyMul
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorPartial right (terms - index))

/-- The lower total-degree triangle inside the square Taylor rectangle. -/
def positivePolynomialTriangle
    (left right : RatPoly) (terms : Nat) : RatPoly :=
  carrierPolyFinSum
    (positivePolynomialTriangleTerm left right terms) terms

/-- One row of the complementary upper-right Mertens corner. -/
def positivePolynomialCornerTerm
    (left right : RatPoly) (terms index : Nat) : RatPoly :=
  polyMul
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorBlock right
      (terms - index) index)

/-- Positive polynomial representative of the rectangular Mertens corner. -/
def positivePolynomialCorner
    (left right : RatPoly) (terms : Nat) : RatPoly :=
  carrierPolyFinSum
    (positivePolynomialCornerTerm left right terms) terms

private theorem positivePolynomialTriangle_row_succ
    (left right : RatPoly) (terms index : Nat)
    (hindex : index < terms) :
    TenHaarCarrierEqv
      (positivePolynomialTriangleTerm
        left right (terms + 1) index)
      (polyAdd
        (positivePolynomialTriangleTerm left right terms index)
        (positivePolynomialConvTerm left right terms index)) := by
  have hsub : (terms + 1) - index = (terms - index) + 1 := by omega
  unfold positivePolynomialTriangleTerm
    positivePolynomialConvTerm
  rw [hsub]
  change TenHaarCarrierEqv
    (polyMul (positivePolynomialTaylorTerm left index)
      (polyAdd
        (positivePolynomialTaylorPartial right (terms - index))
        (positivePolynomialTaylorTerm right (terms - index))))
    (polyAdd
      (polyMul (positivePolynomialTaylorTerm left index)
        (positivePolynomialTaylorPartial right (terms - index)))
      (polyMul (positivePolynomialTaylorTerm left index)
        (positivePolynomialTaylorTerm right (terms - index))))
  exact tenHaarCarrierEqv_polyMul_add_right
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorPartial right (terms - index))
    (positivePolynomialTaylorTerm right (terms - index))

private theorem positivePolynomialTriangle_last
    (left right : RatPoly) (terms : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialTriangleTerm
        left right (terms + 1) terms)
      (positivePolynomialConvTerm left right terms terms) := by
  unfold positivePolynomialTriangleTerm
    positivePolynomialConvTerm
  rw [show (terms + 1) - terms = 1 by omega]
  change TenHaarCarrierEqv
    (polyMul (positivePolynomialTaylorTerm left terms)
      (polyAdd polyZero
        (positivePolynomialTaylorTerm right 0)))
    (polyMul (positivePolynomialTaylorTerm left terms)
      (positivePolynomialTaylorTerm right (terms - terms)))
  rw [Nat.sub_self]
  exact TenHaarCarrierEqv.mul_left
    (positivePolynomialTaylorTerm left terms)
    (tenHaarCarrierEqv_add_zero_left
      (positivePolynomialTaylorTerm right 0))

/-- The lower triangle gains exactly the next total-degree Cauchy
coefficient. -/
theorem positivePolynomialTriangle_succ
    (left right : RatPoly) (terms : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialTriangle left right (terms + 1))
      (polyAdd
        (positivePolynomialTriangle left right terms)
        (positivePolynomialConv left right terms)) := by
  unfold positivePolynomialTriangle positivePolynomialConv
  change TenHaarCarrierEqv
    (polyAdd
      (carrierPolyFinSum
        (positivePolynomialTriangleTerm left right (terms + 1)) terms)
      (positivePolynomialTriangleTerm left right (terms + 1) terms))
    (polyAdd
      (carrierPolyFinSum
        (positivePolynomialTriangleTerm left right terms) terms)
      (polyAdd
        (carrierPolyFinSum
          (positivePolynomialConvTerm left right terms) terms)
        (positivePolynomialConvTerm left right terms terms)))
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_congr
      (carrierPolyFinSum_congr_lt
        (terms := terms)
        (fun index hindex =>
          positivePolynomialTriangle_row_succ
            left right terms index hindex))
      (positivePolynomialTriangle_last left right terms)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_right
      (carrierPolyFinSum_add
        (positivePolynomialTriangleTerm left right terms)
        (positivePolynomialConvTerm left right terms)
        terms)
      (positivePolynomialConvTerm left right terms terms)) ?_
  exact tenHaarCarrierEqv_add_assoc
    (carrierPolyFinSum
      (positivePolynomialTriangleTerm left right terms) terms)
    (carrierPolyFinSum
      (positivePolynomialConvTerm left right terms) terms)
    (positivePolynomialConvTerm left right terms terms)

/-- The complete triangle is the Taylor partial of the sum polynomial. -/
theorem positivePolynomialTriangle_eq_partial
    (left right : RatPoly) :
    ∀ terms,
      TenHaarCarrierEqv
        (positivePolynomialTriangle left right terms)
        (positivePolynomialTaylorPartial
          (polyAdd left right) terms)
  | 0 => TenHaarCarrierEqv.refl polyZero
  | terms + 1 => by
      change TenHaarCarrierEqv
        (positivePolynomialTriangle left right (terms + 1))
        (polyAdd
          (positivePolynomialTaylorPartial
            (polyAdd left right) terms)
          (positivePolynomialTaylorTerm
            (polyAdd left right) terms))
      exact TenHaarCarrierEqv.trans
        (positivePolynomialTriangle_succ left right terms)
        (TenHaarCarrierEqv.add_congr
          (positivePolynomialTriangle_eq_partial
            left right terms)
          (positivePolynomialConv_eq_term left right terms))

private theorem positivePolynomialRectangle_row_decompose
    (left right : RatPoly) (terms index : Nat)
    (hindex : index < terms) :
    TenHaarCarrierEqv
      (polyMul
        (positivePolynomialTaylorTerm left index)
        (positivePolynomialTaylorPartial right terms))
      (polyAdd
        (positivePolynomialTriangleTerm left right terms index)
        (positivePolynomialCornerTerm left right terms index)) := by
  have hsum : (terms - index) + index = terms := by omega
  have hblock := positivePolynomialTaylorPartial_add_block
    right (terms - index) index
  rw [hsum] at hblock
  rw [hblock]
  unfold positivePolynomialTriangleTerm
    positivePolynomialCornerTerm
  exact tenHaarCarrierEqv_polyMul_add_right
    (positivePolynomialTaylorTerm left index)
    (positivePolynomialTaylorPartial right (terms - index))
    (positivePolynomialTaylorBlock right (terms - index) index)

/-- **Finite rectangle/triangle/corner identity.** -/
theorem positivePolynomialRectangle_eq_triangle_add_corner
    (left right : RatPoly) (terms : Nat) :
    TenHaarCarrierEqv
      (polyMul
        (positivePolynomialTaylorPartial left terms)
        (positivePolynomialTaylorPartial right terms))
      (polyAdd
        (positivePolynomialTriangle left right terms)
        (positivePolynomialCorner left right terms)) := by
  rw [positivePolynomialTaylorPartial_eq_finSum left terms]
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_mul_right
      (positivePolynomialTaylorTerm left)
      (positivePolynomialTaylorPartial right terms) terms) ?_
  refine TenHaarCarrierEqv.trans
    (carrierPolyFinSum_congr_lt
      (terms := terms)
      (fun index hindex =>
        positivePolynomialRectangle_row_decompose
          left right terms index hindex)) ?_
  exact carrierPolyFinSum_add
    (positivePolynomialTriangleTerm left right terms)
    (positivePolynomialCornerTerm left right terms)
    terms

/-- Rectangle equals the Taylor partial of the sum plus the positive corner. -/
theorem positivePolynomialRectangle_eq_partial_add_corner
    (left right : RatPoly) (terms : Nat) :
    TenHaarCarrierEqv
      (polyMul
        (positivePolynomialTaylorPartial left terms)
        (positivePolynomialTaylorPartial right terms))
      (polyAdd
        (positivePolynomialTaylorPartial
          (polyAdd left right) terms)
        (positivePolynomialCorner left right terms)) :=
  TenHaarCarrierEqv.trans
    (positivePolynomialRectangle_eq_triangle_add_corner
      left right terms)
    (TenHaarCarrierEqv.add_right
      (positivePolynomialTriangle_eq_partial
        left right terms)
      (positivePolynomialCorner left right terms))

/-! ## 7. Coefficient-L1 domination of the Mertens corner -/

theorem polynomialCoefficientL1_carrierPolyFinSum_le
    (family : Nat → RatPoly) :
    ∀ terms,
      polynomialCoefficientL1
          (carrierPolyFinSum family terms) ≤
        finSum (fun index =>
          polynomialCoefficientL1 (family index)) terms
  | 0 => Q'.le_refl' 0
  | terms + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (carrierPolyFinSum family terms)
            (family terms))) ?_
      exact Q'.add_le_add
        (polynomialCoefficientL1_carrierPolyFinSum_le
          family terms)
        (Q'.le_refl' _)

theorem positivePolynomialCornerTerm_l1_le
    (left right : RatPoly) (terms index : Nat) :
    polynomialCoefficientL1
        (positivePolynomialCornerTerm left right terms index) ≤
      cornerAbsTermAdd
        (positivePolynomialTaylorL1 left)
        (positivePolynomialTaylorL1 right)
        terms index := by
  let leftTerm :=
    positivePolynomialTaylorTerm left index
  let rightBlock :=
    positivePolynomialTaylorBlock right
      (terms - index) index
  have hleft0 :
      (0 : Q') ≤ polynomialCoefficientL1 leftTerm :=
    polynomialCoefficientL1_nonnegative _
  have hright0 :
      (0 : Q') ≤ polynomialCoefficientL1 rightBlock :=
    polynomialCoefficientL1_nonnegative _
  have hleft :
      polynomialCoefficientL1 leftTerm ≤
        ExpNeg.termAbs
          (positivePolynomialTaylorL1 left) index :=
    positivePolynomialTaylorTerm_l1_le left index
  have hright :
      polynomialCoefficientL1 rightBlock ≤
        ExpNeg.blockAbs
          (positivePolynomialTaylorL1 right)
          (terms - index) index :=
    Q'.le_trans' _ _ _
      (positivePolynomialTaylorBlock_l1_le
        right (terms - index) index)
      (positivePolynomialTaylorL1Block_le
        right (terms - index) index)
  unfold positivePolynomialCornerTerm
    cornerAbsTermAdd
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_mul_le leftTerm rightBlock) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hright
    (ExpNeg.termAbs_nonneg
      (positivePolynomialTaylorL1 left)
      (positivePolynomialTaylorL1_nonnegative left) index)

/-- The syntactic coefficient mass of the polynomial corner is dominated by
the scalar Mertens corner at the two polynomial coefficient norms. -/
theorem positivePolynomialCorner_l1_le_cornerAbs
    (left right : RatPoly) (terms : Nat) :
    polynomialCoefficientL1
        (positivePolynomialCorner left right terms) ≤
      cornerAbsAdd
        (positivePolynomialTaylorL1 left)
        (positivePolynomialTaylorL1 right)
        terms := by
  unfold positivePolynomialCorner cornerAbsAdd
  exact Q'.le_trans' _ _ _
    (polynomialCoefficientL1_carrierPolyFinSum_le
      (positivePolynomialCornerTerm left right terms) terms)
    (finSum_le_finSum_of_termwise
      (fun index => polynomialCoefficientL1
        (positivePolynomialCornerTerm left right terms index))
      (cornerAbsTermAdd
        (positivePolynomialTaylorL1 left)
        (positivePolynomialTaylorL1 right) terms)
      (fun index =>
        positivePolynomialCornerTerm_l1_le
          left right terms index)
      terms)

/-! ## 8. Explicit positive-polynomial Mertens modulus -/

/-- Uniform scalar mass paid by the two complete positive Taylor factors. -/
def positivePolynomialMertensScale
    (left right : RatPoly) : Q' :=
  positivePolynomialTaylorBound left +
    positivePolynomialTaylorBound right

theorem positivePolynomialMertensScale_nonnegative
    (left right : RatPoly) :
    (0 : Q') ≤ positivePolynomialMertensScale left right :=
  Q'.zero_le_add _ _
    (positivePolynomialTaylorBound_nonnegative left)
    (positivePolynomialTaylorBound_nonnegative right)

/-- Tail tolerance before restoring the two-factor Mertens scale. -/
def positivePolynomialMertensDelta
    (left right : RatPoly) (epsilon : Q') : Q' :=
  epsilon * Q'.invSucc
    (positivePolynomialMertensScale left right).num.toNat

theorem positivePolynomialMertensDelta_pos
    (left right : RatPoly) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < positivePolynomialMertensDelta left right epsilon :=
  Q'.mul_pos hepsilon
    (Q'.invSucc_pos
      (positivePolynomialMertensScale left right).num.toNat)

/-- Left-tail split point for the explicit corner estimate. -/
def positivePolynomialMertensLeftCutoff
    (left right : RatPoly) (epsilon : Q') : Nat :=
  let delta := positivePolynomialMertensDelta left right epsilon
  max
    (halfRatioCutoff (positivePolynomialTaylorL1 left))
    (termAbsModulus
      (positivePolynomialTaylorL1 left)
      (HalfPow.half * delta))

/-- Explicit two-factor Mertens modulus. -/
def positivePolynomialMertensModulus
    (left right : RatPoly) (epsilon : Q') : Nat :=
  let delta := positivePolynomialMertensDelta left right epsilon
  positivePolynomialMertensLeftCutoff left right epsilon +
    termAbsModulus
      (positivePolynomialTaylorL1 right)
      (HalfPow.half * delta)

/-- The scalar Mertens corner is below `epsilon` past the explicit polynomial
modulus. -/
theorem positivePolynomialCornerAbs_le_of_modulus
    (left right : RatPoly)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (terms : Nat)
    (hterms :
      positivePolynomialMertensModulus left right epsilon ≤ terms) :
    cornerAbsAdd
        (positivePolynomialTaylorL1 left)
        (positivePolynomialTaylorL1 right) terms ≤
      epsilon := by
  let a := positivePolynomialTaylorL1 left
  let b := positivePolynomialTaylorL1 right
  let Ba := positivePolynomialTaylorBound left
  let Bb := positivePolynomialTaylorBound right
  let scale := positivePolynomialMertensScale left right
  let delta := positivePolynomialMertensDelta left right epsilon
  let K := positivePolynomialMertensLeftCutoff left right epsilon
  have ha : (0 : Q') ≤ a :=
    positivePolynomialTaylorL1_nonnegative left
  have hb : (0 : Q') ≤ b :=
    positivePolynomialTaylorL1_nonnegative right
  have hBa0 : (0 : Q') ≤ Ba :=
    positivePolynomialTaylorBound_nonnegative left
  have hBb0 : (0 : Q') ≤ Bb :=
    positivePolynomialTaylorBound_nonnegative right
  have hscale0 : (0 : Q') ≤ scale :=
    positivePolynomialMertensScale_nonnegative left right
  have hdelta : (0 : Q') < delta :=
    positivePolynomialMertensDelta_pos
      left right epsilon hepsilon
  have hdelta0 : (0 : Q') ≤ delta := Q'.le_of_lt hdelta
  have hhalfDelta : (0 : Q') < HalfPow.half * delta :=
    ExpNeg.half_mul_pos delta hdelta
  have hKcut : halfRatioCutoff a ≤ K := by
    unfold K positivePolynomialMertensLeftCutoff
    exact Nat.le_max_left _ _
  have hKmod : termAbsModulus a (HalfPow.half * delta) ≤ K := by
    unfold K positivePolynomialMertensLeftCutoff
    exact Nat.le_max_right _ _
  have hrightCut :
      halfRatioCutoff b ≤
        termAbsModulus b (HalfPow.half * delta) := by
    unfold termAbsModulus
    exact Nat.le_add_right _ _
  have hKm : K ≤ terms := by
    exact Nat.le_trans (Nat.le_add_right _ _) hterms
  obtain ⟨distance, hdistance⟩ := Nat.exists_eq_add_of_le hKm
  subst terms
  have hsplit :
      cornerAbsAdd a b (K + distance) ≈
        finSum (cornerAbsTermAdd a b (K + distance)) K +
          finSum (fun offset =>
            cornerAbsTermAdd a b (K + distance) (K + offset))
            distance :=
    finSum_split (cornerAbsTermAdd a b (K + distance)) K distance
  have hpart1 :
      finSum (cornerAbsTermAdd a b (K + distance)) K ≤
        Ba * delta := by
    have hterm : ∀ index, index < K →
        cornerAbsTermAdd a b (K + distance) index ≤
          ExpNeg.termAbs a index * delta := by
      intro index hindex
      have hmod :
          termAbsModulus b (HalfPow.half * delta) ≤
            (K + distance) - index := by
        have hbase :
            K + termAbsModulus b (HalfPow.half * delta) ≤
              K + distance := by
          simpa [positivePolynomialMertensModulus, K, b, delta]
            using hterms
        have hdistance :
            termAbsModulus b (HalfPow.half * delta) ≤ distance := by
          omega
        omega
      have hblock :
          ExpNeg.blockAbs b ((K + distance) - index) index ≤
            delta :=
        expNeg_tail_bound b hb delta hdelta0
          ((K + distance) - index)
          (Nat.le_trans hrightCut hmod)
          (termAbs_le_of_modulus_le b
            (HalfPow.half * delta) hb hhalfDelta
            ((K + distance) - index) hmod)
          index
      exact Q'.mul_le_mul_of_nonneg_left _ _
        (ExpNeg.termAbs a index) hblock
        (termAbs_nonneg a ha index)
    refine Q'.le_trans' _ _ _
      (finSum_le_lt
        (cornerAbsTermAdd a b (K + distance))
        (fun index => ExpNeg.termAbs a index * delta)
        K hterm) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (finSum_mul_const (ExpNeg.termAbs a) delta K))) ?_
    rw [← partialSumAbs_eq_finSum]
    exact Q'.mul_le_mul_of_nonneg_right
      (partialSumAbs a K) Ba delta
      (partialSumAbs_le_expPosBound a ha K) hdelta0
  have hpart2 :
      finSum (fun offset =>
        cornerAbsTermAdd a b (K + distance) (K + offset))
        distance ≤ delta * Bb := by
    have hterm : ∀ offset,
        cornerAbsTermAdd a b (K + distance) (K + offset) ≤
          ExpNeg.termAbs a (K + offset) * Bb := by
      intro offset
      exact Q'.mul_le_mul_of_nonneg_left _ _
        (ExpNeg.termAbs a (K + offset))
        (blockAbs_le_bound b hb
          (fun cutoff => partialSumAbs_le_expPosBound b hb cutoff)
          ((K + distance) - (K + offset)) (K + offset))
        (termAbs_nonneg a ha (K + offset))
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise
        (fun offset =>
          cornerAbsTermAdd a b (K + distance) (K + offset))
        (fun offset => ExpNeg.termAbs a (K + offset) * Bb)
        hterm distance) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (finSum_mul_const
            (fun offset => ExpNeg.termAbs a (K + offset))
            Bb distance))) ?_
    rw [← blockAbs_eq_finSum]
    have hblock : ExpNeg.blockAbs a K distance ≤ delta :=
      expNeg_tail_bound a ha delta hdelta0 K hKcut
        (termAbs_le_of_modulus_le a
          (HalfPow.half * delta) ha hhalfDelta K hKmod)
        distance
    exact Q'.mul_le_mul_of_nonneg_right
      (ExpNeg.blockAbs a K distance) delta Bb
      hblock hBb0
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (ExpNeg.mul_le_of_mul_invSucc_toNat
      scale epsilon hscale0 (Q'.le_of_lt hepsilon))
  change Ba * delta + delta * Bb ≈ scale * delta
  refine Q'.eqv_trans _ (Ba * delta + Bb * delta) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv delta Bb)) ?_
  change Ba * delta + Bb * delta ≈ (Ba + Bb) * delta
  exact Q'.eqv_symm (Q'.add_mul_eqv Ba Bb delta)

/-- **Explicit coefficient-L1 Mertens bound.** -/
theorem positivePolynomialCorner_l1_le_of_modulus
    (left right : RatPoly)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (terms : Nat)
    (hterms :
      positivePolynomialMertensModulus left right epsilon ≤ terms) :
    polynomialCoefficientL1
        (positivePolynomialCorner left right terms) ≤ epsilon :=
  Q'.le_trans' _ _ _
    (positivePolynomialCorner_l1_le_cornerAbs left right terms)
    (positivePolynomialCornerAbs_le_of_modulus
      left right epsilon hepsilon terms hterms)

/-! ## 9. Scaled Haar-level Mertens theorem -/

/-- Mertens cutoff after paying a uniform coefficient bound for the external
Haar insertion. -/
def positivePolynomialScaledMertensModulus
    (left right : RatPoly) (scale epsilon : Q') : Nat :=
  positivePolynomialMertensModulus left right
    (abstractPacketScaledTailTolerance scale epsilon)

theorem positivePolynomialCorner_scaled_l1_le
    (left right : RatPoly) (scale epsilon : Q')
    (hscale : (0 : Q') ≤ scale)
    (hepsilon : (0 : Q') < epsilon)
    (terms : Nat)
    (hterms :
      positivePolynomialScaledMertensModulus
        left right scale epsilon ≤ terms) :
    scale * polynomialCoefficientL1
        (positivePolynomialCorner left right terms) ≤ epsilon := by
  let delta := abstractPacketScaledTailTolerance scale epsilon
  have hdelta : (0 : Q') < delta :=
    abstractPacketScaledTailTolerance_pos scale epsilon hepsilon
  have hcorner :
      polynomialCoefficientL1
          (positivePolynomialCorner left right terms) ≤ delta :=
    positivePolynomialCorner_l1_le_of_modulus
      left right delta hdelta terms hterms
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ scale hcorner hscale) ?_
  exact ExpNeg.mul_le_of_mul_invSucc_toNat
    scale epsilon hscale (Q'.le_of_lt hepsilon)

private theorem add_increment_close_local
    (earlier later increment epsilon : Q')
    (hdecompose : later ≈ earlier + increment)
    (hbound : Q'.abs increment ≤ epsilon) :
    later ≤ earlier + epsilon ∧
      earlier ≤ later + epsilon := by
  have hdifference : later + (-earlier) ≈ increment := by
    refine Q'.eqv_trans _
      ((earlier + increment) + (-earlier)) _
      (Q'.add_eqv_congr_right _ _ (-earlier) hdecompose) ?_
    refine Q'.eqv_trans _
      (earlier + (increment + (-earlier))) _
      (Q'.add_assoc_eqv earlier increment (-earlier)) ?_
    refine Q'.eqv_trans _
      (earlier + ((-earlier) + increment)) _
      (Q'.add_eqv_congr_left earlier _ _
        (Q'.add_comm_eqv increment (-earlier))) ?_
    refine Q'.eqv_trans _
      ((earlier + (-earlier)) + increment) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv earlier (-earlier) increment)) ?_
    refine Q'.eqv_trans _ (0 + increment) _
      (Q'.add_eqv_congr_right _ _ increment
        (Q'.add_neg_self_eqv earlier)) ?_
    exact QPoly.q_zero_add_eqv increment
  have habs : Q'.abs (later + (-earlier)) ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hbound
  exact
    ⟨ExpNeg.le_add_of_abs_sub_le habs,
     ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm earlier later))
        habs)⟩

/-- **Quantitative two-factor polynomial Mertens theorem under Haar.**  An
arbitrary external insertion is permitted, provided its coefficient mass is
bounded by `scale`. -/
theorem positivePolynomialRectangleHaar_close_sumPartial
    (insertion left right : RatPoly)
    (scale epsilon : Q')
    (hscale : (0 : Q') ≤ scale)
    (hinsertion : polynomialCoefficientL1 insertion ≤ scale)
    (hepsilon : (0 : Q') < epsilon)
    (terms : Nat)
    (hterms :
      positivePolynomialScaledMertensModulus
        left right scale epsilon ≤ terms) :
    let rectangle := quaternionHaar 10
      (polyMul insertion
        (polyMul
          (positivePolynomialTaylorPartial left terms)
          (positivePolynomialTaylorPartial right terms)))
    let collapsed := quaternionHaar 10
      (polyMul insertion
        (positivePolynomialTaylorPartial
          (polyAdd left right) terms))
    rectangle ≤ collapsed + epsilon ∧
      collapsed ≤ rectangle + epsilon := by
  let rectangle := quaternionHaar 10
    (polyMul insertion
      (polyMul
        (positivePolynomialTaylorPartial left terms)
        (positivePolynomialTaylorPartial right terms)))
  let collapsed := quaternionHaar 10
    (polyMul insertion
      (positivePolynomialTaylorPartial
        (polyAdd left right) terms))
  let corner := quaternionHaar 10
    (polyMul insertion
      (positivePolynomialCorner left right terms))
  have hdecompose : rectangle ≈ collapsed + corner := by
    exact Q'.eqv_trans _ _ _
      ((positivePolynomialRectangle_eq_partial_add_corner
        left right terms) insertion)
      (quaternionHaar_polyMul_add_right 10 insertion
        (positivePolynomialTaylorPartial
          (polyAdd left right) terms)
        (positivePolynomialCorner left right terms))
  have hinsertion0 :
      (0 : Q') ≤ polynomialCoefficientL1 insertion :=
    polynomialCoefficientL1_nonnegative insertion
  have hcorner0 :
      (0 : Q') ≤ polynomialCoefficientL1
        (positivePolynomialCorner left right terms) :=
    polynomialCoefficientL1_nonnegative _
  have hcornerL1 :
      polynomialCoefficientL1
          (polyMul insertion
            (positivePolynomialCorner left right terms)) ≤
        scale * polynomialCoefficientL1
          (positivePolynomialCorner left right terms) := by
    refine Q'.le_trans' _ _ _
      (polynomialCoefficientL1_mul_le insertion
        (positivePolynomialCorner left right terms)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      hinsertion hcorner0
  have hcornerAbs : Q'.abs corner ≤ epsilon :=
    Q'.le_trans' _ _ _
      (quaternionHaar_abs_le_coefficientL1 10
        (polyMul insertion
          (positivePolynomialCorner left right terms)))
      (Q'.le_trans' _ _ _ hcornerL1
        (positivePolynomialCorner_scaled_l1_le
          left right scale epsilon hscale hepsilon
          terms hterms))
  exact add_increment_close_local
    collapsed rectangle corner epsilon hdecompose hcornerAbs

/-! ## 10. The BF4 three-factor Mertens collapse -/

/-- External coefficient scale for collapsing the source and target factors
while retaining the kinetic-cross partial. -/
def abstractPacketSourceTargetMertensScale
    (packet : BF4HolonomyStatePacket) : Q' :=
  abstractPacketBoundaryL1 packet *
    abstractPacketCrossTaylorBound

theorem abstractPacketSourceTargetMertensScale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ abstractPacketSourceTargetMertensScale packet :=
  Q'.mul_nonneg _ _
    (abstractPacketBoundaryL1_nonnegative packet)
    abstractPacketCrossTaylorBound_nonnegative

/-- Common cutoff for the two consecutive Cauchy-product collapses. -/
def abstractPacketThreeFactorMertensModulus
    (packet : BF4HolonomyStatePacket) (epsilon : Q') : Nat :=
  max
    (positivePolynomialScaledMertensModulus
      sourceDiagonalComplementPolynomial
      targetDiagonalComplementPolynomial
      (abstractPacketSourceTargetMertensScale packet)
      (HalfPow.half * epsilon))
    (positivePolynomialScaledMertensModulus
      (polyAdd sourceDiagonalComplementPolynomial
        targetDiagonalComplementPolynomial)
      sourceTargetKineticCrossPolynomial
      (abstractPacketBoundaryL1 packet)
      (HalfPow.half * epsilon))

private theorem close_congr_local
    {first first' second second' epsilon : Q'}
    (hfirst : first ≈ first')
    (hsecond : second ≈ second')
    (hclose : first' ≤ second' + epsilon ∧
      second' ≤ first' + epsilon) :
    first ≤ second + epsilon ∧
      second ≤ first + epsilon := by
  constructor
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfirst) ?_
    refine Q'.le_trans' _ _ _ hclose.1 ?_
    exact Q'.add_le_add_right _ _ epsilon
      (Q'.le_of_eqv (Q'.eqv_symm hsecond))
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsecond) ?_
    refine Q'.le_trans' _ _ _ hclose.2 ?_
    exact Q'.add_le_add_right _ _ epsilon
      (Q'.le_of_eqv (Q'.eqv_symm hfirst))

private theorem two_halves_trans_mertens
    (first middle last epsilon : Q')
    (hfirst : first ≤ middle + HalfPow.half * epsilon)
    (hlast : middle ≤ last + HalfPow.half * epsilon) :
    first ≤ last + epsilon := by
  refine Q'.le_trans' _ _ _ hfirst ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (HalfPow.half * epsilon) hlast) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (last +
      ((HalfPow.half * epsilon) +
        (HalfPow.half * epsilon))) _
    (Q'.add_assoc_eqv last
      (HalfPow.half * epsilon)
      (HalfPow.half * epsilon)) ?_
  exact Q'.add_eqv_congr_left last _ _
    (ExpNeg.two_halves epsilon)

private theorem abstractPacketSourceTarget_reorder
    (packet : BF4HolonomyStatePacket) (terms : Nat) :
    let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
    let source := positivePolynomialTaylorPartial
      sourceDiagonalComplementPolynomial terms
    let target := positivePolynomialTaylorPartial
      targetDiagonalComplementPolynomial terms
    let cross := positivePolynomialTaylorPartial
      sourceTargetKineticCrossPolynomial terms
    TenHaarCarrierEqv
      (polyMul boundary (polyMul (polyMul source target) cross))
      (polyMul (polyMul boundary cross) (polyMul source target)) := by
  dsimp only
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_left
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (tenHaarCarrierEqv_mul_comm
        (polyMul
          (positivePolynomialTaylorPartial
            sourceDiagonalComplementPolynomial terms)
          (positivePolynomialTaylorPartial
            targetDiagonalComplementPolynomial terms))
        (positivePolynomialTaylorPartial
          sourceTargetKineticCrossPolynomial terms))) ?_
  exact TenHaarCarrierEqv.symm
    (tenHaarCarrierEqv_mul_assoc
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (positivePolynomialTaylorPartial
        sourceTargetKineticCrossPolynomial terms)
      (polyMul
        (positivePolynomialTaylorPartial
          sourceDiagonalComplementPolynomial terms)
        (positivePolynomialTaylorPartial
          targetDiagonalComplementPolynomial terms)))

private theorem abstractPacketCollapsedSourceTarget_reorder
    (packet : BF4HolonomyStatePacket) (terms : Nat) :
    let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
    let sourceTarget := positivePolynomialTaylorPartial
      (polyAdd sourceDiagonalComplementPolynomial
        targetDiagonalComplementPolynomial) terms
    let cross := positivePolynomialTaylorPartial
      sourceTargetKineticCrossPolynomial terms
    TenHaarCarrierEqv
      (polyMul (polyMul boundary cross) sourceTarget)
      (polyMul boundary (polyMul sourceTarget cross)) := by
  dsimp only
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_assoc
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (positivePolynomialTaylorPartial
        sourceTargetKineticCrossPolynomial terms)
      (positivePolynomialTaylorPartial
        (polyAdd sourceDiagonalComplementPolynomial
          targetDiagonalComplementPolynomial) terms)) ?_
  exact TenHaarCarrierEqv.mul_left
    (bf4PacketRawReflectedBoundaryPolynomial packet)
    (tenHaarCarrierEqv_mul_comm
      (positivePolynomialTaylorPartial
        sourceTargetKineticCrossPolynomial terms)
      (positivePolynomialTaylorPartial
        (polyAdd sourceDiagonalComplementPolynomial
          targetDiagonalComplementPolynomial) terms))

private theorem groupedPositiveComponent_assoc_exact :
    polyAdd
        (polyAdd sourceDiagonalComplementPolynomial
          targetDiagonalComplementPolynomial)
        sourceTargetKineticCrossPolynomial =
      groupedPositiveComponentPolynomial := by
  unfold groupedPositiveComponentPolynomial polyAdd
  exact List.append_assoc _ _ _

/-- **Three-factor BF4 Mertens estimate.**  The equal-cutoff rectangular
packet contraction is uniformly close to the single Taylor partial of the
grouped positive component polynomial. -/
theorem abstractPacketThreeFactorHaar_close_groupedPartial
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (terms : Nat)
    (hterms :
      abstractPacketThreeFactorMertensModulus packet epsilon ≤ terms) :
    abstractPacketRectangularHaar terms terms terms packet ≤
        quaternionHaar 10
          (polyMul
            (bf4PacketRawReflectedBoundaryPolynomial packet)
            (positivePolynomialTaylorPartial
              groupedPositiveComponentPolynomial terms)) + epsilon ∧
      quaternionHaar 10
          (polyMul
            (bf4PacketRawReflectedBoundaryPolynomial packet)
            (positivePolynomialTaylorPartial
              groupedPositiveComponentPolynomial terms)) ≤
        abstractPacketRectangularHaar terms terms terms packet + epsilon := by
  let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
  let source := positivePolynomialTaylorPartial
    sourceDiagonalComplementPolynomial terms
  let target := positivePolynomialTaylorPartial
    targetDiagonalComplementPolynomial terms
  let cross := positivePolynomialTaylorPartial
    sourceTargetKineticCrossPolynomial terms
  let sourceTarget := positivePolynomialTaylorPartial
    (polyAdd sourceDiagonalComplementPolynomial
      targetDiagonalComplementPolynomial) terms
  let middle := quaternionHaar 10
    (polyMul boundary (polyMul sourceTarget cross))
  let grouped := quaternionHaar 10
    (polyMul boundary
      (positivePolynomialTaylorPartial
        groupedPositiveComponentPolynomial terms))
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hfirstCut :
      positivePolynomialScaledMertensModulus
          sourceDiagonalComplementPolynomial
          targetDiagonalComplementPolynomial
          (abstractPacketSourceTargetMertensScale packet)
          (HalfPow.half * epsilon) ≤ terms :=
    Nat.le_trans (Nat.le_max_left _ _) hterms
  have hsecondCut :
      positivePolynomialScaledMertensModulus
          (polyAdd sourceDiagonalComplementPolynomial
            targetDiagonalComplementPolynomial)
          sourceTargetKineticCrossPolynomial
          (abstractPacketBoundaryL1 packet)
          (HalfPow.half * epsilon) ≤ terms :=
    Nat.le_trans (Nat.le_max_right _ _) hterms
  have hinsertionFirst :
      polynomialCoefficientL1 (polyMul boundary cross) ≤
        abstractPacketSourceTargetMertensScale packet := by
    refine Q'.le_trans' _ _ _
      (polynomialCoefficientL1_mul_le boundary cross) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (positivePolynomialTaylorPartial_l1_uniform
        sourceTargetKineticCrossPolynomial terms)
      (abstractPacketBoundaryL1_nonnegative packet)
  have hfirstRaw := positivePolynomialRectangleHaar_close_sumPartial
    (polyMul boundary cross)
    sourceDiagonalComplementPolynomial
    targetDiagonalComplementPolynomial
    (abstractPacketSourceTargetMertensScale packet)
    (HalfPow.half * epsilon)
    (abstractPacketSourceTargetMertensScale_nonnegative packet)
    hinsertionFirst hhalf terms hfirstCut
  change
    quaternionHaar 10
        (polyMul (polyMul boundary cross) (polyMul source target)) ≤
          quaternionHaar 10
              (polyMul (polyMul boundary cross) sourceTarget) +
            HalfPow.half * epsilon ∧
      quaternionHaar 10
              (polyMul (polyMul boundary cross) sourceTarget) ≤
        quaternionHaar 10
            (polyMul (polyMul boundary cross) (polyMul source target)) +
          HalfPow.half * epsilon at hfirstRaw
  have hfirst := close_congr_local
    (tenHaarCarrierEqv_to_haar
      (abstractPacketSourceTarget_reorder packet terms))
    (Q'.eqv_symm
      (tenHaarCarrierEqv_to_haar
        (abstractPacketCollapsedSourceTarget_reorder packet terms)))
    hfirstRaw
  change
    abstractPacketRectangularHaar terms terms terms packet ≤
        middle + HalfPow.half * epsilon ∧
      middle ≤
        abstractPacketRectangularHaar terms terms terms packet +
          HalfPow.half * epsilon at hfirst
  have hsecondRaw := positivePolynomialRectangleHaar_close_sumPartial
    boundary
    (polyAdd sourceDiagonalComplementPolynomial
      targetDiagonalComplementPolynomial)
    sourceTargetKineticCrossPolynomial
    (abstractPacketBoundaryL1 packet)
    (HalfPow.half * epsilon)
    (abstractPacketBoundaryL1_nonnegative packet)
    (Q'.le_refl' _)
    hhalf terms hsecondCut
  change
    middle ≤
        quaternionHaar 10
            (polyMul boundary
              (positivePolynomialTaylorPartial
                (polyAdd
                  (polyAdd sourceDiagonalComplementPolynomial
                    targetDiagonalComplementPolynomial)
                  sourceTargetKineticCrossPolynomial) terms)) +
          HalfPow.half * epsilon ∧
      quaternionHaar 10
            (polyMul boundary
              (positivePolynomialTaylorPartial
                (polyAdd
                  (polyAdd sourceDiagonalComplementPolynomial
                    targetDiagonalComplementPolynomial)
                  sourceTargetKineticCrossPolynomial) terms)) ≤
        middle + HalfPow.half * epsilon at hsecondRaw
  rw [groupedPositiveComponent_assoc_exact] at hsecondRaw
  change middle ≤ grouped + HalfPow.half * epsilon ∧
    grouped ≤ middle + HalfPow.half * epsilon at hsecondRaw
  exact
    ⟨two_halves_trans_mertens
      (abstractPacketRectangularHaar terms terms terms packet)
      middle grouped epsilon hfirst.1 hsecondRaw.1,
     two_halves_trans_mertens
      grouped middle
      (abstractPacketRectangularHaar terms terms terms packet)
      epsilon hsecondRaw.2 hfirst.2⟩

/-! ## 11. Located single-action packet endpoint -/

/-- Cauchy theorem for one positive polynomial Taylor factor under a fixed
Haar insertion. -/
theorem positivePolynomialHaarPartial_cauchy
    (insertion polynomial : RatPoly)
    (scale epsilon : Q')
    (hscale : (0 : Q') ≤ scale)
    (hinsertion : polynomialCoefficientL1 insertion ≤ scale)
    (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst :
      positivePolynomialScaledTaylorModulus
        polynomial scale epsilon ≤ first)
    (hsecond :
      positivePolynomialScaledTaylorModulus
        polynomial scale epsilon ≤ second) :
    quaternionHaar 10
        (polyMul insertion
          (positivePolynomialTaylorPartial polynomial first)) ≤
          quaternionHaar 10
              (polyMul insertion
                (positivePolynomialTaylorPartial polynomial second)) +
            epsilon ∧
      quaternionHaar 10
        (polyMul insertion
          (positivePolynomialTaylorPartial polynomial second)) ≤
          quaternionHaar 10
              (polyMul insertion
                (positivePolynomialTaylorPartial polynomial first)) +
            epsilon := by
  have hordered : ∀ earlier later : Nat,
      positivePolynomialScaledTaylorModulus
          polynomial scale epsilon ≤ earlier →
      earlier ≤ later →
      quaternionHaar 10
          (polyMul insertion
            (positivePolynomialTaylorPartial polynomial earlier)) ≤
            quaternionHaar 10
                (polyMul insertion
                  (positivePolynomialTaylorPartial polynomial later)) +
              epsilon ∧
        quaternionHaar 10
          (polyMul insertion
            (positivePolynomialTaylorPartial polynomial later)) ≤
            quaternionHaar 10
                (polyMul insertion
                  (positivePolynomialTaylorPartial polynomial earlier)) +
              epsilon := by
    intro earlier later hearlier horder
    obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le horder
    let increment := quaternionHaar 10
      (polyMul insertion
        (positivePolynomialTaylorBlock polynomial earlier distance))
    have hdecompose :
        quaternionHaar 10
            (polyMul insertion
              (positivePolynomialTaylorPartial
                polynomial (earlier + distance))) ≈
          quaternionHaar 10
              (polyMul insertion
                (positivePolynomialTaylorPartial polynomial earlier)) +
            increment := by
      rw [positivePolynomialTaylorPartial_add_block]
      exact quaternionHaar_polyMul_add_right 10 insertion _ _
    have hblock0 :
        (0 : Q') ≤ polynomialCoefficientL1
          (positivePolynomialTaylorBlock
            polynomial earlier distance) :=
      polynomialCoefficientL1_nonnegative _
    have hincrement : Q'.abs increment ≤ epsilon := by
      refine Q'.le_trans' _ _ _
        (quaternionHaar_abs_le_coefficientL1 10
          (polyMul insertion
            (positivePolynomialTaylorBlock
              polynomial earlier distance))) ?_
      refine Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le insertion
          (positivePolynomialTaylorBlock
            polynomial earlier distance)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          hinsertion hblock0) ?_
      exact positivePolynomialTaylorBlock_scaled_le
        polynomial scale epsilon hscale hepsilon
        earlier distance hearlier
    have hclose := add_increment_close_local
      (quaternionHaar 10
        (polyMul insertion
          (positivePolynomialTaylorPartial polynomial earlier)))
      (quaternionHaar 10
        (polyMul insertion
          (positivePolynomialTaylorPartial
            polynomial (earlier + distance))))
      increment epsilon hdecompose hincrement
    exact ⟨hclose.2, hclose.1⟩
  rcases Nat.le_total first second with horder | horder
  · exact hordered first second hfirst horder
  · have h := hordered second first hsecond horder
    exact ⟨h.2, h.1⟩

/-- The single grouped-positive-action Taylor contraction for the raw packet
boundary. -/
def abstractPacketGroupedComponentPartial
    (packet : BF4HolonomyStatePacket) (terms : Nat) : Q' :=
  quaternionHaar 10
    (polyMul
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (positivePolynomialTaylorPartial
        groupedPositiveComponentPolynomial terms))

/-- Located endpoint of `H(B_packet exp(G_component))`. -/
def abstractPacketGroupedComponentLimit
    (packet : BF4HolonomyStatePacket) : CReal where
  approx := abstractPacketGroupedComponentPartial packet
  cauchy := by
    intro epsilon hepsilon
    refine
      ⟨positivePolynomialScaledTaylorModulus
          groupedPositiveComponentPolynomial
          (abstractPacketBoundaryL1 packet) epsilon,
       fun first second hfirst hsecond => ?_⟩
    exact positivePolynomialHaarPartial_cauchy
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      groupedPositiveComponentPolynomial
      (abstractPacketBoundaryL1 packet) epsilon
      (abstractPacketBoundaryL1_nonnegative packet)
      (Q'.le_refl' _)
      hepsilon first second hfirst hsecond

@[simp] theorem abstractPacketGroupedComponentLimit_approx
    (packet : BF4HolonomyStatePacket) (terms : Nat) :
    (abstractPacketGroupedComponentLimit packet).approx terms =
      abstractPacketGroupedComponentPartial packet terms := rfl

/-- Equal source/target/cross cutoff schedule. -/
def bf4EqualThreeFactorSchedule : BF4ThreeFactorCofinalSchedule where
  sourceOrder := fun stage => stage
  targetOrder := fun stage => stage
  crossOrder := fun stage => stage
  source_cofinal := fun stage => Nat.le_refl stage
  target_cofinal := fun stage => Nat.le_refl stage
  cross_cofinal := fun stage => Nat.le_refl stage

/-- The equal-cutoff rectangular limit is the located single grouped-action
packet endpoint. -/
theorem abstractPacketEqualRectangle_equiv_groupedComponent
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketRectangularScheduledLimit
        bf4EqualThreeFactorSchedule packet)
      (abstractPacketGroupedComponentLimit packet) := by
  intro epsilon hepsilon
  refine
    ⟨abstractPacketThreeFactorMertensModulus packet epsilon,
     fun terms hterms => ?_⟩
  change
    abstractPacketRectangularHaar terms terms terms packet ≤
        abstractPacketGroupedComponentPartial packet terms + epsilon ∧
      abstractPacketGroupedComponentPartial packet terms ≤
        abstractPacketRectangularHaar terms terms terms packet + epsilon
  exact abstractPacketThreeFactorHaar_close_groupedPartial
    packet epsilon hepsilon terms hterms

/-- **The canonical three-factor rectangle has the single grouped-component
exponential endpoint.** -/
theorem abstractPacketRectangularLimit_equiv_groupedComponent
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketRectangularLimit packet)
      (abstractPacketGroupedComponentLimit packet) :=
  CReal.Equiv.trans
    (CReal.Equiv.symm
      (abstractPacketRectangularScheduledLimit_equiv_diagonal
        bf4EqualThreeFactorSchedule packet))
    (abstractPacketEqualRectangle_equiv_groupedComponent packet)

/-! ## 12. Canonical boundary units and finite packet polarization -/

/-- The order-one positive Taylor partial is the carrier unit. -/
theorem positivePolynomialTaylorPartial_one_eqv_one
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (positivePolynomialTaylorPartial polynomial 1) polyOne := by
  change TenHaarCarrierEqv
    (polyAdd polyZero
      (positivePolynomialTaylorTerm polynomial 0)) polyOne
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_add_zero_left
      (positivePolynomialTaylorTerm polynomial 0)) ?_
  exact positivePolynomialTaylorTerm_zero_eqv_one polynomial

/-- The CP-preserving source diagonal at order one is the carrier unit. -/
theorem sourceDiagonalFeynmanKacPartial_one_eqv_one :
    TenHaarCarrierEqv
      (sourceDiagonalFeynmanKacPartial 1) polyOne :=
  TenHaarCarrierEqv.trans
    (sourceDiagonalFeynmanKacPartial_eqv_ordinary 1)
    (positivePolynomialTaylorPartial_one_eqv_one
      sourceDiagonalComplementPolynomial)

/-- The compiled target diagonal at order one is the carrier unit. -/
theorem targetDiagonalFeynmanKacPartial_one_eqv_one :
    TenHaarCarrierEqv
      (targetDiagonalFeynmanKacPartial 1) polyOne :=
  positivePolynomialTaylorPartial_one_eqv_one
    targetDiagonalComplementPolynomial

/-- The literal source boundary used in polarization is the raw all-spin
packet boundary in the arbitrary-insertion ten-Haar quotient. -/
theorem bf4PacketBoundarySource_eqv_raw
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (bf4PacketBoundarySourcePolynomial packet)
      (bf4PacketRawBoundaryPolynomial packet) := by
  unfold bf4PacketBoundarySourcePolynomial
  refine TenHaarCarrierEqv.trans
    (bf4PacketHalfPolynomial_eqv_boundaryInsertion
      1 [] packet) ?_
  change TenHaarCarrierEqv
    (polyMul (bf4PacketRawBoundaryPolynomial packet)
      (polyMul (sourceDiagonalFeynmanKacPartial 1) polyOne))
    (bf4PacketRawBoundaryPolynomial packet)
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_congr
      (TenHaarCarrierEqv.refl
        (bf4PacketRawBoundaryPolynomial packet))
      (TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_congr
          sourceDiagonalFeynmanKacPartial_one_eqv_one
          (TenHaarCarrierEqv.refl polyOne))
        (tenHaarCarrierEqv_mul_one polyOne))) ?_
  exact tenHaarCarrierEqv_mul_one
    (bf4PacketRawBoundaryPolynomial packet)

/-- The literal reflected target boundary is the raw reflected all-spin
packet boundary in the same quotient. -/
theorem bf4PacketBoundaryTarget_eqv_raw
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (bf4PacketBoundaryTargetPolynomial packet)
      (bf4PacketRawTargetBoundaryPolynomial packet) := by
  unfold bf4PacketBoundaryTargetPolynomial
    bf4PacketBoundarySourcePolynomial
  refine TenHaarCarrierEqv.trans
    (shiftedBF4PacketHalfPolynomial_eqv_targetBoundaryInsertion
      1 [] packet) ?_
  change TenHaarCarrierEqv
    (polyMul (bf4PacketRawTargetBoundaryPolynomial packet)
      (polyMul (targetDiagonalFeynmanKacPartial 1) polyOne))
    (bf4PacketRawTargetBoundaryPolynomial packet)
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_congr
      (TenHaarCarrierEqv.refl
        (bf4PacketRawTargetBoundaryPolynomial packet))
      (TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_congr
          targetDiagonalFeynmanKacPartial_one_eqv_one
          (TenHaarCarrierEqv.refl polyOne))
        (tenHaarCarrierEqv_mul_one polyOne))) ?_
  exact tenHaarCarrierEqv_mul_one
    (bf4PacketRawTargetBoundaryPolynomial packet)

/-- The raw reflected packet boundary is exactly the product of the
canonical source and target boundaries in the full carrier quotient. -/
theorem bf4PacketRawReflectedBoundary_eqv_canonical
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (polyMul
        (bf4PacketBoundarySourcePolynomial packet)
        (bf4PacketBoundaryTargetPolynomial packet)) := by
  unfold bf4PacketRawReflectedBoundaryPolynomial
  exact TenHaarCarrierEqv.mul_congr
    (TenHaarCarrierEqv.symm
      (bf4PacketBoundarySource_eqv_raw packet))
    (TenHaarCarrierEqv.symm
      (bf4PacketBoundaryTarget_eqv_raw packet))

/-- **Finite BF4 packet polarization on every grouped kernel.**  The exact
quarter difference of the canonical source/target quadratic Haar forms is
the raw reflected packet insertion. -/
theorem bf4PacketHaar_polarization_raw
    (packet : BF4HolonomyStatePacket)
    (kernel : RatPoly) :
    Q'.mkPos 1 4 (by decide) *
        (quaternionHaar 10
            (polyMul
              (polyMul
                (bf4PacketBoundarySumPolynomial packet)
                (bf4PacketBoundarySumPolynomial packet))
              kernel) +
          -(quaternionHaar 10
            (polyMul
              (polyMul
                (bf4PacketBoundaryDifferencePolynomial packet)
                (bf4PacketBoundaryDifferencePolynomial packet))
              kernel))) ≈
      quaternionHaar 10
        (polyMul
          (bf4PacketRawReflectedBoundaryPolynomial packet)
          kernel) := by
  have hpolar := weightedHaar_polarization
    (bf4PacketBoundarySourcePolynomial packet)
    (bf4PacketBoundaryTargetPolynomial packet) kernel
  change
    Q'.mkPos 1 4 (by decide) *
        (quaternionHaar 10
            (polyMul
              (polyMul
                (bf4PacketBoundarySumPolynomial packet)
                (bf4PacketBoundarySumPolynomial packet))
              kernel) +
          -(quaternionHaar 10
            (polyMul
              (polyMul
                (bf4PacketBoundaryDifferencePolynomial packet)
                (bf4PacketBoundaryDifferencePolynomial packet))
              kernel))) ≈
      quaternionHaar 10
        (polyMul
          (polyMul
            (bf4PacketBoundarySourcePolynomial packet)
            (bf4PacketBoundaryTargetPolynomial packet))
          kernel) at hpolar
  refine Q'.eqv_trans _ _ _ hpolar ?_
  exact Q'.eqv_symm
    (tenHaarCarrierEqv_to_haar
      (TenHaarCarrierEqv.mul_congr
        (bf4PacketRawReflectedBoundary_eqv_canonical packet)
        (TenHaarCarrierEqv.refl kernel)))

/-! ## 13. Located grouped-component quadratic and packet polarization -/

/-- Finite quadratic coefficient for the single grouped positive action. -/
def abstractGroupedComponentQuadraticPartial
    (polynomial : RatPoly) (terms : Nat) : Q' :=
  quaternionHaar 10
    (polyMul
      (polyMul polynomial polynomial)
      (positivePolynomialTaylorPartial
        groupedPositiveComponentPolynomial terms))

/-- Located quadratic endpoint `H(P² exp(G_component))`. -/
def abstractGroupedComponentQuadraticLimit
    (polynomial : RatPoly) : CReal where
  approx := abstractGroupedComponentQuadraticPartial polynomial
  cauchy := by
    intro epsilon hepsilon
    let insertion := polyMul polynomial polynomial
    let scale := polynomialCoefficientL1 insertion
    refine
      ⟨positivePolynomialScaledTaylorModulus
          groupedPositiveComponentPolynomial scale epsilon,
       fun first second hfirst hsecond => ?_⟩
    exact positivePolynomialHaarPartial_cauchy
      insertion groupedPositiveComponentPolynomial
      scale epsilon
      (polynomialCoefficientL1_nonnegative insertion)
      (Q'.le_refl' scale) hepsilon
      first second hfirst hsecond

@[simp] theorem abstractGroupedComponentQuadraticLimit_approx
    (polynomial : RatPoly) (terms : Nat) :
    (abstractGroupedComponentQuadraticLimit polynomial).approx terms =
      abstractGroupedComponentQuadraticPartial polynomial terms := rfl

/-- The polarized located quadratic endpoint is the raw reflected packet
endpoint.  This is pointwise in the Taylor cutoff, hence requires no second
limit interchange. -/
theorem abstractGroupedComponentPacketPolarization_equiv_raw
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (CReal.mul
        (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
        (CReal.add
          (abstractGroupedComponentQuadraticLimit
            (bf4PacketBoundarySumPolynomial packet))
          (CReal.neg
            (abstractGroupedComponentQuadraticLimit
              (bf4PacketBoundaryDifferencePolynomial packet)))))
      (abstractPacketGroupedComponentLimit packet) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun terms => ?_)
  exact bf4PacketHaar_polarization_raw packet
    (positivePolynomialTaylorPartial
      groupedPositiveComponentPolynomial terms)

/-! ## 14. Carrier transport to the compact complement plus scalar shift -/

/-- The componentwise grouped action and its compiled expression are one
element of the arbitrary-insertion Haar quotient. -/
theorem groupedPositiveComponent_eqv_compiled :
    TenHaarCarrierEqv
      groupedPositiveComponentPolynomial
      groupedPositiveComplementPolynomial := by
  intro insertion
  exact groupedPositiveComponent_haar_eq_compiled insertion

/-- Polynomial representative of the scalar action shift. -/
def groupedToCompactShiftPolynomial : RatPoly :=
  polySmul groupedToCompactComplementShift polyOne

/-- The compiled grouped exponent is exactly `D + shift·1` in the complete
Haar carrier quotient. -/
theorem groupedPositiveComplement_eqv_compact_add_shift :
    TenHaarCarrierEqv
      groupedPositiveComplementPolynomial
      (polyAdd compactActionComplementPolynomial
        groupedToCompactShiftPolynomial) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
        (polyMul insertion compactActionComplementPolynomial) +
      groupedToCompactComplementShift *
        quaternionHaar 10 insertion) _
    (groupedPositiveComplement_haar_eq_compact_add_shift insertion) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right 10 insertion
      compactActionComplementPolynomial
      groupedToCompactShiftPolynomial) ?_)
  exact Q'.add_eqv_congr_left
    (quaternionHaar 10
      (polyMul insertion compactActionComplementPolynomial)) _ _
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right
        10 groupedToCompactComplementShift insertion polyOne)
      (Q'.mul_eqv_congr_left
        groupedToCompactComplementShift _ _
        (quaternionHaar_polyMul_one_right 10 insertion)))

/-- The original component exponent is the compact complement plus its
positive scalar shift. -/
theorem groupedPositiveComponent_eqv_compact_add_shift :
    TenHaarCarrierEqv
      groupedPositiveComponentPolynomial
      (polyAdd compactActionComplementPolynomial
        groupedToCompactShiftPolynomial) :=
  TenHaarCarrierEqv.trans
    groupedPositiveComponent_eqv_compiled
    groupedPositiveComplement_eqv_compact_add_shift

/-- Carrier equality propagates through every positive Taylor coefficient. -/
theorem positivePolynomialTaylorTerm_congr
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right)
    (exponent : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialTaylorTerm left exponent)
      (positivePolynomialTaylorTerm right exponent) := by
  unfold positivePolynomialTaylorTerm
  exact TenHaarCarrierEqv.smul
    (ExpNeg.termAbs 1 exponent)
    (TenHaarCarrierEqv.power h exponent)

/-- Carrier equality propagates through every positive Taylor partial. -/
theorem positivePolynomialTaylorPartial_congr
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    ∀ terms : Nat,
      TenHaarCarrierEqv
        (positivePolynomialTaylorPartial left terms)
        (positivePolynomialTaylorPartial right terms)
  | 0 => TenHaarCarrierEqv.refl polyZero
  | terms + 1 =>
      TenHaarCarrierEqv.add_congr
        (positivePolynomialTaylorPartial_congr h terms)
        (positivePolynomialTaylorTerm_congr h terms)

/-- Every grouped-component Taylor partial is the matching Taylor partial
of the compact complement plus scalar shift. -/
theorem groupedPositiveComponentPartial_eqv_compact_add_shift
    (terms : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialTaylorPartial
        groupedPositiveComponentPolynomial terms)
      (positivePolynomialTaylorPartial
        (polyAdd compactActionComplementPolynomial
          groupedToCompactShiftPolynomial) terms) :=
  positivePolynomialTaylorPartial_congr
    groupedPositiveComponent_eqv_compact_add_shift terms

/-! ## 15. Exact scalar-shift and compact-complement partials -/

/-- Product of two scalar carrier units. -/
theorem tenHaarCarrierEqv_smul_units_mul
    (leftScale rightScale : Q') :
    TenHaarCarrierEqv
      (polyMul
        (polySmul leftScale polyOne)
        (polySmul rightScale polyOne))
      (polySmul (leftScale * rightScale) polyOne) := by
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_polyMul_smul_left
      leftScale polyOne
      (polySmul rightScale polyOne)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.smul leftScale
      (TenHaarCarrierEqv.trans
        (tenHaarCarrierEqv_mul_comm
          polyOne (polySmul rightScale polyOne))
        (tenHaarCarrierEqv_mul_one
          (polySmul rightScale polyOne)))) ?_
  exact tenHaarCarrierEqv_smul_assoc
    leftScale rightScale polyOne

/-- Every power of the scalar shift polynomial is the corresponding scalar
power times the carrier unit. -/
theorem groupedToCompactShiftPolynomial_power_eqv :
    ∀ exponent : Nat,
      TenHaarCarrierEqv
        (polynomialPower groupedToCompactShiftPolynomial exponent)
        (polySmul
          (qpow groupedToCompactComplementShift exponent)
          polyOne)
  | 0 => by
      change TenHaarCarrierEqv polyOne (polySmul 1 polyOne)
      exact TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_smul_one polyOne)
  | exponent + 1 => by
      change TenHaarCarrierEqv
        (polyMul
          (polynomialPower groupedToCompactShiftPolynomial exponent)
          groupedToCompactShiftPolynomial)
        (polySmul
          (qpow groupedToCompactComplementShift exponent *
            groupedToCompactComplementShift)
          polyOne)
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_congr
          (groupedToCompactShiftPolynomial_power_eqv exponent)
          (TenHaarCarrierEqv.refl
            groupedToCompactShiftPolynomial)) ?_
      unfold groupedToCompactShiftPolynomial
      exact tenHaarCarrierEqv_smul_units_mul
        (qpow groupedToCompactComplementShift exponent)
        groupedToCompactComplementShift

/-- Every scalar-shift Taylor coefficient is the ordinary scalar exponential
coefficient times the carrier unit. -/
theorem groupedToCompactShiftTaylorTerm_eqv
    (exponent : Nat) :
    TenHaarCarrierEqv
      (positivePolynomialTaylorTerm
        groupedToCompactShiftPolynomial exponent)
      (polySmul
        (ExpNeg.termAbs groupedToCompactComplementShift exponent)
        polyOne) := by
  unfold positivePolynomialTaylorTerm
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.smul
      (ExpNeg.termAbs 1 exponent)
      (groupedToCompactShiftPolynomial_power_eqv exponent)) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_smul_assoc
      (ExpNeg.termAbs 1 exponent)
      (qpow groupedToCompactComplementShift exponent)
      polyOne) ?_
  apply tenHaarCarrierEqv_smul_coefficient
  refine Q'.eqv_trans _
    (qpow groupedToCompactComplementShift exponent *
      ExpNeg.termAbs 1 exponent) _
    (Q'.mul_comm_eqv
      (ExpNeg.termAbs 1 exponent)
      (qpow groupedToCompactComplementShift exponent)) ?_
  exact Q'.eqv_symm
    (termAbs_eq_qpow_mul_unit
      groupedToCompactComplementShift exponent)

/-- A scalar-shift positive Taylor partial is the scalar positive exponential
partial times the carrier unit. -/
theorem groupedToCompactShiftTaylorPartial_eqv :
    ∀ terms : Nat,
      TenHaarCarrierEqv
        (positivePolynomialTaylorPartial
          groupedToCompactShiftPolynomial terms)
        (polySmul
          (ExpNeg.partialSumAbs
            groupedToCompactComplementShift terms)
          polyOne)
  | 0 => by
      change TenHaarCarrierEqv polyZero (polySmul 0 polyOne)
      exact TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_smul_zero polyOne)
  | terms + 1 => by
      change TenHaarCarrierEqv
        (polyAdd
          (positivePolynomialTaylorPartial
            groupedToCompactShiftPolynomial terms)
          (positivePolynomialTaylorTerm
            groupedToCompactShiftPolynomial terms))
        (polySmul
          (ExpNeg.partialSumAbs
              groupedToCompactComplementShift terms +
            ExpNeg.termAbs
              groupedToCompactComplementShift terms)
          polyOne)
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.add_congr
          (groupedToCompactShiftTaylorPartial_eqv terms)
          (groupedToCompactShiftTaylorTerm_eqv terms)) ?_
      exact TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_smul_add
          (ExpNeg.partialSumAbs
            groupedToCompactComplementShift terms)
          (ExpNeg.termAbs
            groupedToCompactComplementShift terms)
          polyOne)

/-- Haar contraction of the scalar-shift Taylor partial. -/
theorem groupedToCompactShiftTaylorPartial_haar
    (insertion : RatPoly) (terms : Nat) :
    quaternionHaar 10
        (polyMul insertion
          (positivePolynomialTaylorPartial
            groupedToCompactShiftPolynomial terms)) ≈
      ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
        quaternionHaar 10 insertion := by
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul insertion
        (polySmul
          (ExpNeg.partialSumAbs
            groupedToCompactComplementShift terms)
          polyOne))) _
    ((groupedToCompactShiftTaylorPartial_eqv terms) insertion) ?_
  refine Q'.eqv_trans _
    (ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
      quaternionHaar 10 (polyMul insertion polyOne)) _
    (quaternionHaar_polyMul_smul_right 10
      (ExpNeg.partialSumAbs groupedToCompactComplementShift terms)
      insertion polyOne) ?_
  exact Q'.mul_eqv_congr_left
    (ExpNeg.partialSumAbs groupedToCompactComplementShift terms) _ _
    (quaternionHaar_polyMul_one_right 10 insertion)

/-- One compact-complement polynomial Taylor term is the already constructed
positive compact-action quadratic term. -/
theorem compactComplementPositiveTerm_haar_eq_quadratic
    (polynomial : RatPoly) (exponent : Nat) :
    quaternionHaar 10
        (polyMul (polyMul polynomial polynomial)
          (positivePolynomialTaylorTerm
            compactActionComplementPolynomial exponent)) ≈
      compactActionShiftedTaylorQuadraticTerm
        polynomial exponent := by
  unfold positivePolynomialTaylorTerm
  refine Q'.eqv_trans _
    (compactComplementTaylorHaarTerm
      (polyMul polynomial polynomial) exponent) _ ?_ ?_
  · exact quaternionHaar_polyMul_smul_right 10
      (ExpNeg.termAbs 1 exponent)
      (polyMul polynomial polynomial)
      (polynomialPower
        compactActionComplementPolynomial exponent)
  · exact Q'.eqv_symm
      (compactActionShiftedTaylorQuadraticTerm_eq_complement
        polynomial exponent)

/-- The complete compact-complement polynomial Taylor partial contracts to
the canonical located positive compact-action quadratic partial. -/
theorem compactComplementPositivePartial_haar_eq_quadratic
    (polynomial : RatPoly) :
    ∀ terms : Nat,
      quaternionHaar 10
          (polyMul (polyMul polynomial polynomial)
            (positivePolynomialTaylorPartial
              compactActionComplementPolynomial terms)) ≈
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms
  | 0 => by
      change quaternionHaar 10
        (polyMul (polyMul polynomial polynomial) polyZero) ≈ 0
      rw [polyMul_zero_right_local]
      exact Q'.eqv_refl 0
  | terms + 1 => by
      change quaternionHaar 10
          (polyMul (polyMul polynomial polynomial)
            (polyAdd
              (positivePolynomialTaylorPartial
                compactActionComplementPolynomial terms)
              (positivePolynomialTaylorTerm
                compactActionComplementPolynomial terms))) ≈
        compactActionShiftedTaylorQuadraticPartial polynomial terms +
          compactActionShiftedTaylorQuadraticTerm polynomial terms
      refine Q'.eqv_trans _
        (quaternionHaar 10
            (polyMul (polyMul polynomial polynomial)
              (positivePolynomialTaylorPartial
                compactActionComplementPolynomial terms)) +
          quaternionHaar 10
            (polyMul (polyMul polynomial polynomial)
              (positivePolynomialTaylorTerm
                compactActionComplementPolynomial terms))) _
        (quaternionHaar_polyMul_add_right 10
          (polyMul polynomial polynomial)
          (positivePolynomialTaylorPartial
            compactActionComplementPolynomial terms)
          (positivePolynomialTaylorTerm
            compactActionComplementPolynomial terms)) ?_
      exact Q'.add_eqv_congr'
        (compactComplementPositivePartial_haar_eq_quadratic
          polynomial terms)
        (compactComplementPositiveTerm_haar_eq_quadratic
          polynomial terms)

/-- Exact pointwise identification of the two-factor rectangle with the
product of the scalar exponential partial and compact quadratic partial. -/
theorem compactShiftRectangleHaar_eq_productPartial
    (polynomial : RatPoly) (terms : Nat) :
    quaternionHaar 10
        (polyMul (polyMul polynomial polynomial)
          (polyMul
            (positivePolynomialTaylorPartial
              compactActionComplementPolynomial terms)
            (positivePolynomialTaylorPartial
              groupedToCompactShiftPolynomial terms))) ≈
      ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms := by
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul
        (polyMul (polyMul polynomial polynomial)
          (positivePolynomialTaylorPartial
            compactActionComplementPolynomial terms))
        (positivePolynomialTaylorPartial
          groupedToCompactShiftPolynomial terms))) _
    (tenHaarCarrierEqv_to_haar
      (TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_mul_assoc
          (polyMul polynomial polynomial)
          (positivePolynomialTaylorPartial
            compactActionComplementPolynomial terms)
          (positivePolynomialTaylorPartial
            groupedToCompactShiftPolynomial terms)))) ?_
  refine Q'.eqv_trans _
    (ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
      quaternionHaar 10
        (polyMul (polyMul polynomial polynomial)
          (positivePolynomialTaylorPartial
            compactActionComplementPolynomial terms))) _
    (groupedToCompactShiftTaylorPartial_haar
      (polyMul (polyMul polynomial polynomial)
        (positivePolynomialTaylorPartial
          compactActionComplementPolynomial terms)) terms) ?_
  exact Q'.mul_eqv_congr_left
    (ExpNeg.partialSumAbs groupedToCompactComplementShift terms) _ _
    (compactComplementPositivePartial_haar_eq_quadratic
      polynomial terms)

/-! ## 16. Mertens transport to the abstract grouped positive endpoint -/

/-- **Grouped component/action-shift bridge.**  For every supported boundary
polynomial, the located exponential of the literal componentwise grouped
action is the already constructed abstract product
`exp(shift) · H(P² exp(D))`.  The cutoff is the explicit coefficient-L1
Mertens modulus; no diagonal-limit interchange is assumed. -/
theorem abstractGroupedComponentQuadratic_equiv_abstractGroupedPositive
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 10 polynomial) :
    CReal.Equiv
      (abstractGroupedComponentQuadraticLimit polynomial)
      (abstractGroupedPositiveQuadraticLimit polynomial hsupport) := by
  intro epsilon hepsilon
  let insertion := polyMul polynomial polynomial
  let scale := polynomialCoefficientL1 insertion
  refine
    ⟨positivePolynomialScaledMertensModulus
        compactActionComplementPolynomial
        groupedToCompactShiftPolynomial scale epsilon,
     fun terms hterms => ?_⟩
  have hmertens := positivePolynomialRectangleHaar_close_sumPartial
    insertion compactActionComplementPolynomial
    groupedToCompactShiftPolynomial scale epsilon
    (polynomialCoefficientL1_nonnegative insertion)
    (Q'.le_refl' scale) hepsilon terms hterms
  have hcomponent :=
    (groupedPositiveComponentPartial_eqv_compact_add_shift terms)
      insertion
  have hproduct := compactShiftRectangleHaar_eq_productPartial
    polynomial terms
  change
    abstractGroupedComponentQuadraticPartial polynomial terms ≤
        (ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
          compactActionShiftedTaylorQuadraticPartial polynomial terms) +
          epsilon ∧
      ExpNeg.partialSumAbs groupedToCompactComplementShift terms *
          compactActionShiftedTaylorQuadraticPartial polynomial terms ≤
        abstractGroupedComponentQuadraticPartial polynomial terms +
          epsilon
  exact close_congr_local
    hcomponent (Q'.eqv_symm hproduct)
    ⟨hmertens.2, hmertens.1⟩

/-! ## 17. Packet endpoint and physical normalization -/

/-- Polarization after action-shift transport is the raw grouped packet
endpoint. -/
theorem abstractGroupedPositivePacketPolarization_equiv_raw
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (CReal.mul
        (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
        (CReal.add
          (abstractGroupedPositiveQuadraticLimit
            (bf4PacketBoundarySumPolynomial packet)
            (bf4PacketBoundarySum_supported packet))
          (CReal.neg
            (abstractGroupedPositiveQuadraticLimit
              (bf4PacketBoundaryDifferencePolynomial packet)
              (bf4PacketBoundaryDifference_supported packet)))))
      (abstractPacketGroupedComponentLimit packet) := by
  let plusComponent := abstractGroupedComponentQuadraticLimit
    (bf4PacketBoundarySumPolynomial packet)
  let minusComponent := abstractGroupedComponentQuadraticLimit
    (bf4PacketBoundaryDifferencePolynomial packet)
  let plusGrouped := abstractGroupedPositiveQuadraticLimit
    (bf4PacketBoundarySumPolynomial packet)
    (bf4PacketBoundarySum_supported packet)
  let minusGrouped := abstractGroupedPositiveQuadraticLimit
    (bf4PacketBoundaryDifferencePolynomial packet)
    (bf4PacketBoundaryDifference_supported packet)
  have hplus : CReal.Equiv plusComponent plusGrouped :=
    abstractGroupedComponentQuadratic_equiv_abstractGroupedPositive
      (bf4PacketBoundarySumPolynomial packet)
      (bf4PacketBoundarySum_supported packet)
  have hminus : CReal.Equiv minusComponent minusGrouped :=
    abstractGroupedComponentQuadratic_equiv_abstractGroupedPositive
      (bf4PacketBoundaryDifferencePolynomial packet)
      (bf4PacketBoundaryDifference_supported packet)
  have hinside :
      CReal.Equiv
        (CReal.add plusComponent (CReal.neg minusComponent))
        (CReal.add plusGrouped (CReal.neg minusGrouped)) :=
    CReal.Equiv.trans
      (CReal.add_congr_left hplus)
      (CReal.add_congr_right
        (CReal.neg_congr hminus))
  have hpolarized :
      CReal.Equiv
        (CReal.mul
          (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
          (CReal.add plusComponent (CReal.neg minusComponent)))
        (CReal.mul
          (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
          (CReal.add plusGrouped (CReal.neg minusGrouped))) :=
    YMGap.Constructive.TrigSignedAdd.mul_congr_right hinside
  exact CReal.Equiv.trans
    (CReal.Equiv.symm hpolarized)
    (abstractGroupedComponentPacketPolarization_equiv_raw packet)

/-- The unnormalized three-factor rectangular net has the polarized abstract
grouped-positive endpoint. -/
theorem abstractPacketRectangularLimit_equiv_abstractGroupedPositivePacket
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketRectangularLimit packet)
      (CReal.mul
        (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
        (CReal.add
          (abstractGroupedPositiveQuadraticLimit
            (bf4PacketBoundarySumPolynomial packet)
            (bf4PacketBoundarySum_supported packet))
          (CReal.neg
            (abstractGroupedPositiveQuadraticLimit
              (bf4PacketBoundaryDifferencePolynomial packet)
              (bf4PacketBoundaryDifference_supported packet))))) :=
  CReal.Equiv.trans
    (abstractPacketRectangularLimit_equiv_groupedComponent packet)
    (CReal.Equiv.symm
      (abstractGroupedPositivePacketPolarization_equiv_raw packet))

/-- Multiplying a polarized endpoint by a common normalization distributes
the normalization into both quadratic branches. -/
theorem normalize_grouped_packet_polarization
    (normalization plus minus : CReal) :
    CReal.Equiv
      (CReal.mul normalization
        (CReal.mul
          (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
          (CReal.add plus (CReal.neg minus))))
      (CReal.mul
        (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
        (CReal.add
          (CReal.mul normalization plus)
          (CReal.neg
            (CReal.mul normalization minus)))) := by
  let quarter := CReal.ofQ' (Q'.mkPos 1 4 (by decide))
  let difference := CReal.sub plus minus
  change CReal.Equiv
    (CReal.mul normalization (CReal.mul quarter difference))
    (CReal.mul quarter
      (CReal.sub
        (CReal.mul normalization plus)
        (CReal.mul normalization minus)))
  refine CReal.Equiv.trans
    (CReal.Equiv.symm
      (CRealAlg.cmul_assoc normalization quarter difference)) ?_
  refine CReal.Equiv.trans
    (CReal.mul_congr_left
      (CRealAlg.cmul_comm normalization quarter)) ?_
  refine CReal.Equiv.trans
    (CRealAlg.cmul_assoc quarter normalization difference) ?_
  exact YMGap.Constructive.TrigSignedAdd.mul_congr_right
    (CReal.mul_sub normalization plus minus)

/-- **Three-factor cofinal/Mertens endpoint theorem.**  After restoring the
physical source/target normalization, the canonical rectangular net
converges to `abstractPhysicalNormalizedGroupedPacketLimit`. -/
theorem abstractPacketPhysicalNormalizedRectangularLimit_equiv_abstractPhysicalPacket
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketPhysicalNormalizedRectangularLimit packet)
      (abstractPhysicalNormalizedGroupedPacketLimit packet) := by
  let normalization := ExpNeg.expNeg groupedPhysicalNormalization
    groupedPhysicalNormalization_nonnegative
  let plusGrouped := abstractGroupedPositiveQuadraticLimit
    (bf4PacketBoundarySumPolynomial packet)
    (bf4PacketBoundarySum_supported packet)
  let minusGrouped := abstractGroupedPositiveQuadraticLimit
    (bf4PacketBoundaryDifferencePolynomial packet)
    (bf4PacketBoundaryDifference_supported packet)
  have hrectangle :
      CReal.Equiv
        (CReal.mul normalization
          (abstractPacketRectangularLimit packet))
        (CReal.mul normalization
          (CReal.mul
            (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
            (CReal.add plusGrouped (CReal.neg minusGrouped)))) :=
    YMGap.Constructive.TrigSignedAdd.mul_congr_right
      (abstractPacketRectangularLimit_equiv_abstractGroupedPositivePacket
        packet)
  unfold abstractPacketPhysicalNormalizedRectangularLimit
    abstractPhysicalNormalizedGroupedPacketLimit
    abstractPhysicalNormalizedGroupedQuadraticLimit
  exact CReal.Equiv.trans hrectangle
    (normalize_grouped_packet_polarization
      normalization plusGrouped minusGrouped)

/-- The previously located normalized all-label grouped joint endpoint is
therefore the same physical abstract packet endpoint. -/
theorem bf4PacketPhysicalNormalizedGroupedLimit_equiv_abstractPhysicalPacket
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (bf4PacketPhysicalNormalizedGroupedLimit packet)
      (abstractPhysicalNormalizedGroupedPacketLimit packet) :=
  CReal.Equiv.trans
    (CReal.Equiv.symm
      (abstractPacketPhysicalNormalizedRectangularLimit_equiv_grouped
        packet))
    (abstractPacketPhysicalNormalizedRectangularLimit_equiv_abstractPhysicalPacket
      packet)

/-! ## 16. End-to-end compact reference identification -/

/-- The three independent cutoff removals, the two Mertens collapses, the
physical scalar normalization, and the compact negative-action
identification compose to one direct endpoint theorem.

The target is the compact coupled-action *reference* coefficient.  This
statement does not identify that reference with the finite Wilson/heat-kernel
corrected-slab Gibbs law; that scale-dependent comparison is a separate
frontier theorem. -/
theorem abstractPacketPhysicalNormalizedRectangularLimit_equiv_compactPhysical
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketPhysicalNormalizedRectangularLimit packet)
      (compactPhysicalPacketReflectedLimit packet) :=
  CReal.Equiv.trans
    (abstractPacketPhysicalNormalizedRectangularLimit_equiv_abstractPhysicalPacket
      packet)
    (abstractPhysicalNormalizedGroupedPacket_equiv_compactPhysical
      packet)

/-- **Direct all-label packet endpoint bridge.**  The located grouped
source/target packet quadratic is exactly the compact coupled-action packet
quadratic after all three cutoffs have been removed constructively.

Together with the geometric Peter--Weyl construction imported above, the
boundary polynomials in the target are the five-holonomy wavefunctions
obtained by exact integration of the eighteen non-transmitted chords.  The
remaining corrected-slab gate is therefore a physical/reference comparison,
not another Cauchy/Mertens rearrangement. -/
theorem bf4PacketPhysicalNormalizedGroupedLimit_equiv_compactPhysical
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (bf4PacketPhysicalNormalizedGroupedLimit packet)
      (compactPhysicalPacketReflectedLimit packet) :=
  CReal.Equiv.trans
    (bf4PacketPhysicalNormalizedGroupedLimit_equiv_abstractPhysicalPacket
      packet)
    (abstractPhysicalNormalizedGroupedPacket_equiv_compactPhysical
      packet)

/-! ## 17. Recovering a boundary-indexed kernel from packet quadratics -/

/-- Positive polarization packet for two all-spin boundary labels. -/
def bf4BoundaryPolarizationSumPacket
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    BF4HolonomyStatePacket :=
  [((1 : Q'), left), ((1 : Q'), right)]

/-- Signed polarization packet for two all-spin boundary labels. -/
def bf4BoundaryPolarizationDifferencePacket
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    BF4HolonomyStatePacket :=
  [((1 : Q'), left), ((-1 : Q'), right)]

/-- The source/target kernel recovered constructively from the located
all-label grouped packet quadratic.  This definition is division-free: the
factor `1/4` is an exact rational scalar in `CReal`. -/
def bf4AllLabelGroupedPacketKernel
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    CReal :=
  CReal.mul
    (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
    (CReal.add
      (bf4PacketPhysicalNormalizedGroupedLimit
        (bf4BoundaryPolarizationSumPacket left right))
      (CReal.neg
        (bf4PacketPhysicalNormalizedGroupedLimit
          (bf4BoundaryPolarizationDifferencePacket left right))))

/-- The same polarization performed after passing to the compact
coupled-action reference quadratic. -/
def compactPhysicalPolarizedPacketKernel
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    CReal :=
  CReal.mul
    (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
    (CReal.add
      (compactPhysicalPacketReflectedLimit
        (bf4BoundaryPolarizationSumPacket left right))
      (CReal.neg
        (compactPhysicalPacketReflectedLimit
          (bf4BoundaryPolarizationDifferencePacket left right))))

/-- **Kernel-level packet endpoint bridge.**  Constructive polarization
turns the scalar quadratic endpoint into a located source/target kernel, and
the end-to-end compact-reference equivalence survives that polarization.

This is the exact interface needed by a subsequent rowwise comparison: the
remaining object is now indexed by physical boundary labels rather than by
one arbitrary signed packet. -/
theorem bf4AllLabelGroupedPacketKernel_equiv_compactPhysical
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    CReal.Equiv
      (bf4AllLabelGroupedPacketKernel left right)
      (compactPhysicalPolarizedPacketKernel left right) := by
  have hplus :
      CReal.Equiv
        (bf4PacketPhysicalNormalizedGroupedLimit
          (bf4BoundaryPolarizationSumPacket left right))
        (compactPhysicalPacketReflectedLimit
          (bf4BoundaryPolarizationSumPacket left right)) :=
    bf4PacketPhysicalNormalizedGroupedLimit_equiv_compactPhysical
      (bf4BoundaryPolarizationSumPacket left right)
  have hminus :
      CReal.Equiv
        (bf4PacketPhysicalNormalizedGroupedLimit
          (bf4BoundaryPolarizationDifferencePacket left right))
        (compactPhysicalPacketReflectedLimit
          (bf4BoundaryPolarizationDifferencePacket left right)) :=
    bf4PacketPhysicalNormalizedGroupedLimit_equiv_compactPhysical
      (bf4BoundaryPolarizationDifferencePacket left right)
  have hinside :
      CReal.Equiv
        (CReal.add
          (bf4PacketPhysicalNormalizedGroupedLimit
            (bf4BoundaryPolarizationSumPacket left right))
          (CReal.neg
            (bf4PacketPhysicalNormalizedGroupedLimit
              (bf4BoundaryPolarizationDifferencePacket left right))))
        (CReal.add
          (compactPhysicalPacketReflectedLimit
            (bf4BoundaryPolarizationSumPacket left right))
          (CReal.neg
            (compactPhysicalPacketReflectedLimit
              (bf4BoundaryPolarizationDifferencePacket left right)))) :=
    CReal.Equiv.trans
      (CReal.add_congr_left hplus)
      (CReal.add_congr_right
        (CReal.neg_congr hminus))
  unfold bf4AllLabelGroupedPacketKernel
    compactPhysicalPolarizedPacketKernel
  exact YMGap.Constructive.TrigSignedAdd.mul_congr_right hinside

end YMGap.Continuum.BF4PositivePolynomialCauchyMertens

#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.carrierPolyFinSum_congr
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.tenHaarCarrierEqv_smul_cancel_of_pos
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.positivePolynomialTaylorTerm_weighted
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.bf4PacketHaar_polarization_raw
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.abstractGroupedComponentPacketPolarization_equiv_raw
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.abstractGroupedComponentQuadratic_equiv_abstractGroupedPositive
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.abstractPacketPhysicalNormalizedRectangularLimit_equiv_abstractPhysicalPacket
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.bf4PacketPhysicalNormalizedGroupedLimit_equiv_abstractPhysicalPacket
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.abstractPacketPhysicalNormalizedRectangularLimit_equiv_compactPhysical
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.bf4PacketPhysicalNormalizedGroupedLimit_equiv_compactPhysical
#print axioms YMGap.Continuum.BF4PositivePolynomialCauchyMertens.bf4AllLabelGroupedPacketKernel_equiv_compactPhysical
