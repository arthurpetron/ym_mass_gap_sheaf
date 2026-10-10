/-
A computed rational half-budget for ACTUAL polynomial sphere repair.

The Lipschitz constant comes from the original finite polynomial syntax.
Choose tau=epsilon/(2*(1+L)) and delta=tau^2/48; the existing denominator
lemma gives a Nat stage with invSucc(n)<=delta. The actual weighted repair
cost then fits in epsilon/2. There is no inverse of L, square root, supplied
continuity estimate or continuous-Haar premise. Empty/constant polynomials
and arbitrarily small positive rational tolerances are included.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.RatPolyCubeLipschitz
open YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair

local infix:50 " ≈ " => Q'.eqv

/-- A positive computed ceiling; in particular L=0 is not divided out. -/
def repairCeiling (p : RatPoly) : Q' := 1 + polynomialLipschitz p

theorem repairCeiling_positive (p : RatPoly) : (0 : Q') < repairCeiling p :=
  Q'.pos_add_nonneg (by decide) (polynomialLipschitz_nonnegative p)

private theorem lipschitz_le_ceiling (p : RatPoly) :
    polynomialLipschitz p ≤ repairCeiling p :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 (by decide))
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

/-- Actual positive rational Young parameter, computed from p and epsilon. -/
def repairTau (p : RatPoly) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (2 * repairCeiling p)
    (Q'.mul_pos (by decide) (repairCeiling_positive p))

theorem repairTau_positive (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) : (0 : Q') < repairTau p epsilon :=
  Q'.divPos_pos _ _ _ he

private theorem divPos_mul (a b : Q') (hb : (0 : Q') < b) :
    Q'.divPos a b hb * b ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv b hb)))
      (Q'.mul_one_eqv a))

theorem repairTau_pin (p : RatPoly) (epsilon : Q') :
    repairTau p epsilon * (2 * repairCeiling p) ≈ epsilon :=
  divPos_mul _ _ _

/-- Sufficient inverse-degree tolerance, equivalent to epsilon^2/(192 B^2).
Its unreduced denominator is itself a usable constructive Nat stage. -/
def repairSpacingTolerance (p : RatPoly) (epsilon : Q') : Q' :=
  Q'.divPos (repairTau p epsilon * repairTau p epsilon) 48 (by decide)

theorem repairSpacingTolerance_positive (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) : (0 : Q') < repairSpacingTolerance p epsilon :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos (repairTau_positive p epsilon he)
    (repairTau_positive p epsilon he))

theorem repairSpacingTolerance_pin (p : RatPoly) (epsilon : Q') :
    repairSpacingTolerance p epsilon * 48 ≈
      repairTau p epsilon * repairTau p epsilon :=
  divPos_mul _ _ _

/-- The repair stage is DATA, not an existential or an opaque analytic bound. -/
def repairCutoff (p : RatPoly) (epsilon : Q') : Nat :=
  (repairSpacingTolerance p epsilon).den

theorem repairCutoff_inverse_bound (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat) (hn : repairCutoff p epsilon ≤ n) :
    Q'.invSucc n ≤ repairSpacingTolerance p epsilon :=
  Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
    (HalfPow.invSucc_den_le _ (repairSpacingTolerance_positive p epsilon he))

/-- The actual SAME-weight polynomial repair cost fits the allocated half
of the total tolerance at every degree past the computed stage. -/
theorem repair_halfBudget (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat) (hn : repairCutoff p epsilon ≤ n) :
    repairPolynomialCost n p ≤ Q'.invSucc 1 * epsilon := by
  let L := polynomialLipschitz p
  let B := repairCeiling p
  let tau := repairTau p epsilon
  let delta := repairSpacingTolerance p epsilon
  have htau : (0 : Q') < tau := repairTau_positive p epsilon he
  have hrate : Q'.invSucc n ≤ delta := repairCutoff_inverse_bound p epsilon he n hn
  have h48 : 48 * delta ≈ tau * tau :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (repairSpacingTolerance_pin p epsilon)
  have harg : tau*tau + 48*Q'.invSucc n ≤ tau*tau + 48*delta :=
    Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 48 hrate (by decide))
  have harg_pin : tau*tau + 48*delta ≈ 2*(tau*tau) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h48)
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.mul (.const 2) (.mul (.var 0) (.var 0)))
        (by decide) (fun _ => tau))
  have hL : L*(tau*tau + 48*Q'.invSucc n) ≤ L*(2*(tau*tau)) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ harg (polynomialLipschitz_nonnegative p))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ harg_pin))
  have hLB : L*(2*(tau*tau)) ≤ B*(2*(tau*tau)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (lipschitz_le_ceiling p)
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (Q'.le_of_lt htau) (Q'.le_of_lt htau)))
  have hB : B*(2*(tau*tau)) ≈ tau*epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 2) (.mul (.var 1) (.var 1))))
        (.mul (.var 1) (.mul (.var 1) (.mul (.const 2) (.var 0))))
        (by decide) (fun | 0 => B | _ => tau))
      (Q'.mul_eqv_congr_left _ _ _ (repairTau_pin p epsilon))
  have hmain : (2*tau)*repairPolynomialCost n p ≤ tau*epsilon :=
    Q'.le_trans' _ _ _ (repairPolynomialCost_cleared n p tau htau)
      (Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _ hLB (Q'.le_of_eqv hB)))
  have hhalf : (2*tau)*(Q'.invSucc 1*epsilon) ≈ tau*epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => tau | 1 => Q'.invSucc 1 | _ => epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : (2 : Q')*Q'.invSucc 1 ≈ 1))
        (Q'.one_mul_eqv _))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hmain (Q'.ge_of_eqv hhalf))
    (Q'.mul_pos (by decide) htau)

end YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairCeiling
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairCeiling_positive
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairTau
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairTau_positive
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairTau_pin
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairSpacingTolerance
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairSpacingTolerance_positive
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairSpacingTolerance_pin
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairCutoff
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repairCutoff_inverse_bound
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus.repair_halfBudget
