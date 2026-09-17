/-
# Prepending one unit factor to the finite signed family

The original kinetic product is unchanged. Its flow acquires the product
times the new test; its cost acquires that test's diagonal and the exact
signed cross term 2*h*x*flow. The test may already be an aggregate. The
algebraic identities have no positivity or independence hypotheses.

For 0<h<=1, the existing finite-family inequality applies to this unit
factor as well. The resulting estimate retains the signed cross term;
it does not supply a marginal-norm bound for the complete cost.

The consumer groups the original inactive-coordinate tests before joining
them to the active heat family. No cross term is replaced by separate norms.
-/

import YMGap.Continuum.QuaternionHaarFiniteFamilyDual
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.QuaternionHaarUnitFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- A unit factor leaves the entire original product unchanged. -/
theorem product_prepend_unit (x : RatPoly) (ps : List (RatPoly × RatPoly)) :
    RatPolyCoeffEqv (product ((polyOne, x) :: ps)) (product ps) :=
  RatPolyCoeffEqv.one_mul (product ps)

/-- The added test is multiplied by the complete original product. -/
theorem flow_prepend_unit (x : RatPoly) (ps : List (RatPoly × RatPoly)) :
    RatPolyCoeffEqv (flow ((polyOne, x) :: ps))
      (polyAdd (polyMul (product ps) x) (flow ps)) :=
  (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_mul (flow ps))

/-- The signed cross term is exactly h times two copies of x*flow. -/
theorem cost_prepend_unit (h : Q') (x : RatPoly) (ps : List (RatPoly × RatPoly)) :
    RatPolyCoeffEqv (cost h ((polyOne, x) :: ps))
      (polyAdd
        (polyAdd (polyMul (product ps) (polyMul x x)) (cost h ps))
        (polyMul (cap h) (polyAdd (polyMul x (flow ps)) (polyMul x (flow ps))))) :=
  ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_mul (cost h ps))).add
    (RatPolyCoeffEqv.refl _)

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private def unitFloorCertificate {n : Nat} {h : Q'} (hh : h ≤ (1 : Q')) :
    Certificate n (polyAdd polyOne (polyNeg (cap h))) :=
  .ofCoeff (((RatPolyCoeffEqv.one_smul polyOne).symm.add (cap_neg h)).trans (cap_add 1 (-h)))
    (Certificate.constant n (1 + -h) (Q'.sub_nonneg_of_le hh))

private theorem haar_weighted_cap (n : Nat) (mu p : RatPoly) (c : Q') :
    H n (polyMul mu (polyMul (cap c) p)) ≈ c * H n (polyMul mu p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (((cap_mul_left c p).mul_left mu).trans
      (RatPolyCoeffEqv.polyMul_smul_right c mu p)))
    (quaternionHaar_polySmul n c (polyMul mu p))

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- An aggregate signed test can be joined as one unit factor. The original
product and its energy pairing are unchanged, and the exact mixed cost is
retained. No centering, decomposition, or bound on that mixed cost is assumed. -/
theorem prepend_unit_dual {n : Nat} {h : Q'}
    (hh : (0 : Q') < h) (h1 : h ≤ (1 : Q'))
    (ps : List (RatPoly × RatPoly))
    (C : ∀ p, p ∈ ps → Certificate n (polyAdd p.1 (polyNeg (cap h))))
    (hx : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p.2)
    {mu z x : RatPoly} (M : Certificate n mu)
    (hz : SupportedQuaternionBlocks n z) (hxnew : SupportedQuaternionBlocks n x) :
    h *
        ((H n (polyMul mu (polyMul (flow ps) z)) +
            H n (polyMul mu (polyMul (product ps) (polyMul x z)))) *
          (H n (polyMul mu (polyMul (flow ps) z)) +
            H n (polyMul mu (polyMul (product ps) (polyMul x z))))) ≤
      H n (polyMul mu (polyMul (product ps) (polyMul z z))) *
        ((H n (polyMul mu (cost h ps)) +
            H n (polyMul mu (polyMul (product ps) (polyMul x x)))) +
          ((2 : Q') * h) * H n (polyMul mu (polyMul x (flow ps)))) := by
  let C' : ∀ p, p ∈ (polyOne, x) :: ps →
      Certificate n (polyAdd p.1 (polyNeg (cap h))) := fun p hp =>
    if he : p = (polyOne, x) then by
      subst p
      exact unitFloorCertificate h1
    else C p ((List.mem_cons.mp hp).resolve_left he)
  have hx' : ∀ p, p ∈ (polyOne, x) :: ps → SupportedQuaternionBlocks n p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      exact hxnew
    · exact hx p hp
  let J := H n (polyMul mu (polyMul (product ps) (polyMul z z)))
  let L := H n (polyMul mu (polyMul (flow ps) z))
  let Lx := H n (polyMul mu (polyMul (product ps) (polyMul x z)))
  let Q := H n (polyMul mu (cost h ps))
  let D := H n (polyMul mu (polyMul (product ps) (polyMul x x)))
  let X := H n (polyMul mu (polyMul x (flow ps)))
  have hproduct : H n (polyMul mu
      (polyMul (product ((polyOne, x) :: ps)) (polyMul z z))) ≈ J :=
    haar_of_coeff (((product_prepend_unit x ps).mul_right (polyMul z z)).mul_left mu)
  have hflow : H n (polyMul mu (polyMul (flow ((polyOne, x) :: ps)) z)) ≈ L + Lx := by
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff (((flow_prepend_unit x ps).mul_right z).mul_left mu)) ?_
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (haar_weighted_add n mu _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc (product ps) x z).mul_left mu))
          (Q'.eqv_refl L))
        (Q'.add_comm_eqv Lx L))
  have hcost : H n (polyMul mu (cost h ((polyOne, x) :: ps))) ≈
      (Q + D) + ((2 : Q') * h) * X := by
    refine Q'.eqv_trans _ _ _ (haar_of_coeff ((cost_prepend_unit h x ps).mul_left mu)) ?_
    refine Q'.eqv_trans _ _ _ (haar_weighted_add n mu _ _) ?_
    have hc : H n (polyMul mu
        (polyMul (cap h) (polyAdd (polyMul x (flow ps)) (polyMul x (flow ps))))) ≈
        h * (X + X) :=
      Q'.eqv_trans _ _ _ (haar_weighted_cap n mu _ h)
        (Q'.mul_eqv_congr_left _ _ _ (haar_weighted_add n mu _ _))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (haar_weighted_add n mu _ _) hc) ?_
    exact poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.mul (.var 2) (.add (.var 3) (.var 3))))
      (.add (.add (.var 1) (.var 0)) (.mul (.mul (.const 2) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => D | 1 => Q | 2 => h | _ => X)
  have hleft := Q'.mul_eqv_congr_left h _ _ (qmul hflow hflow)
  have hright := qmul hproduct hcost
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ (finite_family_dual hh ((polyOne, x) :: ps) C' hx' M hz)
      (Q'.le_of_eqv hright))

#print axioms product_prepend_unit
#print axioms flow_prepend_unit
#print axioms cost_prepend_unit
#print axioms prepend_unit_dual

end YMGap.Continuum.QuaternionHaarUnitFamily
