/-
# The actual rational class polynomial of the original heat-prefix margin

All coefficients are the original coeffW and chebPoly coefficients, at one
inclusive K.  The unit-interval polynomial is the actual Horner composition
with [-1,2].  Its strict margin is proved, not supplied.  Substitution into
the original multivariate carrier is pinned at COEFFICIENT level to the
checked quarticMarginPolynomial, not merely at rational environments.

This supplies the concrete polynomial input to the finite Bernstein-row
compiler.  It does not itself construct a Haar Certificate or assert an
interacting variance, changing-family or continuum survival bound.
-/

import YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

namespace YMGap.Continuum.SU2HeatJacobiFinitePrefixClassPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (spacingLabelCutoff)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (standardPointwiseHeatPartial)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c hab)
    (Q'.mul_eqv_congr_left b _ _ hcd)

private theorem eval_singleton (c x : Q') : eval [c] x ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left c _ _ (Q'.mul_zero_eqv x))
    (q_add_zero_eqv c)

private theorem eval_linear (a b x : Q') : eval [a,b] x ≈ a+x*b :=
  Q'.add_eqv_congr_left a _ _ (Q'.mul_eqv_congr_left x _ _ (eval_singleton b x))

private theorem eval_arg_congr {x y : Q'} (h : x ≈ y) : ∀ p : Poly,
    eval p x ≈ eval p y
  | [] => Q'.eqv_refl 0
  | c::p => Q'.add_eqv_congr_left c _ _ (mul_congr h (eval_arg_congr h p))

/-- Original character prefix, with the actual inclusive K+1 labels. -/
def classHeatPrefix (q : Q') (K : Nat) : Poly :=
  polyFinSum (fun r => pscale (coeffW q r) (chebPoly r)) (K+1)

/-- The original chord-quartic margin as an actual coefficient list. -/
def classMarginPolynomial (q : Q') (K : Nat) (eta : Q') : Poly :=
  psub (padd (pscale (quarticProfileCoefficient q) (classHeatPrefix (q*q) K))
    [quarticPrefixError q K+eta])
    (pmul (pmul [2,-2] [2,-2]) (classHeatPrefix q K))

/-- Pull back the closed class interval by the ACTUAL affine polynomial. -/
def unitMarginPolynomial (q : Q') (K : Nat) (eta : Q') : Poly :=
  compose [-1,2] (classMarginPolynomial q K eta)

/-- Exact original character-coefficient evaluation pin. -/
theorem eval_classHeatPrefix (q x : Q') (K : Nat) :
    eval (classHeatPrefix q K) x ≈ standardPointwiseHeatPartial q x (K+1) := by
  refine Q'.eqv_trans _ _ _ (eval_polyFinSum _ x (K+1)) ?_
  apply finSum_eqv_congr
  intro r
  exact Q'.eqv_trans _ _ _ (eval_pscale (coeffW q r) (chebPoly r) x)
    (Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly r x))

private theorem eval_chord (x : Q') : eval [2,-2] x ≈ 2*(1-x) :=
  Q'.eqv_trans _ _ _ (eval_linear 2 (-2) x)
    (poly_identity_of_normal_eq
      (.add (.const 2) (.mul (.var 0) (.const (-2))))
      (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))
      (by decide) (fun _ => x))

/-- Evaluation of the literal class-margin polynomial, not a grid proxy. -/
theorem eval_classMarginPolynomial (q x : Q') (K : Nat) (eta : Q') :
    eval (classMarginPolynomial q K eta) x ≈
      (quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) x (K+1) +
        (quarticPrefixError q K+eta)) +
      -(((2*(1-x))*(2*(1-x)))*standardPointwiseHeatPartial q x (K+1)) := by
  refine Q'.eqv_trans _ _ _ (eval_psub _ _ x) ?_
  apply q_add_congr
  · refine Q'.eqv_trans _ _ _ (eval_padd _ _ x) ?_
    exact q_add_congr
      (Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
        (Q'.mul_eqv_congr_left _ _ _ (eval_classHeatPrefix (q*q) x K)))
      (eval_singleton _ x)
  · apply Q'.neg_eqv_congr
    refine Q'.eqv_trans _ _ _ (eval_pmul _ _ x) ?_
    exact mul_congr
      (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr (eval_chord x) (eval_chord x)))
      (eval_classHeatPrefix q x K)

private theorem eval_affine (y : Q') : eval [-1,2] y ≈ -1+2*y :=
  Q'.eqv_trans _ _ _ (eval_linear (-1) 2 y)
    (Q'.add_eqv_congr_left (-1) _ _ (Q'.mul_comm_eqv y 2))

/-- Exact pullback to the unit interval, for every rational argument. -/
theorem eval_unitMarginPolynomial (q y : Q') (K : Nat) (eta : Q') :
    eval (unitMarginPolynomial q K eta) y ≈
      eval (classMarginPolynomial q K eta) (-1+2*y) :=
  Q'.eqv_trans _ _ _ (eval_compose [-1,2] y _)
    (eval_arg_congr (eval_affine y) _)

/-- The proved closed class-interval margin for the actual QPoly list. -/
theorem eta_le_classMargin_eval {q eta x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (heta : (0 : Q') < eta)
    (K : Nat) (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    eta ≤ eval (classMarginPolynomial q K eta) x ∧
      (0 : Q') < eval (classMarginPolynomial q K eta) x := by
  have h := inclusivePrefix_chord_quartic_bound hq0 hq1 hq hxlo hxhi K hKq hKqq
  have hh := Q'.add_le_add_left eta _ _ (Q'.sub_nonneg_of_le h)
  have hr : eta+((quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) x (K+1)+
      quarticPrefixError q K) + -(((2*(1-x))*(2*(1-x)))*
        standardPointwiseHeatPartial q x (K+1))) ≈
      (quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) x (K+1) +
        (quarticPrefixError q K+eta)) +
      -(((2*(1-x))*(2*(1-x)))*standardPointwiseHeatPartial q x (K+1)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.add (.var 1) (.var 2)) (.var 3)))
      (.add (.add (.var 1) (.add (.var 2) (.var 0))) (.var 3))
      (by decide) (fun
        | 0 => eta
        | 1 => quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) x (K+1)
        | 2 => quarticPrefixError q K
        | _ => -(((2*(1-x))*(2*(1-x)))*standardPointwiseHeatPartial q x (K+1)))
  have hmargin := Q'.le_trans' _ _ _ (Q'.ge_of_eqv (q_add_zero_eqv eta))
    (Q'.le_trans' _ _ _ hh (Q'.le_trans' _ _ _ (Q'.le_of_eqv hr)
      (Q'.ge_of_eqv (eval_classMarginPolynomial q x K eta))))
  exact ⟨hmargin,Q'.pos_of_lt_of_le heta hmargin⟩

/-- Computed actual polynomial input to the positive Bernstein-row compiler.
Both original K+1 guards and both unit-interval endpoints are retained. -/
theorem eta_le_unitMargin_eval {q eta y : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (heta : (0 : Q') < eta)
    (K : Nat) (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1)
    (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ (1 : Q')) :
    eta ≤ eval (unitMarginPolynomial q K eta) y := by
  have hlo : (-1 : Q') ≤ -1+2*y :=
    Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hy0)
  have hhi : -1+2*y ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left (-1) _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hy1 (by decide)))
      (Q'.le_of_eqv (by decide : (-1 : Q')+2*1 ≈ 1))
  exact Q'.le_trans' _ _ _
    (eta_le_classMargin_eval hq0 hq1 hq heta K hKq hKqq hlo hhi).1
    (Q'.ge_of_eqv (eval_unitMarginPolynomial q y K eta))

private theorem finiteSum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs++ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | head::xs,ys => by
      rw [List.cons_append]
      change polyAdd (f head) (finitePolySum f (xs++ys)) =
        polyAdd (polyAdd (f head) (finitePolySum f xs)) (finitePolySum f ys)
      rw [finiteSum_append f xs ys]
      exact (List.append_assoc _ _ _).symm

private theorem subst_polyFinSum (X : RatPoly) (f : Nat → Poly) : ∀ N : Nat,
    RatPolyCoeffEqv (subst X (polyFinSum f N))
      (finitePolySum (fun r => subst X (f r)) (List.range N))
  | 0 => RatPolyCoeffEqv.refl _
  | N+1 => by
      rw [List.range_succ,finiteSum_append]
      simp only [finitePolySum,polyAdd]
      exact (subst_padd X (polyFinSum f N) (f N)).trans
        ((subst_polyFinSum X f N).add (RatPolyCoeffEqv.add_zero (subst X (f N))).symm)

private theorem finiteSum_congr {A : Type} {f g : A → RatPoly}
    (h : ∀ r, RatPolyCoeffEqv (f r) (g r)) : ∀ xs : List A,
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | r::xs => (h r).add (finiteSum_congr h xs)

/-- Actual class-prefix substitution has the ORIGINAL heatPrefix coefficients. -/
theorem subst_classHeatPrefix (X : RatPoly) (q : Q') (K : Nat) :
    RatPolyCoeffEqv (subst X (classHeatPrefix q K)) (heatPrefix q K X) :=
  (subst_polyFinSum X _ (K+1)).trans
    (finiteSum_congr (fun r => (subst_pscale X (coeffW q r) (chebPoly r)).trans
      ((subst_chebPoly X r).smul (coeffW q r))) (List.range (K+1)))

private theorem smul_neg_one : ∀ P : RatPoly,
    RatPolyCoeffEqv (polySmul (-1) P) (polyNeg P)
  | [] => RatPolyCoeffEqv.refl _
  | term::rest => by
      intro weight
      change (((-1 : Q')*term.2)*weight term.1 +
          ratWeightedSum weight (polySmul (-1) rest)) ≈
        ((-term.2)*weight term.1 + ratWeightedSum weight (polyNeg rest))
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 term.2)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv term.2))))
        (smul_neg_one rest weight)

private theorem subst_pneg (X : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (subst X (pneg p)) (polyNeg (subst X p)) :=
  (subst_pscale X (-1) p).trans (smul_neg_one _)

private theorem subst_chord (X : RatPoly) :
    RatPolyCoeffEqv (subst X [2,-2]) (polySmul 2 (polyAdd polyOne (polyNeg X))) := by
  have htail : RatPolyCoeffEqv (polyMul X (subst X [-2])) (polySmul 2 (polyNeg X)) :=
    ((subst_singleton X (-2)).mul_left X).trans
      ((RatPolyCoeffEqv.polyMul_smul_right (-2) X polyOne).trans
        (((RatPolyCoeffEqv.mul_one X).smul (-2)).trans
          ((RatPolyCoeffEqv.smul_coefficient (by decide : (-2 : Q') ≈ 2*(-1)) X).trans
            ((RatPolyCoeffEqv.smul_assoc 2 (-1) X).symm.trans ((smul_neg_one X).smul 2)))))
  exact ((RatPolyCoeffEqv.refl (polySmul 2 polyOne)).add htail).trans
    (RatPolyCoeffEqv.smul_add 2 polyOne (polyNeg X)).symm

/-- The essential coefficient-level join: the computed class polynomial
is EXACTLY the checked original multivariate heat-prefix margin after
substitution. No environment equality or supplied identity replaces it. -/
theorem subst_classMarginPolynomial (X : RatPoly) (q : Q') (K : Nat) (eta : Q') :
    RatPolyCoeffEqv (subst X (classMarginPolynomial q K eta))
      (quarticMarginPolynomial q K eta X) := by
  refine (subst_padd X _ _).trans ?_
  apply RatPolyCoeffEqv.add
  · exact (subst_padd X _ _).trans
      (((subst_pscale X (quarticProfileCoefficient q) _).trans
        ((subst_classHeatPrefix X (q*q) K).smul (quarticProfileCoefficient q))).add
        (subst_singleton X (quarticPrefixError q K+eta)))
  · exact (subst_pneg X _).trans
      (RatPolyCoeffEqv.neg ((subst_pmul X _ _).trans
        (((subst_pmul X _ _).trans ((subst_chord X).mul (subst_chord X))).mul
          (subst_classHeatPrefix X q K))))

#print axioms classHeatPrefix
#print axioms classMarginPolynomial
#print axioms unitMarginPolynomial
#print axioms eval_classHeatPrefix
#print axioms eval_classMarginPolynomial
#print axioms eval_unitMarginPolynomial
#print axioms eta_le_classMargin_eval
#print axioms eta_le_unitMargin_eval
#print axioms subst_classHeatPrefix
#print axioms subst_classMarginPolynomial

end YMGap.Continuum.SU2HeatJacobiFinitePrefixClassPolynomial
