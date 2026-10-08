/-
# Actual substitution of the finite Jacobi radial polynomial

The radial class polynomial is substituted into the original carrier by its
literal Horner map. This pins that substitution to the shifted heat and its
actual first two jets; it is finite algebra only, with no restriction on the
rational input or the prefix (including the empty prefix).
-/

import YMGap.Continuum.JacobiHeatRadialHaarCertificate
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

namespace YMGap.Continuum.JacobiHeatRadialSubstitutionPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.QPolyAffineJetTranslation (translate)
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat)
open YMGap.Continuum.JacobiHeatRadialHaarCertificate (radialPolynomial)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv

private theorem shifted_substitution (X : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (subst X (translate 1 p))
      (subst (polyAdd polyOne X) p) := by
  unfold translate
  exact (subst_compose X [1,1] p).trans
    (subst_arg (subst_one_add X) p)

private theorem shifted_jets (X : RatPoly) (w : Q') (N : Nat) :
    RatPolyCoeffEqv (subst X (translate 1 (heat w N)))
      (subst (polyAdd polyOne X) (heat w N)) ∧
    RatPolyCoeffEqv (subst X (translate 1 (pderiv (heat w N))))
      (subst (polyAdd polyOne X) (pderiv (heat w N))) ∧
    RatPolyCoeffEqv (subst X (translate 1 (pderiv (pderiv (heat w N)))))
      (subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))) := by
  exact ⟨shifted_substitution X _, shifted_substitution X _, shifted_substitution X _⟩

private theorem substituted_one_minus_square (X : RatPoly) :
    RatPolyCoeffEqv (subst X [1,0,-1])
      (polyAdd polyOne (polyNeg (polyMul X X))) := by
  have hminus : RatPolyCoeffEqv (subst X [-1]) (polyNeg polyOne) :=
    (subst_singleton X (-1)).trans (neg_smul polyOne).symm
  have htail : RatPolyCoeffEqv (subst X [0,-1])
      (polyMul X (polyNeg polyOne)) :=
    (subst_zero_cons X [-1]).trans (hminus.mul_left X)
  have hprod : RatPolyCoeffEqv (polyMul X (polyNeg polyOne)) (polyNeg X) := by
    exact ((RatPolyCoeffEqv.refl X).mul (neg_smul polyOne)).trans
      ((RatPolyCoeffEqv.polyMul_smul_right (-1) X polyOne).trans
        (((RatPolyCoeffEqv.mul_one X).smul (-1)).trans (neg_smul X).symm))
  have hsquare : RatPolyCoeffEqv (polyMul X (polyNeg X))
      (polyNeg (polyMul X X)) := by
    exact ((RatPolyCoeffEqv.refl X).mul (neg_smul X)).trans
      ((RatPolyCoeffEqv.polyMul_smul_right (-1) X X).trans
        (neg_smul (polyMul X X)).symm)
  change RatPolyCoeffEqv
    (polyAdd (polySmul 1 polyOne) (polyMul X (subst X [0,-1]))) _
  exact (RatPolyCoeffEqv.one_smul polyOne).add
    (((htail.trans hprod).mul_left X).trans hsquare)

private theorem substituted_variable (X : RatPoly) :
    RatPolyCoeffEqv (subst X [0,1]) X := by
  exact (subst_zero_cons X [1]).trans
    ((subst_singleton X 1).mul_left X |>.trans
      ((RatPolyCoeffEqv.one_smul polyOne).mul_left X |>.trans
        (RatPolyCoeffEqv.mul_one X)))

private theorem negated_substitution (X : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (subst X (pneg p)) (polyNeg (subst X p)) := by
  exact (subst_pscale X (-1) p).trans (neg_smul (subst X p)).symm

private theorem shifted_product (X : RatPoly) (w : Q') (N : Nat) :
    RatPolyCoeffEqv
      (subst X (pmul (translate 1 (heat w N)) (translate 1 (pderiv (heat w N)))))
      (polyMul (subst (polyAdd polyOne X) (heat w N))
        (subst (polyAdd polyOne X) (pderiv (heat w N)))) := by
  have hj := shifted_jets X w N
  exact (subst_pmul X (translate 1 (heat w N))
      (translate 1 (pderiv (heat w N)))).trans (hj.1.mul hj.2.1)

private theorem cap_product (C : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul C p) (polyMul (cap C) p) := by
  change RatPolyCoeffEqv (polySmul C p) (polyMul (polySmul C polyOne) p)
  exact ((RatPolyCoeffEqv.polyMul_smul_left C polyOne p).trans
    ((RatPolyCoeffEqv.one_mul p).smul C)).symm

/-- The actual original-carrier substitution of the produced radial class
polynomial, in terms of the literal shifted heat and its first two formal
derivatives. This is valid for every rational input, coefficient and prefix. -/
theorem radial_substitution_pin (X : RatPoly) (w C : Q') (N : Nat) :
    let h := subst (polyAdd polyOne X) (heat w N)
    let hx := subst (polyAdd polyOne X) (pderiv (heat w N))
    let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))
    RatPolyCoeffEqv (subst X (radialPolynomial w N C))
      (polyAdd (polyMul (cap C) (polyMul h h))
        (polyAdd
          (polyMul (polyAdd polyOne (polyNeg (polyMul X X)))
            (polyAdd (polyMul h hxx) (polyNeg (polyMul hx hx))))
          (polyNeg (polyMul X (polyMul h hx))))) := by
  let H := translate 1 (heat w N)
  let Hx := translate 1 (pderiv (heat w N))
  let Hxx := translate 1 (pderiv (pderiv (heat w N)))
  let h := subst (polyAdd polyOne X) (heat w N)
  let hx := subst (polyAdd polyOne X) (pderiv (heat w N))
  let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))
  have hj := shifted_jets X w N
  have h0 : RatPolyCoeffEqv (subst X H) h := hj.1
  have h1 : RatPolyCoeffEqv (subst X Hx) hx := hj.2.1
  have h2 : RatPolyCoeffEqv (subst X Hxx) hxx := hj.2.2
  have hcoord := substituted_one_minus_square X
  have hvar := substituted_variable X
  have hhh : RatPolyCoeffEqv (subst X (pmul H H)) (polyMul h h) :=
    (subst_pmul X H H).trans (h0.mul h0)
  have hfirstprod : RatPolyCoeffEqv (subst X (pmul H Hxx)) (polyMul h hxx) :=
    (subst_pmul X H Hxx).trans (h0.mul h2)
  have hsecondprod : RatPolyCoeffEqv (subst X (pmul Hx Hx)) (polyMul hx hx) :=
    (subst_pmul X Hx Hx).trans (h1.mul h1)
  have hdifference : RatPolyCoeffEqv
      (subst X (psub (pmul H Hxx) (pmul Hx Hx)))
      (polyAdd (polyMul h hxx) (polyNeg (polyMul hx hx))) := by
    exact (subst_padd X (pmul H Hxx) (pneg (pmul Hx Hx))).trans
      (hfirstprod.add ((negated_substitution X (pmul Hx Hx)).trans
        (RatPolyCoeffEqv.neg hsecondprod)))
  have hfirstpart : RatPolyCoeffEqv
      (subst X (pmul [1,0,-1] (psub (pmul H Hxx) (pmul Hx Hx))))
      (polyMul (polyAdd polyOne (polyNeg (polyMul X X)))
        (polyAdd (polyMul h hxx) (polyNeg (polyMul hx hx)))) := by
    exact (subst_pmul X [1,0,-1] _).trans (hcoord.mul hdifference)
  have hlastproduct : RatPolyCoeffEqv
      (subst X (pmul [0,1] (pmul H Hx))) (polyMul X (polyMul h hx)) := by
    exact (subst_pmul X [0,1] _).trans (hvar.mul (shifted_product X w N))
  have hlast : RatPolyCoeffEqv (subst X (pneg (pmul [0,1] (pmul H Hx))))
      (polyNeg (polyMul X (polyMul h hx))) :=
    (negated_substitution X (pmul [0,1] (pmul H Hx))).trans
      (RatPolyCoeffEqv.neg hlastproduct)
  have hbase : RatPolyCoeffEqv (subst X (pscale C (pmul H H)))
      (polyMul (cap C) (polyMul h h)) := by
    exact (subst_pscale X C (pmul H H)).trans
      ((hhh.smul C).trans (cap_product C (polyMul h h)))
  -- Expand only the constructors defining this radial polynomial. Every
  -- factor is transported by an actual substitution algebra lemma above.
  unfold radialPolynomial
  exact (subst_padd X _ _).trans (hbase.add
    ( (subst_padd X _ _).trans (hfirstpart.add hlast)))

end YMGap.Continuum.JacobiHeatRadialSubstitutionPin

#print axioms YMGap.Continuum.JacobiHeatRadialSubstitutionPin.radial_substitution_pin
