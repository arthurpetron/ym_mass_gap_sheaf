/-
# Literal square and angular-energy curves of the ORIGINAL head heat

Finite nome rows are multiplied and tangentially differentiated before their
coefficient pderiv is evaluated. The resulting square/Gamma derivatives are
proved to be the actual original input-generator expressions; they are not
DEFINED by those expressions. Shared retained-link/spectator coefficients
remain arbitrary. This is the inner product-rule leg of the Laurent heat
interpolation, not a conditional variance or physical mass-gap estimate.
-/

import YMGap.Continuum.RatPolyNomeRows
import YMGap.Continuum.SU2QuaternionHeadHeatGenerator
import YMGap.Continuum.SU2QuaternionAngularBochner

namespace YMGap.Continuum.SU2QuaternionHeadHeatCurves

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir (angularLaplacian_carrier)
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator
open YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow
open YMGap.Continuum.SU2QuaternionAngularBochner (mixedGamma gamma2)
open YMGap.Continuum.RatPolyNomeRows

private def sixRows (f : Nat → Nat → Rows) : Rows :=
  f 0 1 ++ (f 0 2 ++ (f 0 3 ++ (f 1 2 ++ (f 1 3 ++ f 2 3))))

private theorem six_coeff {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) :=
  (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

private theorem evalRows_sixRows (f : Nat → Nat → Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (sixRows f) r) (six fun i j => evalRows (f i j) r) :=
  (evalRows_append _ _ r).trans
    ((RatPolyCoeffEqv.refl _).add ((evalRows_append _ _ r).trans
      ((RatPolyCoeffEqv.refl _).add ((evalRows_append _ _ r).trans
        ((RatPolyCoeffEqv.refl _).add ((evalRows_append _ _ r).trans
          ((RatPolyCoeffEqv.refl _).add (evalRows_append _ _ r))))))))

private theorem derivative_sixRows (f : Nat → Nat → Rows) :
    derivativeRows (sixRows f) = sixRows (fun i j => derivativeRows (f i j)) := by
  simp only [sixRows, derivativeRows, List.map_append]

/-- Literal coefficient rows of the square, retaining all original groups. -/
def squareNomeRows (tail : Nat) (p : RatPoly) : Rows :=
  mulRows (nomeHeatPolynomial tail p) (nomeHeatPolynomial tail p)

/-- Literal coefficient rows of the SAME six original rotations' energy. -/
def angularNomeRows (tail : Nat) (p : RatPoly) : Rows :=
  sixRows fun i j =>
    mulRows (mapRows (angularDerivative i j) (nomeHeatPolynomial tail p))
      (mapRows (angularDerivative i j) (nomeHeatPolynomial tail p))

def formalSquareNomeDerivative (tail : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  evalRows (derivativeRows (squareNomeRows tail p)) r

def formalAngularNomeDerivative (tail : Nat) (p : RatPoly) (r : Q') : RatPoly :=
  evalRows (derivativeRows (angularNomeRows tail p)) r

/-- The finite coefficient representation is literally the actual flow square. -/
theorem squareNomeRows_eval (tail : Nat) (p : RatPoly) (r : Q') :
    RatPolyCoeffEqv (evalRows (squareNomeRows tail p) r)
      (polyMul (finiteNomeFlow tail p r) (finiteNomeFlow tail p r)) :=
  evalRows_mul _ _ r

theorem angularNomeRows_eval (tail : Nat) (p : RatPoly) (r : Q') :
    RatPolyCoeffEqv (evalRows (angularNomeRows tail p) r)
      (angularSquare (finiteNomeFlow tail p r)) := by
  refine (evalRows_sixRows _ r).trans (six_coeff (fun i j => ?_))
  exact (evalRows_mul _ _ r).trans
    ((evalRows_angularDerivative i j _ r).mul (evalRows_angularDerivative i j _ r))

private theorem product_twice (a b : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyMul b a) (polyMul a b))
      (polySmul 2 (polyMul a b)) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
    (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
    (fun | 0 => a | _ => b)).trans (cap_mul_left 2 _)

/-- Actual literal coefficient product rule, before the heat generator is used. -/
theorem formalSquareNomeDerivative_pin (tail : Nat) (p : RatPoly) (r : Q') :
    RatPolyCoeffEqv (formalSquareNomeDerivative tail p r)
      (polySmul 2 (polyMul (finiteNomeFlow tail p r) (formalNomeDerivative tail p r))) := by
  let A := nomeHeatPolynomial tail p
  have h := (evalRows_derivative_mul A A r).trans
    (product_twice (evalRows A r) (evalRows (derivativeRows A) r))
  simpa only [A, formalSquareNomeDerivative, squareNomeRows, evalRows,
    derivativeRows, finiteNomeFlow, formalNomeDerivative, List.map_map, Function.comp_def] using h

private theorem derivative_map_angular (i j : Nat) (A : Rows) :
    derivativeRows (mapRows (angularDerivative i j) A) =
      mapRows (angularDerivative i j) (derivativeRows A) := by
  simp only [derivativeRows, mapRows, List.map_map, Function.comp_def]

/-- Genuine pderiv of the six-direction coefficient curve; the source may
depend on the original retained output and every spectator. -/
theorem formalAngularNomeDerivative_pin (tail : Nat) (p : RatPoly) (r : Q') :
    RatPolyCoeffEqv (formalAngularNomeDerivative tail p r)
      (polySmul 2 (mixedGamma (finiteNomeFlow tail p r) (formalNomeDerivative tail p r))) := by
  unfold formalAngularNomeDerivative angularNomeRows
  rw [derivative_sixRows]
  refine (evalRows_sixRows _ r).trans ?_
  refine (six_coeff (fun i j => ?_)).trans (six_smul 2 _)
  have he := evalRows_derivative_mul
    (mapRows (angularDerivative i j) (nomeHeatPolynomial tail p))
    (mapRows (angularDerivative i j) (nomeHeatPolynomial tail p)) r
  rw [derivative_map_angular] at he
  have h := he.trans
    (((evalRows_angularDerivative i j _ r).mul (evalRows_angularDerivative i j _ r)).add
      ((evalRows_angularDerivative i j _ r).mul (evalRows_angularDerivative i j _ r)))
  have h' := h.trans (product_twice
    (angularDerivative i j (evalRows (nomeHeatPolynomial tail p) r))
    (angularDerivative i j (evalRows (derivativeRows (nomeHeatPolynomial tail p)) r)))
  simpa only [evalRows, derivativeRows, finiteNomeFlow, formalNomeDerivative,
    List.map_map, Function.comp_def] using h'

private theorem mixedGamma_right_smul (p q : RatPoly) (c : Q') :
    RatPolyCoeffEqv (mixedGamma p (polySmul c q)) (polySmul c (mixedGamma p q)) :=
  (six_coeff (fun i j =>
    ((angularDerivative_smul i j c q).mul_left (angularDerivative i j p)).trans
      (RatPolyCoeffEqv.polyMul_smul_right c _ _))).trans (six_smul c _)

private theorem mixedGamma_right_carrier {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) {q q' : RatPoly} (h : HaarCarrierEqv blocks q q') :
    HaarCarrierEqv blocks (mixedGamma p q) (mixedGamma p q') :=
  six_carrier (fun _ _ hi hj => HaarCarrierEqv.mul_left _
    (angularDerivative_carrier hb hi hj h))

/-- Reuse the checked actual source generator, without supplying one as a
new hypothesis or confusing the original flow with a surrogate. -/
theorem finiteNomeFlow_formal_generator (tail : Nat) (p : RatPoly) (r : Q')
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (polySmul r (formalNomeDerivative tail p r))
      (polyNeg (angularLaplacian (finiteNomeFlow tail p r))) :=
  (headMap_formal_nome_generator tail r (inputCutoff tail p) p hp (Nat.le_refl _)).trans
    (HaarCarrierEqv.neg (angularLaplacian_carrier (Nat.zero_lt_succ tail)
      (finiteNomeFlow_original_pin tail r (inputCutoff tail p) p hp (Nat.le_refl _)).symm))

/-- Literal square-curve Euler derivative for the actual saturated heat. -/
theorem squareNomeCurve_formal_generator (tail : Nat) (p : RatPoly) (r : Q')
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (polySmul r (formalSquareNomeDerivative tail p r))
      (polyNeg (polySmul 2 (polyMul (finiteNomeFlow tail p r)
        (angularLaplacian (finiteNomeFlow tail p r))))) := by
  let V := finiteNomeFlow tail p r
  let D := formalNomeDerivative tail p r
  have hmove : RatPolyCoeffEqv (polySmul r (polySmul 2 (polyMul V D)))
      (polySmul 2 (polyMul V (polySmul r D))) :=
    (RatPolyCoeffEqv.smul_assoc r 2 _).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv r 2) _).trans
        ((RatPolyCoeffEqv.smul_assoc 2 r _).symm.trans
          (RatPolyCoeffEqv.smul 2 (RatPolyCoeffEqv.polyMul_smul_right r V D).symm)))
  have hfinish : RatPolyCoeffEqv (polySmul 2 (polyMul V (polyNeg (angularLaplacian V))))
      (polyNeg (polySmul 2 (polyMul V (angularLaplacian V)))) :=
    ((neg_smul _).mul_left V).smul 2 |>.trans
      ((RatPolyCoeffEqv.polyMul_smul_right (-1) V _).smul 2 |>.trans
        ((RatPolyCoeffEqv.smul_assoc 2 (-1) _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv 2 (-1)) _).trans
            ((RatPolyCoeffEqv.smul_assoc (-1) 2 _).symm.trans (neg_smul _).symm))))
  exact (RatPolyCoeffEqv.haarCarrier ((formalSquareNomeDerivative_pin tail p r).smul r)).trans
    ((RatPolyCoeffEqv.haarCarrier hmove).trans
      ((HaarCarrierEqv.smul 2 (HaarCarrierEqv.mul_left V
        (finiteNomeFlow_formal_generator tail p r hp))).trans
        (RatPolyCoeffEqv.haarCarrier hfinish)))

/-- Literal angular-energy curve Euler derivative, on the original carrier. -/
theorem angularNomeCurve_formal_generator (tail : Nat) (p : RatPoly) (r : Q')
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (polySmul r (formalAngularNomeDerivative tail p r))
      (polyNeg (polySmul 2 (mixedGamma (finiteNomeFlow tail p r)
        (angularLaplacian (finiteNomeFlow tail p r))))) := by
  let V := finiteNomeFlow tail p r
  let D := formalNomeDerivative tail p r
  have hmove : RatPolyCoeffEqv (polySmul r (polySmul 2 (mixedGamma V D)))
      (polySmul 2 (mixedGamma V (polySmul r D))) :=
    (RatPolyCoeffEqv.smul_assoc r 2 _).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv r 2) _).trans
        ((RatPolyCoeffEqv.smul_assoc 2 r _).symm.trans
          (RatPolyCoeffEqv.smul 2 (mixedGamma_right_smul V D r).symm)))
  have hfinish : RatPolyCoeffEqv (polySmul 2 (mixedGamma V (polyNeg (angularLaplacian V))))
      (polyNeg (polySmul 2 (mixedGamma V (angularLaplacian V)))) :=
    ((six_coeff (fun i j => RatPolyCoeffEqv.mul_left _
      (angularDerivative_congr i j (neg_smul _)))).trans
      (mixedGamma_right_smul V _ (-1))).smul 2 |>.trans
        ((RatPolyCoeffEqv.smul_assoc 2 (-1) _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv 2 (-1)) _).trans
            ((RatPolyCoeffEqv.smul_assoc (-1) 2 _).symm.trans (neg_smul _).symm)))
  exact (RatPolyCoeffEqv.haarCarrier ((formalAngularNomeDerivative_pin tail p r).smul r)).trans
    ((RatPolyCoeffEqv.haarCarrier hmove).trans
      ((HaarCarrierEqv.smul 2 (mixedGamma_right_carrier (Nat.zero_lt_succ tail) V
        (finiteNomeFlow_formal_generator tail p r hp))).trans
        (RatPolyCoeffEqv.haarCarrier hfinish)))

end YMGap.Continuum.SU2QuaternionHeadHeatCurves

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.squareNomeRows
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.angularNomeRows
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.formalSquareNomeDerivative
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.formalAngularNomeDerivative
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.squareNomeRows_eval
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.angularNomeRows_eval
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.formalSquareNomeDerivative_pin
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.formalAngularNomeDerivative_pin
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.finiteNomeFlow_formal_generator
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.squareNomeCurve_formal_generator
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurves.angularNomeCurve_formal_generator
