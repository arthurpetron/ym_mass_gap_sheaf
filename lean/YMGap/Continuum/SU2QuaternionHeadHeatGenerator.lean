/-
# Formal nome generator of the ORIGINAL saturated head heat

The actual finite flow is represented by QPoly coefficient polynomials and
original signed harmonic groups. Its nome derivative is the literal pderiv
of those polynomials, NOT a definition using the angular Casimir. The
identity w*d_w P_w=-L P_w holds under every Haar insertion, retaining all
shared spectators and the computed input cutoff. It includes nome zero.
No analytic/physical generator, positivity at nome one, conditional variance
bound or scaling estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatSemigroup
import YMGap.Continuum.QuaternionHaarAngularCasimir
import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
import YMGap.Constructive.QPolyFiniteGeometric
import YMGap.Constructive.QPolyCoefficientEvaluation

namespace YMGap.Continuum.SU2QuaternionHeadHeatGenerator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal (headMap)
open YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow

local infix:50 " ≈ " => Q'.eqv

private def degrees (tail : Nat) (p : RatPoly) : List Nat :=
  headDegrees (sumHarmonics (modes (tail+1) (Nat.zero_lt_succ tail) p))

private def group (tail : Nat) (p : RatPoly) (d : Nat) : RatPoly :=
  grouped d (modes (tail+1) (Nat.zero_lt_succ tail) p)

/-- Finite polynomial-in-nome coefficients with their ACTUAL original groups. -/
def nomeHeatPolynomial (tail : Nat) (p : RatPoly) : List (Poly × RatPoly) :=
  (degrees tail p).map fun d =>
    (polynomialPower coordinate (d*(d+2)), group tail p d)

/-- Evaluate the explicit nome coefficient polynomials, keeping spectators. -/
def finiteNomeFlow (tail : Nat) (p : RatPoly) (w : Q') : RatPoly :=
  polySum ((nomeHeatPolynomial tail p).map fun row =>
    polySmul (eval row.1 w) row.2)

/-- Literal formal differentiation of the finite nome coefficients. -/
def formalNomeDerivative (tail : Nat) (p : RatPoly) (w : Q') : RatPoly :=
  polySum ((nomeHeatPolynomial tail p).map fun row =>
    polySmul (eval (pderiv row.1) w) row.2)

private theorem coordinate_eval (w : Q') : eval coordinate w ≈ w :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => w)

private theorem nome_power_eval (w : Q') : ∀ k : Nat,
    eval (polynomialPower coordinate k) w ≈ RGTransport.qpow w k
  | 0 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ 0 (Q'.mul_zero_eqv w)) (q_add_zero_eqv 1)
  | k+1 => Q'.eqv_trans _ _ _ (eval_pmul coordinate (polynomialPower coordinate k) w)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ w _ (coordinate_eval w))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left w _ _ (nome_power_eval w k))
          (Q'.mul_comm_eqv w (RGTransport.qpow w k))))

private theorem coordinate_power_derivative (k : Nat) :
    CoeffEqv (pderiv (polynomialPower coordinate (k+1)))
      (pscale (Q'.ofNat (k+1)) (polynomialPower coordinate k)) := by
  have hd : CoeffEqv (pderiv coordinate) [1] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv 1
    | succ i => exact Q'.eqv_refl 0
  exact (QPolyPositivePrimitive.power_derivative_succ coordinate k).trans
    (((hd.pmul (CoeffEqv.refl _)).trans (coeffEqv_pmul_one_left _)).pscale _)

/-- Formal polynomial power rule in cleared Euler form; no nome inverse,
including k=0 and w=0. -/
theorem nome_power_generator (w : Q') (k : Nat) :
    w * eval (pderiv (polynomialPower coordinate k)) w ≈
      Q'.ofNat k * RGTransport.qpow w k := by
  cases k with
  | zero =>
      exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv w)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ 0 1 Q'.ofNat_zero_eqv) (Q'.zero_mul_eqv 1)))
  | succ k =>
      have hd := Q'.eqv_trans _ _ _ (coefficient_eval (coordinate_power_derivative k) w)
        (Q'.eqv_trans _ _ _ (eval_pscale (Q'.ofNat (k+1)) _ w)
          (Q'.mul_eqv_congr_left (Q'.ofNat (k+1)) _ _ (nome_power_eval w k)))
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ hd)
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
          (fun | 0 => w | 1 => Q'.ofNat (k+1) | _ => RGTransport.qpow w k))

private theorem sum_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ d, RatPolyCoeffEqv (f d) (g d)) →
      RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | d::ds, h => (h d).add (sum_congr f g ds h)

/-- The finite coefficient representation is the literal original headMap
at every cutoff retaining its computed modes, under ALL surviving insertions. -/
theorem finiteNomeFlow_original_pin (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : inputCutoff tail p ≤ K) :
    HaarCarrierEqv (tail+1) (finiteNomeFlow tail p w) (headMap w K p) := by
  have he := sum_congr
    (fun d => polySmul (eval (polynomialPower coordinate (d*(d+2))) w) (group tail p d))
    (fun d => polySmul (RGTransport.qpow w (d*(d+2))) (group tail p d))
    (degrees tail p) (fun d => RatPolyCoeffEqv.smul_coefficient (nome_power_eval w _) _)
  simpa only [finiteNomeFlow, nomeHeatPolynomial, List.map_map, Function.comp_def]
    using (RatPolyCoeffEqv.haarCarrier he).trans (headMap_saturated tail w K p hp hK).symm

private theorem smul_sum (c : Q') (f : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySmul c (polySum (ids.map f)))
      (polySum (ids.map fun d => polySmul c (f d)))
  | [] => RatPolyCoeffEqv.refl _
  | d::ds => (RatPolyCoeffEqv.smul_add c _ _).trans
      ((RatPolyCoeffEqv.refl _).add (smul_sum c f ds))

private theorem casimir_nat (d : Nat) :
    Q'.ofNat (d*(d+2)) ≈ Q'.ofNat d * (Q'.ofNat d+2) :=
  Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d+2))
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))

private theorem minus_lap_term (tail : Nat) (p : RatPoly) (w : Q') (d : Nat) :
    HaarCarrierEqv (tail+1)
      (polyNeg (angularLaplacian
        (polySmul (eval (polynomialPower coordinate (d*(d+2))) w) (group tail p d))))
      (polySmul (Q'.ofNat (d*(d+2)) * RGTransport.qpow w (d*(d+2))) (group tail p d)) := by
  let e := eval (polynomialPower coordinate (d*(d+2))) w
  let c := Q'.ofNat d * (Q'.ofNat d+2)
  have heig := harmonic_angularLaplacian (Nat.zero_lt_succ tail) (group tail p d)
    (grouped_degree d _) (grouped_harmonic d _)
  have hs : (-1)*(e*(-c)) ≈ Q'.ofNat (d*(d+2))*RGTransport.qpow w (d*(d+2)) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.mul (.var 0) (.neg (.var 1))))
        (.mul (.var 1) (.var 0)) (by decide) (fun | 0 => e | _ => c))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e (Q'.eqv_symm (casimir_nat d)))
        (Q'.mul_eqv_congr_left _ _ _ (nome_power_eval w _)))
  exact (HaarCarrierEqv.neg
    ((RatPolyCoeffEqv.haarCarrier (angularLaplacian_smul e _)).trans
      (HaarCarrierEqv.smul e heig))).trans
    (RatPolyCoeffEqv.haarCarrier
      ((neg_smul _).trans
        (((RatPolyCoeffEqv.smul_assoc e (-c) _).smul (-1)).trans
          ((RatPolyCoeffEqv.smul_assoc (-1) (e*(-c)) _).trans
            (RatPolyCoeffEqv.smul_coefficient hs _)))))

private theorem negative_laplacian_sum (tail : Nat) (p : RatPoly) (w : Q') :
    ∀ ids : List Nat, HaarCarrierEqv (tail+1)
      (polyNeg (angularLaplacian (polySum (ids.map fun d =>
        polySmul (eval (polynomialPower coordinate (d*(d+2))) w) (group tail p d)))))
      (polySum (ids.map fun d =>
        polySmul (Q'.ofNat (d*(d+2))*RGTransport.qpow w (d*(d+2))) (group tail p d)))
  | [] => HaarCarrierEqv.refl _ _
  | d::ds => by
      have hc := coeffEvalExpr_eqv_of_normalize_eq
        (.neg (.add (.var 0) (.var 1))) (.add (.neg (.var 0)) (.neg (.var 1)))
        (by decide) (fun
          | 0 => angularLaplacian
              (polySmul (eval (polynomialPower coordinate (d*(d+2))) w) (group tail p d))
          | _ => angularLaplacian (polySum (ds.map fun j =>
              polySmul (eval (polynomialPower coordinate (j*(j+2))) w) (group tail p j))))
      exact (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.neg (angularLaplacian_add _ _)).trans hc)).trans
        (HaarCarrierEqv.add (minus_lap_term tail p w d)
          (negative_laplacian_sum tail p w ds))

private theorem laplacian_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularLaplacian p) (angularLaplacian q) :=
  six_carrier (fun _ _ hi hj =>
    angularDerivative_carrier hb hi hj (angularDerivative_carrier hb hi hj h))

/-- Formal nome differentiation generates the ACTUAL original saturated heat
map. Full spectators and all Haar insertions survive; no nome division. -/
theorem headMap_formal_nome_generator (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : inputCutoff tail p ≤ K) :
    HaarCarrierEqv (tail+1) (polySmul w (formalNomeDerivative tail p w))
      (polyNeg (angularLaplacian (headMap w K p))) := by
  have hd : RatPolyCoeffEqv
      (polySmul w (polySum ((degrees tail p).map fun d => polySmul
        (eval (pderiv (polynomialPower coordinate (d*(d+2)))) w) (group tail p d))))
      (polySum ((degrees tail p).map fun d => polySmul
        (Q'.ofNat (d*(d+2))*RGTransport.qpow w (d*(d+2))) (group tail p d))) :=
    (smul_sum w (fun d => polySmul
    (eval (pderiv (polynomialPower coordinate (d*(d+2)))) w) (group tail p d))
    (degrees tail p)).trans
      (sum_congr _ _ (degrees tail p) (fun d =>
        (RatPolyCoeffEqv.smul_assoc _ _ _).trans
          (RatPolyCoeffEqv.smul_coefficient (nome_power_generator w (d*(d+2))) _)))
  have hflow : HaarCarrierEqv (tail+1)
      (polySmul w (formalNomeDerivative tail p w))
      (polyNeg (angularLaplacian (finiteNomeFlow tail p w))) := by
    simpa only [formalNomeDerivative, finiteNomeFlow, nomeHeatPolynomial,
      List.map_map, Function.comp_def] using
      (RatPolyCoeffEqv.haarCarrier hd).trans
        (negative_laplacian_sum tail p w (degrees tail p)).symm
  exact hflow.trans (HaarCarrierEqv.neg
    (laplacian_carrier (Nat.zero_lt_succ tail)
      (finiteNomeFlow_original_pin tail w K p hp hK)))

end YMGap.Continuum.SU2QuaternionHeadHeatGenerator

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.nomeHeatPolynomial
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.finiteNomeFlow
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.formalNomeDerivative
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.nome_power_generator
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.finiteNomeFlow_original_pin
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGenerator.headMap_formal_nome_generator
