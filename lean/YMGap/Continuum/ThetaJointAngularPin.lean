/-
# Actual finite angular pin for the signed joint theta polynomial

The literal polynomial on the original signed box is coefficient-pinned to
the square of the original bare prefix.  Its actual angular operator is then
transported by formal polynomial differentiation and the product rule.  This
is a finite algebraic identity; no frequency-moment estimate is included.
-/

import YMGap.Continuum.ThetaJointValuePin
import YMGap.Continuum.FiniteJacobiAngularComparison
import YMGap.Continuum.ChebyshevFormalJets
import YMGap.Constructive.QPolyCoefficientEvaluation
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaJointAngularPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaJointValuePin
open YMGap.Continuum.ChebyshevFormalJets
open YMGap.Continuum.FiniteJacobiAngularComparison
open YMGap.Continuum.FiniteJacobiSeriesComparison (bareTheta)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_mul_eqv)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_map)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a+c ≈ b+d := Q'.add_eqv_congr' h g

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

/-- Right-associated sum of coefficient polynomials. -/
def polySum : List Poly → Poly
  | [] => []
  | p::ps => padd p (polySum ps)

/-- Original joint coefficient cell as an actual x-polynomial. -/
def jointCellPolynomial (w : Q') (z : SignedPair) : Poly :=
  pscale (w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs))
    (Tpoly (z.1+z.2).natAbs)

/-- Literal polynomial for the joint theta sum on the original signed box. -/
def jointPolynomial (w : Q') (N : Nat) : Poly :=
  polySum ((boxIndices N).map (jointCellPolynomial w))

/-- Literal coefficient polynomial of the original symmetric bare prefix. -/
def barePolynomial (w : Q') (N : Nat) : Poly :=
  seriesPoly (fun j => w^(j*j)) N

private theorem eval_polySum (ps : List Poly) (x : Q') :
    eval (polySum ps) x ≈ listQSum (fun p => eval p x) ps := by
  induction ps with
  | nil => exact Q'.eqv_refl 0
  | cons p ps ih =>
      change eval (padd p (polySum ps)) x ≈ eval p x + listQSum (fun q => eval q x) ps
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
        (add_congr (Q'.eqv_refl _) ih)

private theorem listQSum_map' {A B : Type} (f : A → B) (g : B → Q') :
    ∀ xs, listQSum g (xs.map f) ≈ listQSum (fun a => g (f a)) xs
  | [] => Q'.eqv_refl 0
  | a::xs => by
      change g (f a) + listQSum g (xs.map f) ≈
        g (f a) + listQSum (fun a => g (f a)) xs
      exact Q'.add_eqv_congr_left _ _ _ (listQSum_map' f g xs)

private theorem eval_jointPolynomial (w x : Q') (N : Nat) :
    eval (jointPolynomial w N) x ≈
      listQSum (fun z : SignedPair =>
        w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs) *
          Cheb.T (z.1+z.2).natAbs x) (boxIndices N) := by
  unfold jointPolynomial
  exact Q'.eqv_trans _ _ _ (eval_polySum _ x)
    (Q'.eqv_trans _ _ _ (listQSum_map' _ _ _)
      (listQSum_congr (fun z => Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
        (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly _ x))) _))

private theorem eval_barePolynomial (w x : Q') (N : Nat) :
    eval (barePolynomial w N) x ≈ bareTheta w x N := by
  unfold barePolynomial
  exact eval_seriesPoly _ x N

private theorem eval_derivative_product (p q : Poly) (x : Q') :
    eval (pderiv (pmul p q)) x ≈
      eval (pderiv p) x * eval q x + eval p x * eval (pderiv q) x := by
  exact Q'.eqv_trans _ _ _
    (coefficient_eval (pderiv_pmul p q) x)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_pmul _ _ x) (eval_pmul _ _ x)))

/-- The actual joint polynomial is coefficient-pinned to the square of the
original bare prefix, using the signed-box endpoint value identity. -/
theorem joint_coeff_pin (w : Q') (N : Nat) :
    CoeffEqv (jointPolynomial w N) (pmul (barePolynomial w N) (barePolynomial w N)) := by
  apply coefficients_of_eval_eqv
  intro x
  have hj := eval_jointPolynomial w x N
  have hv := theta_box_endpoint_value_pin w x N
  have ht : listQSum (fun z : SignedPair =>
      w^(z.1.natAbs*z.1.natAbs + z.2.natAbs*z.2.natAbs) *
        Cheb.T (z.1+z.2).natAbs x) (boxIndices N) ≈
      bareTheta w x N * bareTheta w x N := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_congr
      (fun z => cell_endpoint_pin w x z) _)) hv
  exact Q'.eqv_trans _ _ _ hj (Q'.eqv_trans _ _ _ ht
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
      (mul_congr (eval_barePolynomial w x N) (eval_barePolynomial w x N)))))

/-- Formal angular product rule, stated at a rational point. -/
theorem angular_square_rule (p : Poly) (x : Q') :
    angularEval (pmul p p) x ≈
      2 * (eval p x * angularEval p x) +
        2 * ((1 + -(x*x)) * (eval (pderiv p) x * eval (pderiv p) x)) := by
  let a := pmul (pderiv p) p
  let b := pmul p (pderiv p)
  have h1 := Q'.eqv_trans _ _ _
    (coefficient_eval (pderiv_pmul p p) x)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_pmul _ _ x) (eval_pmul _ _ x)))
  have h2coeff : CoeffEqv (pderiv (pderiv (pmul p p))) (padd (pderiv a) (pderiv b)) :=
    ((pderiv_pmul p p).pderiv).trans (pderiv_padd a b)
  have h2 := Q'.eqv_trans _ _ _ (coefficient_eval h2coeff x)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_derivative_product (pderiv p) p x)
        (eval_derivative_product p (pderiv p) x)))
  -- The finite product-rule expansion is normalized only after all formal
  -- derivative transports have been made explicit above.
  unfold angularEval
  let sx : YMGap.Continuum.RingNormaliser.PolyExpr :=
    .add (.const 1) (.neg (.mul (.var 0) (.var 0)))
  exact Q'.eqv_trans _ _ _
    (add_congr (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ h1)))
    (poly_identity_of_normal_eq
      (.add
        (.mul sx
          (.add (.add (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 2)))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 1) (.var 3)))))
        (.neg (.mul (.var 0) (.add (.mul (.var 2) (.var 1)) (.mul (.var 1) (.var 2))))))
      (.add
        (.mul (.const 2) (.mul (.var 1)
          (.add (.mul sx (.var 3)) (.neg (.mul (.var 0) (.var 2))))))
        (.mul (.const 2) (.mul sx (.mul (.var 2) (.var 2)))))
      (by decide) (fun
        | 0 => x
        | 1 => eval p x
        | 2 => eval (pderiv p) x
        | _ => eval (pderiv (pderiv p)) x))

/-- The actual angular jet of the joint polynomial is the product-rule jet
of the actual bare-prefix square. -/
theorem joint_angular_pin (w x : Q') (N : Nat) :
    angularEval (jointPolynomial w N) x ≈
      2 * (eval (barePolynomial w N) x * angularEval (barePolynomial w N) x) +
        2 * ((1 + -(x*x)) *
          (eval (pderiv (barePolynomial w N)) x * eval (pderiv (barePolynomial w N)) x)) := by
  have h := joint_coeff_pin w N
  have hjet : CoeffEqv (pderiv (pderiv (jointPolynomial w N)))
      (pderiv (pderiv (pmul (barePolynomial w N) (barePolynomial w N)))) := h.pderiv.pderiv
  have hfirst : CoeffEqv (pderiv (jointPolynomial w N))
      (pderiv (pmul (barePolynomial w N) (barePolynomial w N))) := h.pderiv
  have hang : angularEval (jointPolynomial w N) x ≈
      angularEval (pmul (barePolynomial w N) (barePolynomial w N)) x := by
    unfold angularEval
    exact add_congr
      (Q'.mul_eqv_congr_left _ _ _ (coefficient_eval hjet x))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (coefficient_eval hfirst x)))
  exact Q'.eqv_trans _ _ _ hang (angular_square_rule (barePolynomial w N) x)

/-- Literal plus-frequency-square coefficient; no positivity is asserted. -/
def plusFrequencyCell (w x : Q') (z : SignedPair) : Q' :=
  Q'.ofNat ((z.1+z.2).natAbs*(z.1+z.2).natAbs) *
    w^(z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs) *
      Cheb.T (z.1+z.2).natAbs x

private theorem jointCell_angular_pin (w x : Q') (z : SignedPair) :
    angularEval (jointCellPolynomial w z) x ≈ -(plusFrequencyCell w x z) := by
  let a := (z.1+z.2).natAbs
  let c := w^(z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)
  have hmode : angularEval (Tpoly a) x ≈
      -(Q'.ofNat (a*a)*Cheb.T a x) :=
    Q'.eqv_trans _ _ _ (formal_angular_ode a x)
      (Q'.neg_eqv_congr _ _ (mul_congr
        (Q'.eqv_symm (ofNat_mul_eqv a a)) (eval_Tpoly a x)))
  exact Q'.eqv_trans _ _ _ (angular_scale c (Tpoly a) x)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ hmode)
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.neg (.mul (.var 1) (.var 2))))
        (.neg (.mul (.mul (.var 1) (.var 0)) (.var 2)))
        (by decide) (fun | 0 => c | 1 => Q'.ofNat (a*a) | _ => Cheb.T a x)))

private theorem angular_joint_sum (w x : Q') : ∀ zs : List SignedPair,
    angularEval (polySum (zs.map (jointCellPolynomial w))) x ≈
      -(listQSum (plusFrequencyCell w x) zs)
  | [] => poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.const 0))
        (.neg (.mul (.var 0) (.const 0)))) (.neg (.const 0))
      (by decide) (fun _ => x)
  | z::zs => Q'.eqv_trans _ _ _ (angular_add _ _ x)
      (Q'.eqv_trans _ _ _
        (add_congr (jointCell_angular_pin w x z) (angular_joint_sum w x zs))
        (poly_identity_of_normal_eq
          (.add (.neg (.var 0)) (.neg (.var 1)))
          (.neg (.add (.var 0) (.var 1))) (by decide)
          (fun | 0 => plusFrequencyCell w x z | _ => listQSum (plusFrequencyCell w x) zs)))

/-- Actual angular jet equals the negative literal plus-frequency-square
box sum, including N=0. This is finite sum transport, not differentiation
of a value limit. -/
theorem joint_angular_frequency_pin (w x : Q') (N : Nat) :
    angularEval (jointPolynomial w N) x ≈
      -(listQSum (plusFrequencyCell w x) (boxIndices N)) :=
  angular_joint_sum w x (boxIndices N)

end YMGap.Continuum.ThetaJointAngularPin

#print axioms YMGap.Continuum.ThetaJointAngularPin.jointPolynomial
#print axioms YMGap.Continuum.ThetaJointAngularPin.barePolynomial
#print axioms YMGap.Continuum.ThetaJointAngularPin.joint_coeff_pin
#print axioms YMGap.Continuum.ThetaJointAngularPin.angular_square_rule
#print axioms YMGap.Continuum.ThetaJointAngularPin.joint_angular_pin
#print axioms YMGap.Continuum.ThetaJointAngularPin.plusFrequencyCell
#print axioms YMGap.Continuum.ThetaJointAngularPin.joint_angular_frequency_pin
