/-
# A finite, uniform product defect for the ORIGINAL regularized log polynomials

For p_N(t)=sum_{k=1}^N t*(1-t)^k/k and a,b in [0,1],
  0 <= b*p_N(a)+a*p_N(b)-p_N(a*b) <= 1/(N+1).
The proof constructs finite coefficient primitives. It uses no analytic
logarithm addition law, differentiation under a limit, or positive lower
bound on a or b. Both endpoints and N=0 are retained. The arbitrary-rational
defect/primitive identities are also exposed for the separate scalar-series
identification; no operator, entropy or Yang--Mills estimate is asserted here.
-/

import YMGap.Continuum.RegularizedLogPolynomial
import YMGap.Constructive.QPolyFiniteLogDerivative
import YMGap.Constructive.QPolyFinitePowerDifference
import YMGap.Constructive.QPolyComplementCancellation
import YMGap.Constructive.QPolyCoefficientEvaluation

namespace YMGap.Constructive.Q'.eqv

private theorem trans {a b c : Q'} (h : a.eqv b) (k : b.eqv c) : a.eqv c :=
  Q'.eqv_trans _ _ _ h k

private theorem symm {a b : Q'} (h : a.eqv b) : b.eqv a := Q'.eqv_symm h

end YMGap.Constructive.Q'.eqv

namespace YMGap.Continuum.RegularizedLogPolynomialProductDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower complement coordinate)
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFiniteLogDerivative
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Constructive.QPolyComplementCancellation
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  q_mul_congr h k

private theorem sc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  Q'.add_eqv_congr' h (Q'.neg_eqv_congr _ _ k)

private theorem sub_le_left (a b : Q') (hb : (0 : Q') ≤ b) : a-b ≤ a :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv
    (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
      (by decide) (fun | 0 => a | _ => b))))

private theorem sub_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (psub p q) (psub p' q') := hp.padd hq.pneg

private theorem pderiv_sub (p q : Poly) :
    CoeffEqv (pderiv (psub p q)) (psub (pderiv p) (pderiv q)) :=
  (pderiv_padd _ _).trans ((CoeffEqv.refl _).padd (pderiv_pscale (-1) q))

private theorem mul_sub (p q r : Poly) :
    CoeffEqv (pmul p (psub q r)) (psub (pmul p q) (pmul p r)) :=
  (coeffEqv_pmul_padd_right _ _ _).trans
    ((CoeffEqv.refl _).padd (coeffEqv_pmul_pscale (-1) p r))

private theorem mul_constant (c : Q') (p : Poly) :
    CoeffEqv (pmul [c] p) (pscale c p) := by
  intro i
  exact (coeff_pmul [c] p i).trans
    ((mulCoeff_singleton c p i).trans (coeff_pscale c p i).symm)

private theorem constant_eval (c x : Q') : eval [c] x ≈ c :=
  (Q'.add_eqv_congr_left c _ _ (q_mul_zero x)).trans (q_add_zero_eqv c)

private theorem affine_eval (c d x : Q') : eval [c,d] x ≈ c+d*x :=
  (Q'.add_eqv_congr_left c _ _ (Q'.mul_eqv_congr_left x _ _ (constant_eval d x))).trans
    (Q'.add_eqv_congr_left c _ _ (Q'.mul_comm_eqv x d))

private theorem affine_derivative (c d : Q') : CoeffEqv (pderiv [c,d]) [d] := by
  intro i
  cases i with
  | zero => exact Q'.one_mul_eqv d
  | succ i => exact Q'.eqv_refl _

private theorem affine_complement (a : Q') :
    CoeffEqv (psub [1] [1-a,a]) (pscale a complement) := by
  intro i
  cases i with
  | zero =>
      change (1 + (-1)*(1-a)) ≈ a*1
      exact poly_identity_of_normal_eq
        (.add (.const 1) (.mul (.const (-1)) (.add (.const 1) (.neg (.var 0)))))
        (.mul (.var 0) (.const 1)) (by decide) (fun _ => a)
  | succ i =>
      cases i with
      | zero => exact Q'.mul_comm_eqv (-1) a
      | succ i => exact Q'.eqv_refl _

private theorem affine_minus_coordinate (a : Q') :
    CoeffEqv (psub [1-a,a] coordinate) (pscale (1-a) complement) := by
  intro i
  cases i with
  | zero =>
      change ((1-a)+(-1)*0) ≈ (1-a)*1
      exact (Q'.add_eqv_congr_left _ _ _ (q_mul_zero _)).trans
        ((q_add_zero_eqv _).trans (Q'.mul_one_eqv _).symm)
  | succ i =>
      cases i with
      | zero =>
          change (a+(-1)*1) ≈ (1-a)*(-1)
          exact poly_identity_of_normal_eq
            (.add (.var 0) (.mul (.const (-1)) (.const 1)))
            (.mul (.add (.const 1) (.neg (.var 0))) (.const (-1)))
            (by decide) (fun _ => a)
      | succ i => exact Q'.eqv_refl _

private theorem coordinate_complement : CoeffEqv (psub [1] coordinate) complement := by
  intro i
  cases i with
  | zero => decide
  | succ i => cases i with
    | zero => decide
    | succ i => exact Q'.eqv_refl _

private theorem subtract_complements (p q : Poly) :
    CoeffEqv (psub (psub [1] p) (psub [1] q)) (psub q p) := by
  intro i
  have hs (u v : Poly) : coeff (psub u v) i ≈ coeff u i - coeff v i :=
    (coeff_psub u v i).trans (Q'.add_eqv_congr_left _ _ _
      ((Q'.neg_mul_eqv 1 _).trans (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
  exact (hs _ _).trans ((sc (hs _ _) (hs _ _)).trans
    ((poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 0) (.neg (.var 2)))))
      (.add (.var 2) (.neg (.var 1))) (by decide)
      (fun | 0 => coeff [1] i | 1 => coeff p i | _ => coeff q i)).trans (hs _ _).symm))

/-- Actual finite polynomial with variable h:
ell_N(1-a)+ell_N(h)-ell_N(1-a+a*h), ell_N(z)=sum_{k=1}^N z^k/k. -/
def defectPolynomial (a : Q') (N : Nat) : Poly :=
  padd (finiteLog [1-a] N)
    (psub (finiteLog coordinate N) (finiteLog [1-a,a] N))

private theorem constant_log_derivative (c : Q') (N : Nat) :
    CoeffEqv (pderiv (finiteLog [c] N)) [] :=
  (finiteLog_derivative [c] N).trans (CoeffEqv.refl _)

private theorem defect_derivative_geometric (a : Q') (N : Nat) :
    CoeffEqv (pderiv (defectPolynomial a N))
      (psub (geometricPolynomial coordinate N)
        (pscale a (geometricPolynomial [1-a,a] N))) := by
  have ht := (finiteLog_derivative coordinate N).trans
    (((affine_derivative 0 1).pmul (CoeffEqv.refl _)).trans
      (coeffEqv_pmul_one_left _))
  have hv := (finiteLog_derivative [1-a,a] N).trans
    (((affine_derivative (1-a) a).pmul (CoeffEqv.refl _)).trans (mul_constant a _))
  exact (pderiv_padd _ _).trans
    ((constant_log_derivative (1-a) N).padd
      ((pderiv_sub _ _).trans (sub_congr ht hv)))

/-- Cleared finite geometric cancellation, valid for arbitrary rational a. -/
theorem defect_cleared_derivative (a : Q') (N : Nat) :
    CoeffEqv (pmul complement (pderiv (defectPolynomial a N)))
      (psub (polynomialPower [1-a,a] N) (polynomialPower coordinate N)) := by
  have ht : CoeffEqv (pmul complement (geometricPolynomial coordinate N))
      (psub [1] (polynomialPower coordinate N)) :=
    ((coordinate_complement.symm).pmul (CoeffEqv.refl _)).trans (geometric_telescope coordinate N)
  have hv : CoeffEqv (pmul complement (pscale a (geometricPolynomial [1-a,a] N)))
      (psub [1] (polynomialPower [1-a,a] N)) :=
    (coeffEqv_pmul_pscale a _ _).trans
      ((coeffEqv_pscale_pmul a _ _).symm.trans
        (((affine_complement a).symm.pmul (CoeffEqv.refl _)).trans
          (geometric_telescope [1-a,a] N)))
  exact ((CoeffEqv.refl complement).pmul (defect_derivative_geometric a N)).trans
    ((mul_sub _ _ _).trans ((sub_congr ht hv).trans (subtract_complements _ _)))

/-- The actual derivative is an explicit mixed-power polynomial, with no
interval guard. This identity is also available at negative evaluation points. -/
theorem defect_derivative (a : Q') (N : Nat) :
    CoeffEqv (pderiv (defectPolynomial a N))
      (pscale (1-a) (powerDifferenceRow [1-a,a] coordinate N)) := by
  have hf : CoeffEqv
      (pmul complement (pscale (1-a) (powerDifferenceRow [1-a,a] coordinate N)))
      (psub (polynomialPower [1-a,a] N) (polynomialPower coordinate N)) :=
    (coeffEqv_pmul_pscale _ _ _).trans
      ((coeffEqv_pscale_pmul _ _ _).symm.trans
        (((affine_minus_coordinate a).symm.pmul (CoeffEqv.refl _)).trans
          (powerDifference_telescope [1-a,a] coordinate N)))
  exact complement_mul_injective ((defect_cleared_derivative a N).trans hf.symm)

private theorem finiteLog_eval_congr {p q : Poly} {x y : Q'}
    (h : eval p x ≈ eval q y) : ∀ N,
    eval (finiteLog p N) x ≈ eval (finiteLog q N) y
  | 0 => Q'.eqv_refl _
  | N+1 => (eval_padd _ _ _).trans
      ((Q'.add_eqv_congr' (finiteLog_eval_congr h N)
        ((eval_pscale _ _ _).trans
          ((Q'.mul_eqv_congr_left _ _ _
            ((polynomialPower_eval p _ x).trans
              ((BernsteinSequenceWrap.pow_eqv_congr h _).trans
                (polynomialPower_eval q _ y).symm))).trans
            (eval_pscale _ _ _).symm))).trans (eval_padd _ _ _).symm)

private theorem finiteLog_zero (p : Poly) (x : Q') (h : eval p x ≈ 0) : ∀ N,
    eval (finiteLog p N) x ≈ 0
  | 0 => Q'.eqv_refl _
  | N+1 => by
      have hp : eval (polynomialPower p (N+1)) x ≈ 0 :=
        (eval_pmul _ _ _).trans ((mc h (Q'.eqv_refl _)).trans (q_zero_mul _))
      exact (eval_padd _ _ _).trans
        ((Q'.add_eqv_congr' (finiteLog_zero p x h N)
          ((eval_pscale _ _ _).trans ((mc (Q'.eqv_refl _) hp).trans (q_mul_zero _)))).trans
            (q_add_zero_eqv _))

/-- Exact zero initial value, for every rational a and every finite cutoff. -/
theorem defect_zero (a : Q') (N : Nat) : eval (defectPolynomial a N) 0 ≈ 0 := by
  have ht : eval coordinate 0 ≈ 0 := by decide
  have hv : eval [1-a,a] 0 ≈ eval [1-a] 0 :=
    (affine_eval _ _ _).trans
      ((Q'.add_eqv_congr_left _ _ _ (q_mul_zero a)).trans
        ((q_add_zero_eqv _).trans (constant_eval _ _).symm))
  exact (eval_padd _ _ _).trans
    ((Q'.add_eqv_congr' (Q'.eqv_refl _)
      ((eval_psub _ _ _).trans (sc (finiteLog_zero coordinate 0 ht N)
        (finiteLog_eval_congr hv N)))).trans
      (poly_identity_of_normal_eq (.add (.var 0) (.add (.const 0) (.neg (.var 0))))
        (.const 0) (by decide) (fun _ => eval (finiteLog [1-a] N) 0)))

/-- Computed reciprocal coefficients; no coefficient or convergence witness
is extracted from a proposition. -/
def reciprocalCoefficients : Nat → Poly → Poly
  | _, [] => []
  | k, c::p => (Q'.invSucc k*c)::reciprocalCoefficients (k+1) p

/-- The literal zero-initial finite primitive. -/
def primitive (p : Poly) : Poly := 0::reciprocalCoefficients 0 p

private theorem scaled_reciprocals : ∀ (k : Nat) (p : Poly),
    CoeffEqv (scaleFrom (k+1) (reciprocalCoefficients k p)) p
  | _, [] => CoeffEqv.refl _
  | k, c::p => by
      intro i
      cases i with
      | zero =>
          exact (Q'.mul_assoc_eqv _ _ _).symm.trans
            ((Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_succ_mul_invSucc k)).trans
              (Q'.one_mul_eqv c))
      | succ i => exact scaled_reciprocals (k+1) p i

theorem primitive_derivative (p : Poly) : CoeffEqv (pderiv (primitive p)) p :=
  scaled_reciprocals 0 p

theorem primitive_zero (p : Poly) : eval (primitive p) 0 ≈ 0 :=
  (Q'.add_eqv_congr_left 0 _ _ (q_zero_mul _)).trans (q_add_zero_eqv 0)

private theorem primitive_congr {p q : Poly} (h : CoeffEqv p q) :
    CoeffEqv (primitive p) (primitive q) :=
  QPolyPositivePrimitive.derivative_initial_unique _ _
    ((primitive_derivative p).trans (h.trans (primitive_derivative q).symm))
    ((primitive_zero p).trans (primitive_zero q).symm)

/-- The positive-derivative primitive is the ORIGINAL finite defect, not a
replacement chosen for its sign. -/
theorem defect_primitive (a : Q') (N : Nat) :
    CoeffEqv (primitive (pscale (1-a) (powerDifferenceRow [1-a,a] coordinate N)))
      (defectPolynomial a N) :=
  QPolyPositivePrimitive.derivative_initial_unique _ _
    ((primitive_derivative _).trans (defect_derivative a N).symm)
    ((primitive_zero _).trans (defect_zero a N).symm)

private def NonnegativeCoefficients (p : Poly) : Prop := ∀ c, c ∈ p → (0 : Q') ≤ c

private theorem nn_nil : NonnegativeCoefficients [] := fun _ h => nomatch h

private theorem nn_cons {c : Q'} {p : Poly} (hc : (0 : Q') ≤ c)
    (hp : NonnegativeCoefficients p) : NonnegativeCoefficients (c::p) := by
  intro d hd
  rcases List.mem_cons.mp hd with h | h
  · subst d; exact hc
  · exact hp d h

private theorem nn_add : ∀ {p q : Poly}, NonnegativeCoefficients p →
    NonnegativeCoefficients q → NonnegativeCoefficients (padd p q)
  | [], _, _, hq => hq
  | _::_, [], hp, _ => hp
  | c::_p, d::_q, hp, hq => nn_cons
      (Q'.zero_le_add _ _ (hp _ List.mem_cons_self) (hq _ List.mem_cons_self))
      (nn_add (fun _ h => hp _ (List.mem_cons_of_mem c h))
        (fun _ h => hq _ (List.mem_cons_of_mem d h)))

private theorem nn_scale (c : Q') (hc : (0 : Q') ≤ c) : ∀ {p : Poly},
    NonnegativeCoefficients p → NonnegativeCoefficients (pscale c p)
  | [], _ => nn_nil
  | d::_p, hp => nn_cons (Q'.mul_nonneg _ _ hc (hp _ List.mem_cons_self))
      (nn_scale c hc (fun _ h => hp _ (List.mem_cons_of_mem d h)))

private theorem nn_mul : ∀ {p q : Poly}, NonnegativeCoefficients p →
    NonnegativeCoefficients q → NonnegativeCoefficients (pmul p q)
  | [], _, _, _ => nn_nil
  | c::_p, _q, hp, hq => nn_add (nn_scale c (hp _ List.mem_cons_self) hq)
      (nn_cons (Q'.le_refl' 0) (nn_mul (fun _ h => hp _ (List.mem_cons_of_mem c h)) hq))

private theorem nn_power {p : Poly} (hp : NonnegativeCoefficients p) : ∀ n,
    NonnegativeCoefficients (polynomialPower p n)
  | 0 => nn_cons (by decide) nn_nil
  | n+1 => nn_mul hp (nn_power hp n)

private theorem nn_difference {p q : Poly} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : ∀ n,
    NonnegativeCoefficients (powerDifferenceRow p q n)
  | 0 => nn_nil
  | n+1 => nn_add (nn_mul hp (nn_difference hp hq n)) (nn_power hq n)

private theorem nn_reciprocals : ∀ k {p : Poly}, NonnegativeCoefficients p →
    NonnegativeCoefficients (reciprocalCoefficients k p)
  | _, [], _ => nn_nil
  | k, c::_p, hp => nn_cons
      (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg k) (hp _ List.mem_cons_self))
      (nn_reciprocals (k+1) (fun _ h => hp _ (List.mem_cons_of_mem c h)))

private theorem nn_primitive {p : Poly} (hp : NonnegativeCoefficients p) :
    NonnegativeCoefficients (primitive p) := nn_cons (Q'.le_refl' 0) (nn_reciprocals 0 hp)

private theorem nn_eval (x : Q') (hx : (0 : Q') ≤ x) : ∀ {p : Poly},
    NonnegativeCoefficients p → (0 : Q') ≤ eval p x
  | [], _ => Q'.le_refl' 0
  | c::_p, hp => Q'.zero_le_add _ _ (hp _ List.mem_cons_self)
      (Q'.mul_nonneg _ _ hx (nn_eval x hx (fun _ h => hp _ (List.mem_cons_of_mem c h))))

private theorem derivative_add_cancel (p q : Poly) :
    CoeffEqv (padd (padd (pneg p) q) p) q := by
  intro i
  exact (coeff_padd i _ _).trans
    ((q_add_congr ((coeff_padd i _ _).trans
      (q_add_congr (coeff_pneg_eqv _ _) (Q'.eqv_refl _))) (Q'.eqv_refl _)).trans
      (poly_identity_of_normal_eq
        (.add (.add (.neg (.var 0)) (.var 1)) (.var 0)) (.var 1)
        (by decide) (fun | 0 => coeff p i | _ => coeff q i)))

private theorem primitive_complement (p : Poly) :
    CoeffEqv (primitive (pmul complement p))
      (padd (pmul complement (primitive p)) (primitive (primitive p))) := by
  apply QPolyPositivePrimitive.derivative_initial_unique
  · have hd : CoeffEqv (pderiv (padd (pmul complement (primitive p))
        (primitive (primitive p)))) (pmul complement p) :=
      (pderiv_padd _ _).trans
        ((((pderiv_pmul _ _).trans
          ((((affine_derivative 1 (-1)).pmul (CoeffEqv.refl _)).trans (mul_constant (-1) _)).padd
            ((CoeffEqv.refl complement).pmul (primitive_derivative p)))).padd
          (primitive_derivative (primitive p))).trans (derivative_add_cancel _ _))
    exact (primitive_derivative _).trans hd.symm
  · exact (primitive_zero _).trans
      ((eval_padd _ _ _).trans ((Q'.add_eqv_congr'
        ((eval_pmul _ _ _).trans ((mc (Q'.eqv_refl _) (primitive_zero p)).trans (q_mul_zero _)))
        (primitive_zero _)).trans (q_add_zero_eqv _))).symm

private theorem primitive_sub (p q : Poly) :
    CoeffEqv (primitive (psub p q)) (psub (primitive p) (primitive q)) :=
  QPolyPositivePrimitive.derivative_initial_unique _ _
    ((primitive_derivative _).trans
      ((pderiv_sub _ _).trans (sub_congr (primitive_derivative p) (primitive_derivative q))).symm)
    ((primitive_zero _).trans
      ((eval_psub _ _ _).trans ((sc (primitive_zero p) (primitive_zero q)).trans (by decide))).symm)

private theorem primitive_affine_power (a : Q') (N : Nat) :
    CoeffEqv (pscale a (primitive (polynomialPower [1-a,a] N)))
      (pscale (Q'.invSucc N)
        (psub (polynomialPower [1-a,a] (N+1))
          [eval (polynomialPower [1-a,a] (N+1)) 0])) := by
  apply QPolyPositivePrimitive.derivative_initial_unique
  · have hv : CoeffEqv (pderiv (polynomialPower [1-a,a] (N+1)))
        (pscale (Q'.ofNat (N+1)*a) (polynomialPower [1-a,a] N)) :=
      (QPolyPositivePrimitive.power_derivative_succ _ _).trans
        (((((affine_derivative (1-a) a).pmul (CoeffEqv.refl _)).trans
          (mul_constant a _)).pscale _).trans (coeffEqv_pscale_comp _ _ _))
    have hs : Q'.invSucc N*(Q'.ofNat (N+1)*a) ≈ a :=
      (Q'.mul_assoc_eqv _ _ _).symm.trans
        ((Q'.mul_eqv_congr_right _ _ _
          ((Q'.mul_comm_eqv _ _).trans (Q'.ofNat_succ_mul_invSucc N))).trans (Q'.one_mul_eqv _))
    have hz (p : Poly) : CoeffEqv (psub p []) p := by
      intro i
      exact (coeff_padd i p []).trans (q_add_zero_eqv _)
    have hdconst : CoeffEqv
        (pderiv [eval (polynomialPower [1-a,a] (N+1)) 0]) [] := CoeffEqv.refl []
    have hr : CoeffEqv
        (pderiv (pscale (Q'.invSucc N)
          (psub (polynomialPower [1-a,a] (N+1))
            [eval (polynomialPower [1-a,a] (N+1)) 0])))
        (pscale (Q'.invSucc N)
          (pscale (Q'.ofNat (N+1)*a) (polynomialPower [1-a,a] N))) :=
      (pderiv_pscale _ _).trans
        ((((pderiv_sub _ _).trans (sub_congr hv hdconst)).trans (hz _)).pscale _)
    exact ((pderiv_pscale _ _).trans ((primitive_derivative _).pscale a)).trans
      (hr.trans ((coeffEqv_pscale_comp _ _ _).trans (coeffEqv_pscale_scalar hs _))).symm
  · have hl : eval (pscale a (primitive (polynomialPower [1-a,a] N))) 0 ≈ 0 :=
      (eval_pscale _ _ _).trans
        ((mc (Q'.eqv_refl _) (primitive_zero _)).trans (q_mul_zero _))
    have hr : eval (pscale (Q'.invSucc N)
        (psub (polynomialPower [1-a,a] (N+1))
          [eval (polynomialPower [1-a,a] (N+1)) 0])) 0 ≈ 0 :=
      (eval_pscale _ _ _).trans
        ((mc (Q'.eqv_refl _) ((eval_psub _ _ _).trans
          ((sc (Q'.eqv_refl _) (constant_eval _ _)).trans (Q'.add_neg_self_eqv _)))).trans
            (q_mul_zero _))
    exact hl.trans hr.symm

private theorem primitive_complement_bound (p : Poly) (hp : NonnegativeCoefficients p)
    (b : Q') (hb : b ≤ 1) :
    b*eval (primitive p) (1-b) ≤ eval (primitive (pmul complement p)) (1-b) := by
  have hx : (0 : Q') ≤ 1-b := Q'.sub_nonneg_of_le hb
  have hc : eval complement (1-b) ≈ b :=
    (affine_eval _ _ _).trans (poly_identity_of_normal_eq
      (.add (.const 1) (.mul (.const (-1)) (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => b))
  have he := (coefficient_eval (primitive_complement p) (1-b)).trans
    ((eval_padd _ _ _).trans ((Q'.add_eqv_congr'
      ((eval_pmul _ _ _).trans (mc hc (Q'.eqv_refl _))) (Q'.eqv_refl _))))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (nn_eval (1-b) hx (nn_primitive (nn_primitive hp))))
    (Q'.ge_of_eqv he)

private theorem defect_eval (a t : Q') (N : Nat) :
    a*(1-t)*eval (defectPolynomial a N) t ≈
      (1-t)*partialSum a N+a*partialSum (1-t) N-partialSum (a*(1-t)) N := by
  induction N with
  | zero =>
      change a*(1-t)*(0+(0-0)) ≈ (1-t)*0+a*0-0
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
          (.add (.const 0) (.add (.const 0) (.neg (.const 0)))))
        (.add (.add (.mul (.add (.const 1) (.neg (.var 1))) (.const 0))
          (.mul (.var 0) (.const 0))) (.neg (.const 0))) (by decide)
        (fun | 0 => a | _ => t)
  | succ N ih =>
      have termpin (p : Poly) : eval (finiteLog p (N+1)) t ≈
          eval (finiteLog p N) t+Q'.invSucc N*(eval p t)^(N+1) :=
        (eval_padd _ _ _).trans (q_add_congr (Q'.eqv_refl _)
          ((eval_pscale _ _ _).trans (Q'.mul_eqv_congr_left _ _ _ (polynomialPower_eval p _ t))))
      have ht : eval coordinate t ≈ t :=
        (affine_eval 0 1 t).trans ((q_zero_add_eqv _).trans (Q'.one_mul_eqv _))
      have hv : eval [1-a,a] t ≈ 1-a*(1-t) :=
        (affine_eval _ _ _).trans (poly_identity_of_normal_eq
          (.add (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 1)))
          (.add (.const 1) (.neg (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))))
          (by decide) (fun | 0 => a | _ => t))
      have hc := constant_eval (1-a) t
      have he := (eval_padd _ _ _).trans
        (q_add_congr (termpin [1-a]) ((eval_psub _ _ _).trans
          (sc (termpin coordinate) (termpin [1-a,a]))))
      have hbefore : eval (defectPolynomial a N) t ≈
          eval (finiteLog [1-a] N) t+
            (eval (finiteLog coordinate N) t-eval (finiteLog [1-a,a] N) t) :=
        (eval_padd _ _ t).trans
          (q_add_congr (Q'.eqv_refl _) (eval_psub _ _ t))
      have hstep : eval (defectPolynomial a (N+1)) t ≈
          eval (defectPolynomial a N) t+Q'.invSucc N*
            ((1-a)^(N+1)+t^(N+1)-(1-a*(1-t))^(N+1)) := by
        have h := he.trans (q_add_congr
          (q_add_congr (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (BernsteinSequenceWrap.pow_eqv_congr hc _)))
          (sc (q_add_congr (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (BernsteinSequenceWrap.pow_eqv_congr ht _)))
            (q_add_congr (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (BernsteinSequenceWrap.pow_eqv_congr hv _)))))
        exact h.trans ((poly_identity_of_normal_eq
          (.add (.add (.var 0) (.mul (.var 3) (.var 4)))
            (.add (.add (.var 1) (.mul (.var 3) (.var 5)))
              (.neg (.add (.var 2) (.mul (.var 3) (.var 6))))))
          (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.mul (.var 3) (.add (.add (.var 4) (.var 5)) (.neg (.var 6)))))
          (by decide) (fun | 0 => eval (finiteLog [1-a] N) t | 1 => eval (finiteLog coordinate N) t | 2 => eval (finiteLog [1-a,a] N) t | 3 => Q'.invSucc N | 4 => (1-a)^(N+1) | 5 => t^(N+1) | _ => (1-a*(1-t))^(N+1))).trans
              (q_add_congr hbefore.symm (Q'.eqv_refl _)))
      have hdouble : 1-(1-t) ≈ t := poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
        (.var 0) (by decide) (fun _ => t)
      have hend : (1-t)*partialSum a (N+1)+a*partialSum (1-t) (N+1)-
          partialSum (a*(1-t)) (N+1) ≈
          ((1-t)*partialSum a N+a*partialSum (1-t) N-partialSum (a*(1-t)) N)+
            (a*(1-t))*(Q'.invSucc N*((1-a)^(N+1)+t^(N+1)-(1-a*(1-t))^(N+1))) := by
        change (1-t)*(partialSum a N+RegularizedLogPolynomial.term a N)+
          a*(partialSum (1-t) N+RegularizedLogPolynomial.term (1-t) N)-
          (partialSum (a*(1-t)) N+RegularizedLogPolynomial.term (a*(1-t)) N) ≈ _
        have ht' := BernsteinSequenceWrap.pow_eqv_congr hdouble (N+1)
        refine (sc (q_add_congr (Q'.eqv_refl _)
          (mc (Q'.eqv_refl _) (q_add_congr (Q'.eqv_refl _)
            (mc (Q'.eqv_refl _) (mc (Q'.eqv_refl _) ht'))))) (Q'.eqv_refl _)).trans ?_
        exact poly_identity_of_normal_eq
          (.add (.add (.mul (.add (.const 1) (.neg (.var 1)))
            (.add (.var 2) (.mul (.var 5) (.mul (.var 0) (.var 6)))))
            (.mul (.var 0) (.add (.var 3) (.mul (.var 5)
              (.mul (.add (.const 1) (.neg (.var 1))) (.var 7))))))
            (.neg (.add (.var 4) (.mul (.var 5)
              (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))) (.var 8))))))
          (.add (.add (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
            (.mul (.var 0) (.var 3))) (.neg (.var 4)))
            (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
              (.mul (.var 5) (.add (.add (.var 6) (.var 7)) (.neg (.var 8))))))
          (by decide) (fun | 0 => a | 1 => t | 2 => partialSum a N | 3 => partialSum (1-t) N | 4 => partialSum (a*(1-t)) N | 5 => Q'.invSucc N | 6 => (1-a)^(N+1) | 7 => t^(N+1) | _ => (1-a*(1-t))^(N+1))
      exact (mc (Q'.eqv_refl _) hstep).trans
        ((Q'.mul_add_eqv _ _ _).trans ((q_add_congr ih (Q'.eqv_refl _)).trans hend.symm))

/-- The actual coefficient primitive evaluated at h=1-b gives precisely
the signed defect of the original regularized partial sums. -/
theorem defect_value (a b : Q') (N : Nat) :
    a*b*eval (defectPolynomial a N) (1-b) ≈
      b*partialSum a N+a*partialSum b N-partialSum (a*b) N := by
  have hb : 1-(1-b) ≈ b := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => b)
  have pc {x y : Q'} (h : x ≈ y) : ∀ n, partialSum x n ≈ partialSum y n := by
    intro n
    induction n with
    | zero => exact Q'.eqv_refl _
    | succ n ih => exact q_add_congr ih (mc (Q'.eqv_refl _)
        (mc h (BernsteinSequenceWrap.pow_eqv_congr (sc (Q'.eqv_refl 1) h) _)))
  exact (mc (mc (Q'.eqv_refl _) hb).symm (Q'.eqv_refl _)).trans
    ((defect_eval a (1-b) N).trans
      (sc (q_add_congr (mc hb (Q'.eqv_refl _)) (mc (Q'.eqv_refl _) (pc hb N)))
        (pc (mc (Q'.eqv_refl _) hb) N)))

/-- Uniform finite multiplication defect, including a=0, b=0 and N=0.
There is no lower-spectrum or analytic logarithm hypothesis. -/
theorem product_defect_bounds (a b : Q') (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1)
    (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1) (N : Nat) :
    (0 : Q') ≤ b*partialSum a N+a*partialSum b N-partialSum (a*b) N ∧
      b*partialSum a N+a*partialSum b N-partialSum (a*b) N ≤ Q'.invSucc N := by
  let G := pscale (1-a) (powerDifferenceRow [1-a,a] coordinate N)
  have hG : NonnegativeCoefficients G := nn_scale _ (Q'.sub_nonneg_of_le ha1)
    (nn_difference (nn_cons (Q'.sub_nonneg_of_le ha1) (nn_cons ha0 nn_nil))
      (nn_cons (Q'.le_refl' 0) (nn_cons (by decide) nn_nil)) N)
  have hx : (0 : Q') ≤ 1-b := Q'.sub_nonneg_of_le hb1
  have hp : eval (primitive G) (1-b) ≈ eval (defectPolynomial a N) (1-b) :=
    coefficient_eval (defect_primitive a N) (1-b)
  have hd := (mc (Q'.eqv_refl (a*b)) hp).trans (defect_value a b N)
  refine ⟨Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha0 hb0) (nn_eval _ hx (nn_primitive hG)))
    (Q'.le_of_eqv hd), ?_⟩
  have hc : CoeffEqv (pmul complement G)
      (psub (polynomialPower [1-a,a] N) (polynomialPower coordinate N)) :=
    ((CoeffEqv.refl complement).pmul (defect_derivative a N).symm).trans
      (defect_cleared_derivative a N)
  have he := (coefficient_eval (primitive_congr hc) (1-b)).trans
    ((coefficient_eval (primitive_sub _ _) (1-b)).trans (eval_psub _ _ _))
  have hsecond : (0 : Q') ≤ eval (primitive (polynomialPower coordinate N)) (1-b) :=
    nn_eval (1-b) hx
      (nn_primitive (nn_power (nn_cons (Q'.le_refl' 0) (nn_cons (by decide) nn_nil)) N))
  have hsmall : eval (primitive (pmul complement G)) (1-b) ≤
      eval (primitive (polynomialPower [1-a,a] N)) (1-b) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (sub_le_left _ _ hsecond)
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ a
    (Q'.le_trans' _ _ _ (primitive_complement_bound G hG b hb1) hsmall) ha0
  have hv : eval [1-a,a] (1-b) ≈ 1-a*b :=
    (affine_eval _ _ _).trans (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => a | _ => b))
  have hab0 := Q'.mul_nonneg _ _ ha0 hb0
  have hab1 : a*b ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ b ha1 hb0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv b)) hb1)
  have hv0 : (0 : Q') ≤ eval [1-a,a] (1-b) :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hab1) (Q'.ge_of_eqv hv)
  have hv1 : eval [1-a,a] (1-b) ≤ 1 := Q'.le_trans' _ _ _ (Q'.le_of_eqv hv)
    (sub_le_left _ _ hab0)
  have hpow : eval (polynomialPower [1-a,a] (N+1)) (1-b) ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomialPower_eval _ _ _))
      (HKPos.pow_le_one hv0 hv1 _)
  have hzero : (0 : Q') ≤ eval (polynomialPower [1-a,a] (N+1)) 0 :=
    nn_eval 0 (Q'.le_refl' 0)
      (nn_power (nn_cons (Q'.sub_nonneg_of_le ha1) (nn_cons ha0 nn_nil)) (N+1))
  have hdiff : eval (polynomialPower [1-a,a] (N+1)) (1-b)-
      eval (polynomialPower [1-a,a] (N+1)) 0 ≤ 1 :=
    Q'.le_trans' _ _ _ (sub_le_left _ _ hzero) hpow
  have hvalue := (eval_pscale a _ (1-b)).symm.trans
    ((coefficient_eval (primitive_affine_power a N) (1-b)).trans
      ((eval_pscale _ _ _).trans
        (mc (Q'.eqv_refl _) ((eval_psub _ _ _).trans
          (sc (Q'.eqv_refl _) (constant_eval _ _))))))
  have hlast := Q'.le_trans' _ _ _ (Q'.le_of_eqv hvalue)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hdiff (Q'.invSucc_nonneg N))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hd.symm)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ hfirst hlast))

end YMGap.Continuum.RegularizedLogPolynomialProductDefect

#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defectPolynomial
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defect_cleared_derivative
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defect_derivative
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defect_zero
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.reciprocalCoefficients
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.primitive
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.primitive_derivative
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.primitive_zero
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defect_primitive
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.defect_value
#print axioms YMGap.Continuum.RegularizedLogPolynomialProductDefect.product_defect_bounds
