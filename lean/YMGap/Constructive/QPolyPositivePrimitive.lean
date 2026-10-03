/-
Finite positive primitives of `(1-h)^a*h^b`, in the actual `QPoly` coefficient
carrier.  The recursion below is the positive integration-by-parts expansion

  I(0,b)   = h^(b+1)/(b+1),
  I(a+1,b) = (1-h)^(a+1)*h^(b+1)/(b+1)
             + (a+1)/(b+1)*I(a,b+1).

Unfolding it gives the finite sum in the original root/log sandwich note.
The derivative theorem is coefficientwise, not merely an evaluation identity.
No analytic integration, interval differentiation theorem, or operator lift is
used or claimed here.
-/

import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Constructive.QPolyPositivePrimitive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative

/-- Computed finite polynomial power; exponent zero is the constant one. -/
def polynomialPower (p : Poly) : Nat → Poly
  | 0 => [1]
  | n + 1 => pmul p (polynomialPower p n)

/-- The literal affine factor `1-h`. -/
def complement : Poly := [1, -1]

/-- The literal coordinate `h`. -/
def coordinate : Poly := [0, 1]

/-- An explicit finite positive primitive, recursive in the first exponent. -/
def primitive : Nat → Nat → Poly
  | 0, b => pscale (Q'.invSucc b) (polynomialPower coordinate (b + 1))
  | a + 1, b =>
      padd
        (pscale (Q'.invSucc b)
          (pmul (polynomialPower complement (a + 1))
            (polynomialPower coordinate (b + 1))))
        (pscale (Q'.ofNat (a + 1) * Q'.invSucc b)
          (primitive a (b + 1)))

private theorem mul_constant (k : Q') (p : Poly) :
    CoeffEqv (pmul [k] p) (pscale k p) := by
  intro i
  change (coeff (padd (pscale k p) [0]) i).eqv (coeff (pscale k p) i)
  have hz : (coeff [0] i).eqv 0 := by
    cases i <;> exact Q'.eqv_refl 0
  exact Q'.eqv_trans _ _ _ (coeff_padd i _ _)
    (Q'.eqv_trans _ _ _ (q_add_congr (Q'.eqv_refl _) hz)
      (q_add_zero_eqv _))

private theorem add_zero_right (p : Poly) : CoeffEqv (padd p []) p := by
  intro i
  exact Q'.eqv_trans _ _ _ (coeff_padd i p []) (q_add_zero_eqv _)

/-- Finite polynomial power rule, coefficientwise over the rational setoid. -/
theorem power_derivative_succ (p : Poly) (n : Nat) :
    CoeffEqv (pderiv (polynomialPower p (n + 1)))
      (pscale (Q'.ofNat (n + 1))
        (pmul (pderiv p) (polynomialPower p n))) := by
  induction n with
  | zero =>
      have hzero : CoeffEqv (pmul p (pderiv [1])) [] :=
        coeffEqv_pmul_comm p []
      exact (pderiv_pmul p [1]).trans
        ((CoeffEqv.padd (CoeffEqv.refl _) hzero).trans
          ((add_zero_right _).trans
            (coeffEqv_pscale_one _).symm))
  | succ n ih =>
      let v := pmul (pderiv p) (polynomialPower p (n + 1))
      have hreorder :
          CoeffEqv (pmul p (pmul (pderiv p) (polynomialPower p n))) v :=
        (coeffEqv_pmul_assoc p (pderiv p) (polynomialPower p n)).symm.trans
          (((coeffEqv_pmul_comm p (pderiv p)).pmul (CoeffEqv.refl _)).trans
            (coeffEqv_pmul_assoc (pderiv p) p (polynomialPower p n)))
      have hright :
          CoeffEqv (pmul p (pderiv (polynomialPower p (n + 1))))
            (pscale (Q'.ofNat (n + 1)) v) :=
        ((CoeffEqv.refl p).pmul ih).trans
          ((coeffEqv_pmul_pscale _ _ _).trans
            (hreorder.pscale (Q'.ofNat (n + 1))))
      have hscalar : (1 + Q'.ofNat (n + 1)).eqv (Q'.ofNat (n + 2)) :=
        Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
          (Q'.eqv_symm (Q'.ofNat_add_eqv (n + 1) 1))
      exact (pderiv_pmul p (polynomialPower p (n + 1))).trans
        ((CoeffEqv.padd (CoeffEqv.refl v) hright).trans
          ((CoeffEqv.padd (coeffEqv_pscale_one v).symm
              (CoeffEqv.refl _)).trans
            ((coeffEqv_padd_pscale _ _ v).trans
              (coeffEqv_pscale_scalar hscalar v))))

private theorem coordinate_derivative (n : Nat) :
    CoeffEqv (pderiv (polynomialPower coordinate (n + 1)))
      (pscale (Q'.ofNat (n + 1)) (polynomialPower coordinate n)) := by
  have hd : CoeffEqv (pderiv coordinate) [1] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv 1
    | succ i => exact Q'.eqv_refl 0
  exact (power_derivative_succ coordinate n).trans
    (((hd.pmul (CoeffEqv.refl _)).trans
      (coeffEqv_pmul_one_left _)).pscale _)

private theorem complement_derivative (n : Nat) :
    CoeffEqv (pderiv (polynomialPower complement (n + 1)))
      (pscale (-Q'.ofNat (n + 1)) (polynomialPower complement n)) := by
  have hd : CoeffEqv (pderiv complement) [-1] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv (-1)
    | succ i => exact Q'.eqv_refl 0
  have hs : (Q'.ofNat (n + 1) * (-1)).eqv (-Q'.ofNat (n + 1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ 1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv _))
  exact (power_derivative_succ complement n).trans
    ((((hd.pmul (CoeffEqv.refl _)).trans (mul_constant (-1) _)).pscale _).trans
      ((coeffEqv_pscale_comp _ _ _).trans
        (coeffEqv_pscale_scalar hs _)))

private theorem inverse_cancel (b : Nat) :
    (Q'.invSucc b * Q'.ofNat (b + 1)).eqv 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.ofNat_succ_mul_invSucc b)

private theorem cancellation (A inv B x y : Q')
    (hB : (inv * B).eqv 1) :
    (inv * ((-A) * x + B * y) + (A * inv) * x).eqv y := by
  have hn : (inv * ((-A) * x)).eqv (-((A * inv) * x)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x
          (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv inv A)
            (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv inv A))))
        (Q'.neg_mul_eqv _ x))
  have hy : (inv * (B * y)).eqv y :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y hB)
        (Q'.one_mul_eqv y))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv inv _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (q_add_congr hn hy)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ y)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv y _ _)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left y _ 0 (Q'.neg_add_self_eqv _))
      (q_add_zero_eqv y))

/-- The computed primitive has exactly the desired FORMAL derivative, at every
padded coefficient. -/
theorem primitive_derivative (a b : Nat) :
    CoeffEqv (pderiv (primitive a b))
      (pmul (polynomialPower complement a) (polynomialPower coordinate b)) := by
  induction a generalizing b with
  | zero =>
      exact (pderiv_pscale _ _).trans
        (((coordinate_derivative b).pscale _).trans
          ((coeffEqv_pscale_comp _ _ _).trans
            ((coeffEqv_pscale_scalar (inverse_cancel b) _).trans
              ((coeffEqv_pscale_one _).trans
                (coeffEqv_pmul_one_left _).symm))))
  | succ a ih =>
      let U := polynomialPower complement (a + 1)
      let H := polynomialPower coordinate (b + 1)
      let Q := pmul (polynomialPower complement a) H
      let P := pmul U (polynomialPower coordinate b)
      have ht : CoeffEqv (pderiv (pmul U H))
          (padd (pscale (-Q'.ofNat (a + 1)) Q)
            (pscale (Q'.ofNat (b + 1)) P)) :=
        (pderiv_pmul U H).trans
          (CoeffEqv.padd
            (((complement_derivative a).pmul (CoeffEqv.refl H)).trans
              (coeffEqv_pscale_pmul _ _ _))
            (((CoeffEqv.refl U).pmul (coordinate_derivative b)).trans
              (coeffEqv_pmul_pscale _ _ _)))
      have hd : CoeffEqv (pderiv (primitive (a + 1) b))
          (padd
            (pscale (Q'.invSucc b)
              (padd (pscale (-Q'.ofNat (a + 1)) Q)
                (pscale (Q'.ofNat (b + 1)) P)))
            (pscale (Q'.ofNat (a + 1) * Q'.invSucc b) Q)) :=
        (pderiv_padd _ _).trans
          (CoeffEqv.padd
            ((pderiv_pscale _ _).trans (ht.pscale _))
            ((pderiv_pscale _ _).trans ((ih (b + 1)).pscale _)))
      intro i
      refine Q'.eqv_trans _ _ _ (hd i) ?_
      refine Q'.eqv_trans _ _ _ (coeff_padd i _ _) ?_
      refine Q'.eqv_trans _ _ _
        (q_add_congr (coeff_pscale _ _ i) (coeff_pscale _ _ i)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (coeff_padd i _ _)
              (q_add_congr (coeff_pscale _ _ i) (coeff_pscale _ _ i))))) ?_
      exact cancellation _ _ _ _ _ (inverse_cancel b)

private theorem eval_constant_one (h : Q') : (eval [1] h).eqv 1 :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero h)) (q_add_zero_eqv 1)

private theorem eval_coordinate (h : Q') : (eval coordinate h).eqv h := by
  have ht : (eval [1] h).eqv 1 := eval_constant_one h
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 _ _ (Q'.mul_eqv_congr_left h _ _ ht))
    (Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.mul_one_eqv h))

private theorem eval_complement (h : Q') : (eval complement h).eqv (1 + -h) := by
  have ht : (eval [-1] h).eqv (-1) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) _ 0 (q_mul_zero h)) (q_add_zero_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_eqv_congr_left h _ _ ht))
    (Q'.add_eqv_congr_left 1 _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv h 1)
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv h))))

private theorem power_nonnegative (p : Poly) (h : Q')
    (hp : (0 : Q') ≤ eval p h) (n : Nat) :
    (0 : Q') ≤ eval (polynomialPower p n) h := by
  induction n with
  | zero =>
      exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1)
        (Q'.ge_of_eqv (eval_constant_one h))
  | succ n ih =>
      exact Q'.le_trans' _ _ _
        (Q'.mul_nonneg _ _ hp ih) (Q'.ge_of_eqv (eval_pmul _ _ h))

/-- Nonnegativity includes BOTH endpoints of the closed rational interval. -/
theorem primitive_nonnegative (a b : Nat) (h : Q')
    (h0 : (0 : Q') ≤ h) (h1 : h ≤ 1) :
    (0 : Q') ≤ eval (primitive a b) h := by
  have hH : (0 : Q') ≤ eval coordinate h :=
    Q'.le_trans' _ _ _ h0 (Q'.ge_of_eqv (eval_coordinate h))
  have hU : (0 : Q') ≤ eval complement h := by
    have hh := Q'.add_le_add_right h 1 (-h) h1
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv h)) hh)
      (Q'.ge_of_eqv (eval_complement h))
  induction a generalizing b with
  | zero =>
      exact Q'.le_trans' _ _ _
        (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg b)
          (power_nonnegative coordinate h hH (b + 1)))
        (Q'.ge_of_eqv (eval_pscale _ _ h))
  | succ a ih =>
      have hA : (0 : Q') ≤ Q'.ofNat (a + 1) :=
        Q'.le_of_lt (Q'.ofNat_succ_pos a)
      have hl : (0 : Q') ≤ eval
          (pscale (Q'.invSucc b)
            (pmul (polynomialPower complement (a + 1))
              (polynomialPower coordinate (b + 1)))) h :=
        Q'.le_trans' _ _ _
          (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg b)
            (Q'.le_trans' _ _ _
              (Q'.mul_nonneg _ _ (power_nonnegative complement h hU _)
                (power_nonnegative coordinate h hH _))
              (Q'.ge_of_eqv (eval_pmul _ _ h))))
          (Q'.ge_of_eqv (eval_pscale _ _ h))
      have hr : (0 : Q') ≤ eval
          (pscale (Q'.ofNat (a + 1) * Q'.invSucc b) (primitive a (b + 1))) h :=
        Q'.le_trans' _ _ _
          (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hA (Q'.invSucc_nonneg b))
            (ih (b + 1)))
          (Q'.ge_of_eqv (eval_pscale _ _ h))
      exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ hl hr)
        (Q'.ge_of_eqv (eval_padd _ _ h))

private theorem coordinate_power_zero (b : Nat) :
    (eval (polynomialPower coordinate (b + 1)) 0).eqv 0 :=
  Q'.eqv_trans _ _ _ (eval_pmul _ _ 0)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 _ (eval_coordinate 0)) (q_zero_mul _))

/-- The computed primitive has the exact zero initial value. -/
theorem primitive_zero (a b : Nat) : (eval (primitive a b) 0).eqv 0 := by
  induction a generalizing b with
  | zero =>
      exact Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ 0 (coordinate_power_zero b)) (q_mul_zero _))
  | succ a ih =>
      have hl : (eval
          (pscale (Q'.invSucc b)
            (pmul (polynomialPower complement (a + 1))
              (polynomialPower coordinate (b + 1)))) 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ 0
              (Q'.eqv_trans _ _ _ (eval_pmul _ _ 0)
                (Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_left _ _ 0 (coordinate_power_zero b))
                  (q_mul_zero _)))) (q_mul_zero _))
      have hr : (eval
          (pscale (Q'.ofNat (a + 1) * Q'.invSucc b) (primitive a (b + 1))) 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ 0 (ih (b + 1))) (q_mul_zero _))
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ 0)
        (Q'.eqv_trans _ _ _ (q_add_congr hl hr) (q_add_zero_eqv 0))

private theorem eval_zero_coefficient (p : Poly) :
    (eval p 0).eqv (coeff p 0) := by
  cases p with
  | nil => exact Q'.eqv_refl 0
  | cons c cs =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left c _ 0 (q_zero_mul _)) (q_add_zero_eqv c)

/-- The derivative and initial value determine the ACTUAL finite polynomial.
This lets a computed positive primitive be identified with the original
S/F polynomial, rather than substituting an unrelated positive object. -/
theorem derivative_initial_unique (p q : Poly)
    (hd : CoeffEqv (pderiv p) (pderiv q))
    (h0 : (eval p 0).eqv (eval q 0)) : CoeffEqv p q := by
  intro i
  cases i with
  | zero =>
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_zero_coefficient p))
        (Q'.eqv_trans _ _ _ h0 (eval_zero_coefficient q))
  | succ i =>
      have hc : (Q'.ofNat (i+1)*coeff p (i+1)).eqv
          (Q'.ofNat (i+1)*coeff q (i+1)) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (coeff_pderiv p i))
          (Q'.eqv_trans _ _ _ (hd i) (coeff_pderiv q i))
      have undo (c : Q') :
          (Q'.invSucc i*(Q'.ofNat (i+1)*c)).eqv c :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ c (inverse_cancel i))
            (Q'.one_mul_eqv c))
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (undo (coeff p (i+1))))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc)
          (undo (coeff q (i+1))))

end YMGap.Constructive.QPolyPositivePrimitive

#print axioms YMGap.Constructive.QPolyPositivePrimitive.polynomialPower
#print axioms YMGap.Constructive.QPolyPositivePrimitive.complement
#print axioms YMGap.Constructive.QPolyPositivePrimitive.coordinate
#print axioms YMGap.Constructive.QPolyPositivePrimitive.primitive
#print axioms YMGap.Constructive.QPolyPositivePrimitive.power_derivative_succ
#print axioms YMGap.Constructive.QPolyPositivePrimitive.primitive_derivative
#print axioms YMGap.Constructive.QPolyPositivePrimitive.primitive_nonnegative
#print axioms YMGap.Constructive.QPolyPositivePrimitive.primitive_zero
#print axioms YMGap.Constructive.QPolyPositivePrimitive.derivative_initial_unique
