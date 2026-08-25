/-
# Coefficient-level formal differentiation for constructive rational polynomials

The existing `QPoly` carrier is a finite coefficient list with semantic rational
equality `Q'.eqv`.  This module adds the coefficient-facing formal derivative

    [c₀,c₁,c₂,...]' = [c₁,2c₂,3c₃,...]

and a finite Cauchy-coefficient presentation of multiplication.  The latter is
the constructive bridge needed to state and prove Leibniz identities at an
arbitrary coefficient without normalizing rational representatives.

No infinite power series, quotient choice, or classical coefficient extraction
is used.  Every sum is the structurally recursive `RationalTail.finSum`.
-/

import YMGap.Constructive.QPolyCoefficient
import YMGap.Constructive.CauchyConv

namespace YMGap.Constructive.QPolyFormalDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.RationalTail

local infix:50 " ~q " => Q'.eqv

/-- Scale successive coefficients by `start,start+1,...`. -/
def scaleFrom : Nat -> Poly -> Poly
  | _, [] => []
  | start, c :: cs =>
      (Q'.ofNat start * c) :: scaleFrom (start + 1) cs

/-- Formal derivative of a finite coefficient-list polynomial. -/
def pderiv : Poly -> Poly
  | [] => []
  | _ :: cs => scaleFrom 1 cs

/-- Arbitrary padded coefficient of `scaleFrom`. -/
theorem coeff_scaleFrom : forall (start : Nat) (p : Poly) (index : Nat),
    (coeff (scaleFrom start p) index).eqv
      (Q'.ofNat (start + index) * coeff p index)
  | start, [], index => Q'.eqv_symm (q_mul_zero _)
  | start, c :: cs, 0 => by
      change (Q'.ofNat start * c).eqv
        (Q'.ofNat (start + 0) * c)
      rw [Nat.add_zero]
      exact Q'.eqv_refl _
  | start, c :: cs, index + 1 => by
      change
        (coeff (scaleFrom (start + 1) cs) index).eqv
          (Q'.ofNat (start + (index + 1)) * coeff cs index)
      have hind := coeff_scaleFrom (start + 1) cs index
      have hindex : start + (index + 1) = (start + 1) + index := by
        omega
      rw [hindex]
      exact hind

/-- The `index`-th derivative coefficient is
`(index+1) * p[index+1]`. -/
theorem coeff_pderiv (p : Poly) (index : Nat) :
    (coeff (pderiv p) index).eqv
      (Q'.ofNat (index + 1) * coeff p (index + 1)) := by
  cases p with
  | nil => exact Q'.eqv_symm (q_mul_zero _)
  | cons c cs =>
      change
        (coeff (scaleFrom 1 cs) index).eqv
          (Q'.ofNat (index + 1) * coeff cs index)
      have h := coeff_scaleFrom 1 cs index
      have hindex : 1 + index = index + 1 := by omega
      rw [hindex] at h
      exact h

/-- Coefficientwise semantic equality of finite polynomials, with zero padding. -/
def CoeffEqv (p q : Poly) : Prop :=
  forall index : Nat, (coeff p index).eqv (coeff q index)

theorem CoeffEqv.refl (p : Poly) : CoeffEqv p p :=
  fun _ => Q'.eqv_refl _

theorem CoeffEqv.symm {p q : Poly} (h : CoeffEqv p q) : CoeffEqv q p :=
  fun index => Q'.eqv_symm (h index)

theorem CoeffEqv.trans {p q r : Poly}
    (hpq : CoeffEqv p q) (hqr : CoeffEqv q r) : CoeffEqv p r :=
  fun index => Q'.eqv_trans _ _ _ (hpq index) (hqr index)

theorem CoeffEqv.padd {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (padd p q) (padd p' q') := by
  intro index
  exact Q'.eqv_trans _ (coeff p index + coeff q index) _
    (coeff_padd index p q)
    (Q'.eqv_trans _ (coeff p' index + coeff q' index) _
      (q_add_congr (hp index) (hq index))
      (Q'.eqv_symm (coeff_padd index p' q')))

theorem CoeffEqv.pscale (k : Q') {p q : Poly}
    (h : CoeffEqv p q) : CoeffEqv (pscale k p) (pscale k q) := by
  intro index
  exact Q'.eqv_trans _ (k * coeff p index) _
    (coeff_pscale k p index)
    (Q'.eqv_trans _ (k * coeff q index) _
      (Q'.mul_eqv_congr_left k _ _ (h index))
      (Q'.eqv_symm (coeff_pscale k q index)))

/-- Padded coefficients of polynomial negation are rational negations of the
corresponding input coefficients. -/
theorem coeff_pneg_eqv (p : Poly) (index : Nat) :
    (coeff (pneg p) index).eqv (-(coeff p index)) := by
  unfold pneg
  exact Q'.eqv_trans _ ((-1 : Q') * coeff p index) _
    (coeff_pscale (-1) p index)
    (Q'.eqv_trans _ (-(1 * coeff p index)) _
      (Q'.neg_mul_eqv 1 (coeff p index))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))

/-- Coefficientwise-equivalent polynomials remain equivalent after
negation. -/
theorem CoeffEqv.pneg {p q : Poly} (h : CoeffEqv p q) :
    CoeffEqv (pneg p) (pneg q) := CoeffEqv.pscale (-1) h

/-- Coefficientwise cancellation of a middle polynomial and its negation. -/
theorem coeffEqv_padd_pneg_cancel (p q r : Poly) :
    CoeffEqv (padd (padd p (pneg q)) (padd q r)) (padd p r) := by
  intro index
  let a : Q' := coeff p index
  let b : Q' := coeff q index
  let c : Q' := coeff r index
  refine Q'.eqv_trans _
    (coeff (padd p (pneg q)) index + coeff (padd q r) index) _
    (coeff_padd index (padd p (pneg q)) (padd q r)) ?_
  refine Q'.eqv_trans _
    ((a + -b) + (b + c)) _
    (q_add_congr
      (Q'.eqv_trans _
        (a + coeff (pneg q) index) _
        (coeff_padd index p (pneg q))
        (Q'.add_eqv_congr_left a _ _ (coeff_pneg_eqv q index)))
      (coeff_padd index q r)) ?_
  refine Q'.eqv_trans _
    (a + ((-b + b) + c)) _
    (Q'.eqv_trans _
      ((a + -b) + b + c) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (a + -b) b c))
      (Q'.eqv_trans _
        ((a + (-b + b)) + c) _
        (Q'.add_eqv_congr_right _ _ c
          (Q'.add_assoc_eqv a (-b) b))
        (Q'.add_assoc_eqv a (-b + b) c))) ?_
  refine Q'.eqv_trans _
    (a + (0 + c)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_eqv_congr_right _ 0 c (Q'.neg_add_self_eqv b))) ?_
  refine Q'.eqv_trans _ (a + c) _
    (Q'.add_eqv_congr_left a _ c (q_zero_add_eqv c))
    (Q'.eqv_symm (coeff_padd index p r))

theorem CoeffEqv.zeroCons {p q : Poly} (h : CoeffEqv p q) :
    CoeffEqv ((0 : Q') :: p) ((0 : Q') :: q) := by
  intro index
  cases index with
  | zero => exact Q'.eqv_refl 0
  | succ index => exact h index

theorem coeffEqv_padd_comm (p q : Poly) :
    CoeffEqv (padd p q) (padd q p) := by
  intro index
  exact Q'.eqv_trans _ (coeff p index + coeff q index) _
    (coeff_padd index p q)
    (Q'.eqv_trans _ (coeff q index + coeff p index) _
      (Q'.add_comm_eqv _ _)
      (Q'.eqv_symm (coeff_padd index q p)))

/-- A polynomial plus its coefficientwise negation is the padded zero
polynomial. -/
theorem coeffEqv_padd_pneg_self (p : Poly) :
    CoeffEqv (padd p (pneg p)) [] := by
  intro index
  exact Q'.eqv_trans _
    (coeff p index + coeff (pneg p) index) _
    (coeff_padd index p (pneg p))
    (Q'.eqv_trans _
      (coeff p index + -(coeff p index)) _
      (Q'.add_eqv_congr_left _ _ _ (coeff_pneg_eqv p index))
      (Q'.add_neg_self_eqv _))

theorem coeffEqv_padd_assoc (p q r : Poly) :
    CoeffEqv (padd (padd p q) r) (padd p (padd q r)) := by
  intro index
  exact Q'.eqv_trans _
    ((coeff p index + coeff q index) + coeff r index) _
    (Q'.eqv_trans _
      (coeff (padd p q) index + coeff r index) _
      (coeff_padd index (padd p q) r)
      (Q'.add_eqv_congr_right _ _ _ (coeff_padd index p q)))
    (Q'.eqv_trans _
      (coeff p index + (coeff q index + coeff r index)) _
      (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_symm
        (Q'.eqv_trans _
          (coeff p index + coeff (padd q r) index) _
          (coeff_padd index p (padd q r))
          (Q'.add_eqv_congr_left _ _ _ (coeff_padd index q r)))))

/-- Polynomial addition inherits the rational interchange law. -/
theorem coeffEqv_padd_interchange (p q r s : Poly) :
    CoeffEqv (padd (padd p q) (padd r s))
      (padd (padd p r) (padd q s)) := by
  intro index
  refine Q'.eqv_trans _
    (coeff (padd p q) index + coeff (padd r s) index) _
    (coeff_padd index (padd p q) (padd r s)) ?_
  refine Q'.eqv_trans _
    ((coeff p index + coeff q index) +
      (coeff r index + coeff s index)) _
    (q_add_congr (coeff_padd index p q) (coeff_padd index r s)) ?_
  refine Q'.eqv_trans _
    ((coeff p index + coeff r index) +
      (coeff q index + coeff s index)) _
    (q_interchange _ _ _ _) ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (coeff (padd p r) index + coeff (padd q s) index) _
      (coeff_padd index (padd p r) (padd q s))
      (q_add_congr (coeff_padd index p r) (coeff_padd index q s)))

/-- Reflection reversal of a finite rational sum. -/
theorem finSum_reverse (f : QSeq) : forall count : Nat,
    (finSum f count).eqv
      (finSum (fun index => f (count - 1 - index)) count)
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      have hpeel := finSum_peel_left
        (fun index => f (count - index)) count
      have hreflect :
          (fun index => f (count + 1 - 1 - index)) =
            (fun index => f (count - index)) := by
        funext index
        have h : count + 1 - 1 - index = count - index := by omega
        rw [h]
      have htail :
          (fun index => f (count - (index + 1))) =
            (fun index => f (count - 1 - index)) := by
        funext index
        have h : count - (index + 1) = count - 1 - index := by omega
        rw [h]
      rw [hreflect]
      change
        (finSum f count + f count).eqv
          (finSum (fun index => f (count - index)) (count + 1))
      refine Q'.eqv_trans _
        (f count + finSum f count) _
        (Q'.add_comm_eqv _ _) ?_
      have hinner :
          (finSum f count).eqv
            (finSum (fun index => f (count - (index + 1))) count) := by
        rw [htail]
        exact finSum_reverse f count
      have hzero : count - 0 = count := by omega
      rw [hzero] at hpeel
      exact Q'.eqv_trans _
        (f count +
          finSum (fun index => f (count - (index + 1))) count) _
        (Q'.add_eqv_congr_left _ _ _ hinner)
        (Q'.eqv_symm hpeel)

/-- The finite Cauchy coefficient `sum_{i=0}^degree p_i q_{degree-i}`. -/
def cauchyCoeff (p q : Poly) (degree : Nat) : Q' :=
  finSum
    (fun index => coeff p index * coeff q (degree - index))
    (degree + 1)

/-- One summand of the finite Cauchy coefficient. -/
def cauchyTerm (p q : Poly) (degree index : Nat) : Q' :=
  coeff p index * coeff q (degree - index)

/-- Multiplication in `QPoly` has the expected finite Cauchy coefficient. -/
theorem coeff_pmul_eqv_cauchyCoeff : forall (p q : Poly) (degree : Nat),
    (coeff (pmul p q) degree).eqv (cauchyCoeff p q degree)
  | [], q, degree => by
      unfold cauchyCoeff
      have hzero :
          (finSum
            (fun index => coeff ([] : Poly) index *
              coeff q (degree - index))
            (degree + 1)).eqv
            (finSum (fun _ => (0 : Q')) (degree + 1)) :=
        finSum_eqv_congr _ _
          (fun index => q_zero_mul (coeff q (degree - index))) _
      exact Q'.eqv_trans _
        (0 : Q') _
        (Q'.eqv_refl 0)
        (Q'.eqv_trans _
          (finSum (fun _ => (0 : Q')) (degree + 1)) _
          (Q'.eqv_symm
            (Q'.eqv_of_eq (finSum_zero_seq (degree + 1))))
          (Q'.eqv_symm hzero))
  | a :: ps, q, 0 => by
      unfold cauchyCoeff
      change
        (coeff (pmul (a :: ps) q) 0).eqv
          ((0 : Q') + a * coeff q 0)
      exact Q'.eqv_trans _ (a * coeff q 0) _
        (coeff_pmul (a :: ps) q 0)
        (Q'.eqv_symm (q_zero_add_eqv _))
  | a :: ps, q, degree + 1 => by
      unfold cauchyCoeff
      let term : Nat -> Q' := fun index =>
        coeff (a :: ps) index * coeff q ((degree + 1) - index)
      have hpeel := finSum_peel_left term (degree + 1)
      have htailTerm : forall index : Nat, index < degree + 1 ->
          (term (index + 1)).eqv
            (coeff ps index * coeff q (degree - index)) := by
        intro index hindex
        have hsub : (degree + 1) - (index + 1) = degree - index := by
          omega
        change
          (coeff ps index * coeff q ((degree + 1) - (index + 1))).eqv
            (coeff ps index * coeff q (degree - index))
        rw [hsub]
        exact Q'.eqv_refl _
      have htail :
          (finSum (fun index => term (index + 1)) (degree + 1)).eqv
            (finSum
              (fun index => coeff ps index * coeff q (degree - index))
              (degree + 1)) :=
        finSum_eqv_congr_lt _ _ (degree + 1) htailTerm
      have hhead : (term 0).eqv (a * coeff q (degree + 1)) := by
        change
          (a * coeff q ((degree + 1) - 0)).eqv
            (a * coeff q (degree + 1))
        rw [Nat.sub_zero]
        exact Q'.eqv_refl _
      have hproduct := coeff_pmul (a :: ps) q (degree + 1)
      have htailProduct := coeff_pmul_eqv_cauchyCoeff ps q degree
      have hcauchyPeel :
          (finSum term (degree + 2)).eqv
            (a * coeff q (degree + 1) +
              finSum
                (fun index => coeff ps index * coeff q (degree - index))
                (degree + 1)) := by
        exact Q'.eqv_trans _
          (term 0 +
            finSum (fun index => term (index + 1)) (degree + 1)) _
          hpeel
          (Q'.eqv_trans _
            (a * coeff q (degree + 1) +
              finSum (fun index => term (index + 1)) (degree + 1)) _
            (q_add_congr hhead (Q'.eqv_refl _))
            (Q'.add_eqv_congr_left _ _ _ htail))
      exact Q'.eqv_trans _
        (a * coeff q (degree + 1) +
          coeff (pmul ps q) degree) _
        (Q'.eqv_trans _
          (a * coeff q (degree + 1) + mulCoeff ps q degree) _
          hproduct
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (coeff_pmul ps q degree))))
        (Q'.eqv_trans _
          (a * coeff q (degree + 1) +
            finSum
              (fun index => coeff ps index * coeff q (degree - index))
              (degree + 1)) _
          (Q'.add_eqv_congr_left _ _ _ htailProduct)
          (Q'.eqv_symm hcauchyPeel))

/-- Coefficientwise congruence of polynomial multiplication. -/
theorem CoeffEqv.pmul {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (pmul p q) (pmul p' q') := by
  intro degree
  refine Q'.eqv_trans _ (cauchyCoeff p q degree) _
    (coeff_pmul_eqv_cauchyCoeff p q degree) ?_
  refine Q'.eqv_trans _ (cauchyCoeff p' q' degree) _ ?_
    (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff p' q' degree))
  unfold cauchyCoeff
  exact finSum_eqv_congr_lt _ _ (degree + 1) (fun index hindex =>
    q_mul_congr (hp index) (hq (degree - index)))

/-- Commutativity of `QPoly` multiplication at every padded coefficient. -/
theorem coeffEqv_pmul_comm (p q : Poly) :
    CoeffEqv (pmul p q) (pmul q p) := by
  intro degree
  let term : QSeq := fun index =>
    coeff p index * coeff q (degree - index)
  have hreverse := finSum_reverse term (degree + 1)
  have hreindex :
      (finSum (fun index => term (degree + 1 - 1 - index))
        (degree + 1)).eqv
        (cauchyCoeff q p degree) := by
    unfold cauchyCoeff
    exact finSum_eqv_congr_lt _ _ (degree + 1) (fun index hindex => by
      have hfirst : degree + 1 - 1 - index = degree - index := by
        omega
      have hsecond : degree - (degree - index) = index := by
        omega
      unfold term
      rw [hfirst, hsecond]
      exact Q'.mul_comm_eqv _ _)
  exact Q'.eqv_trans _ (cauchyCoeff p q degree) _
    (coeff_pmul_eqv_cauchyCoeff p q degree)
    (Q'.eqv_trans _
      (finSum (fun index => term (degree + 1 - 1 - index))
        (degree + 1)) _
      hreverse
      (Q'.eqv_trans _ (cauchyCoeff q p degree) _
        hreindex
        (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff q p degree))))

/-- Right distributivity of multiplication over coefficient-list addition. -/
theorem coeffEqv_pmul_padd_right (p q r : Poly) :
    CoeffEqv (pmul p (padd q r))
      (padd (pmul p q) (pmul p r)) := by
  intro degree
  refine Q'.eqv_trans _ (cauchyCoeff p (padd q r) degree) _
    (coeff_pmul_eqv_cauchyCoeff p (padd q r) degree) ?_
  unfold cauchyCoeff
  have hterms :
      (finSum
        (fun index =>
          coeff p index * coeff (padd q r) (degree - index))
        (degree + 1)).eqv
        (finSum
          (fun index =>
            coeff p index * coeff q (degree - index) +
              coeff p index * coeff r (degree - index))
          (degree + 1)) :=
    finSum_eqv_congr_lt _ _ (degree + 1) (fun index hindex =>
      Q'.eqv_trans _
        (coeff p index *
          (coeff q (degree - index) + coeff r (degree - index))) _
        (Q'.mul_eqv_congr_left _ _ _
          (coeff_padd (degree - index) q r))
        (Q'.mul_add_eqv _ _ _))
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        coeff p index * coeff q (degree - index) +
          coeff p index * coeff r (degree - index))
      (degree + 1)) _ hterms ?_
  refine Q'.eqv_trans _
    (finSum
        (fun index => coeff p index * coeff q (degree - index))
        (degree + 1) +
      finSum
        (fun index => coeff p index * coeff r (degree - index))
        (degree + 1)) _
    (finSum_add _ _ (degree + 1)) ?_
  exact Q'.eqv_trans _
    (coeff (pmul p q) degree + coeff (pmul p r) degree) _
    (q_add_congr
      (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff p q degree))
      (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff p r degree)))
    (Q'.eqv_symm (coeff_padd degree (pmul p q) (pmul p r)))

/-- Left distributivity, obtained from commutativity and right
distributivity without changing coefficient representatives. -/
theorem coeffEqv_padd_pmul_left (p q r : Poly) :
    CoeffEqv (pmul (padd p q) r)
      (padd (pmul p r) (pmul q r)) :=
  CoeffEqv.trans (coeffEqv_pmul_comm (padd p q) r)
    (CoeffEqv.trans (coeffEqv_pmul_padd_right r p q)
      (CoeffEqv.padd
        (coeffEqv_pmul_comm r p) (coeffEqv_pmul_comm r q)))

/-- A scalar may be pulled through the left input of multiplication. -/
theorem coeffEqv_pscale_pmul (k : Q') (p q : Poly) :
    CoeffEqv (pmul (pscale k p) q) (pscale k (pmul p q)) := by
  intro degree
  refine Q'.eqv_trans _ (cauchyCoeff (pscale k p) q degree) _
    (coeff_pmul_eqv_cauchyCoeff (pscale k p) q degree) ?_
  unfold cauchyCoeff
  have hterms :
      (finSum
        (fun index =>
          coeff (pscale k p) index * coeff q (degree - index))
        (degree + 1)).eqv
        (finSum
          (fun index => k *
            (coeff p index * coeff q (degree - index)))
          (degree + 1)) :=
    finSum_eqv_congr_lt _ _ (degree + 1) (fun index hindex =>
      Q'.eqv_trans _
        ((k * coeff p index) * coeff q (degree - index)) _
        (Q'.mul_eqv_congr_right _ _ _ (coeff_pscale k p index))
        (Q'.mul_assoc_eqv _ _ _))
  refine Q'.eqv_trans _
    (finSum
      (fun index => k *
        (coeff p index * coeff q (degree - index)))
      (degree + 1)) _ hterms ?_
  refine Q'.eqv_trans _
    (k * finSum
      (fun index => coeff p index * coeff q (degree - index))
      (degree + 1)) _
    (Q'.eqv_symm
      (const_mul_finSum
        (fun index => coeff p index * coeff q (degree - index))
        k (degree + 1))) ?_
  exact Q'.eqv_trans _
    (k * coeff (pmul p q) degree) _
    (Q'.mul_eqv_congr_left k _ _
      (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff p q degree)))
    (Q'.eqv_symm (coeff_pscale k (pmul p q) degree))

/-- A scalar may likewise be pulled through the right input of
multiplication. -/
theorem coeffEqv_pmul_pscale (k : Q') (p q : Poly) :
    CoeffEqv (pmul p (pscale k q)) (pscale k (pmul p q)) :=
  CoeffEqv.trans (coeffEqv_pmul_comm p (pscale k q))
    (CoeffEqv.trans (coeffEqv_pscale_pmul k q p)
      (CoeffEqv.pscale k (coeffEqv_pmul_comm q p)))

/-- Nested coefficient scalings multiply their scalars. -/
theorem coeffEqv_pscale_comp (a b : Q') (p : Poly) :
    CoeffEqv (pscale a (pscale b p)) (pscale (a * b) p) := by
  intro index
  exact Q'.eqv_trans _
    (a * coeff (pscale b p) index) _
    (coeff_pscale a (pscale b p) index)
    (Q'.eqv_trans _
      (a * (b * coeff p index)) _
      (Q'.mul_eqv_congr_left a _ _ (coeff_pscale b p index))
      (Q'.eqv_trans _
        ((a * b) * coeff p index) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv a b (coeff p index)))
        (Q'.eqv_symm (coeff_pscale (a * b) p index))))

/-- Adding two scalings of the same polynomial adds the scalars. -/
theorem coeffEqv_padd_pscale (a b : Q') (p : Poly) :
    CoeffEqv (padd (pscale a p) (pscale b p))
      (pscale (a + b) p) := by
  intro index
  exact Q'.eqv_trans _
    (coeff (pscale a p) index + coeff (pscale b p) index) _
    (coeff_padd index (pscale a p) (pscale b p))
    (Q'.eqv_trans _
      (a * coeff p index + b * coeff p index) _
      (q_add_congr
        (coeff_pscale a p index) (coeff_pscale b p index))
      (Q'.eqv_trans _
        ((a + b) * coeff p index) _
        (Q'.eqv_symm (Q'.add_mul_eqv a b (coeff p index)))
        (Q'.eqv_symm (coeff_pscale (a + b) p index))))

/-- Scaling distributes over polynomial addition coefficientwise. -/
theorem coeffEqv_pscale_padd (k : Q') (p q : Poly) :
    CoeffEqv (pscale k (padd p q))
      (padd (pscale k p) (pscale k q)) := by
  intro index
  refine Q'.eqv_trans _
    (k * coeff (padd p q) index) _
    (coeff_pscale k (padd p q) index) ?_
  refine Q'.eqv_trans _
    (k * (coeff p index + coeff q index)) _
    (Q'.mul_eqv_congr_left k _ _ (coeff_padd index p q)) ?_
  refine Q'.eqv_trans _
    (k * coeff p index + k * coeff q index) _
    (Q'.mul_add_eqv k _ _) ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (coeff (pscale k p) index + coeff (pscale k q) index) _
      (coeff_padd index (pscale k p) (pscale k q))
      (q_add_congr
        (coeff_pscale k p index) (coeff_pscale k q index)))

/-- Negation distributes over polynomial addition. -/
theorem coeffEqv_pneg_padd (p q : Poly) :
    CoeffEqv (pneg (padd p q)) (padd (pneg p) (pneg q)) := by
  unfold pneg
  exact coeffEqv_pscale_padd (-1) p q

/-- Semantically equal rational scalars induce coefficientwise-equivalent
polynomial scalings. -/
theorem coeffEqv_pscale_scalar {a b : Q'} (h : a.eqv b) (p : Poly) :
    CoeffEqv (pscale a p) (pscale b p) := by
  intro index
  exact Q'.eqv_trans _ (a * coeff p index) _
    (coeff_pscale a p index)
    (Q'.eqv_trans _ (b * coeff p index) _
      (Q'.mul_eqv_congr_right a b _ h)
      (Q'.eqv_symm (coeff_pscale b p index)))

/-- Scaling by one preserves every padded coefficient. -/
theorem coeffEqv_pscale_one (p : Poly) : CoeffEqv (pscale 1 p) p := by
  intro index
  exact Q'.eqv_trans _ ((1 : Q') * coeff p index) _
    (coeff_pscale 1 p index) (Q'.one_mul_eqv _)

/-- Double polynomial negation restores every padded coefficient. -/
theorem coeffEqv_pneg_pneg (p : Poly) : CoeffEqv (pneg (pneg p)) p := by
  unfold pneg
  exact CoeffEqv.trans
    (coeffEqv_pscale_comp (-1) (-1) p)
    (CoeffEqv.trans
      (coeffEqv_pscale_scalar
        (by decide : (((-1 : Q') * (-1 : Q')).eqv (1 : Q'))) p)
      (coeffEqv_pscale_one p))

/-- The singleton constant-one polynomial is a left multiplicative identity
up to padded coefficient equality. -/
theorem coeffEqv_pmul_one_left (p : Poly) :
    CoeffEqv (pmul [(1 : Q')] p) p := by
  intro index
  change
    (coeff (padd (pscale 1 p) [(0 : Q')]) index).eqv
      (coeff p index)
  have hzero : (coeff [(0 : Q')] index).eqv 0 := by
    cases index with
    | zero => exact Q'.eqv_refl 0
    | succ index => exact Q'.eqv_refl 0
  exact Q'.eqv_trans _
    (coeff (pscale 1 p) index + coeff [(0 : Q')] index) _
    (coeff_padd index (pscale 1 p) [(0 : Q')])
    (Q'.eqv_trans _
      (coeff p index + 0) _
      (q_add_congr (coeffEqv_pscale_one p index) hzero)
      (q_add_zero_eqv _))

/-- Multiplication by a polynomial with a prepended zero shifts the complete
product by one coefficient. -/
theorem coeffEqv_zeroCons_pmul (p q : Poly) :
    CoeffEqv (pmul ((0 : Q') :: p) q)
      ((0 : Q') :: pmul p q) := by
  intro degree
  change
    (coeff (padd (pscale 0 q) ((0 : Q') :: pmul p q)) degree).eqv
      (coeff ((0 : Q') :: pmul p q) degree)
  exact Q'.eqv_trans _
    (coeff (pscale 0 q) degree +
      coeff ((0 : Q') :: pmul p q) degree) _
    (coeff_padd degree (pscale 0 q) ((0 : Q') :: pmul p q))
    (Q'.eqv_trans _
      ((0 : Q') + coeff ((0 : Q') :: pmul p q) degree) _
      (Q'.add_eqv_congr_right _ 0 _
        (Q'.eqv_trans _ (0 * coeff q degree) _
          (coeff_pscale 0 q degree) (q_zero_mul _)))
      (q_zero_add_eqv _))

/-- Associativity of `QPoly` multiplication at every padded coefficient. -/
theorem coeffEqv_pmul_assoc : forall (p q r : Poly),
    CoeffEqv (pmul (pmul p q) r) (pmul p (pmul q r))
  | [], q, r => CoeffEqv.refl []
  | a :: ps, q, r => by
      change
        CoeffEqv
          (pmul
            (padd (pscale a q) ((0 : Q') :: pmul ps q)) r)
          (padd (pscale a (pmul q r))
            ((0 : Q') :: pmul ps (pmul q r)))
      refine CoeffEqv.trans
        (coeffEqv_padd_pmul_left
          (pscale a q) ((0 : Q') :: pmul ps q) r) ?_
      exact CoeffEqv.padd
        (coeffEqv_pscale_pmul a q r)
        (CoeffEqv.trans
          (coeffEqv_zeroCons_pmul (pmul ps q) r)
          (CoeffEqv.zeroCons (coeffEqv_pmul_assoc ps q r)))

/-! ## Weighted Cauchy reindexing and the coefficient Leibniz rule -/

/-- The index-weighted half of the next Cauchy coefficient is the Cauchy
coefficient with the derivative on the left factor. -/
theorem leftWeightedCauchy (p q : Poly) (degree : Nat) :
    (finSum
      (fun index =>
        Q'.ofNat index * cauchyTerm p q (degree + 1) index)
      (degree + 2)).eqv
      (cauchyCoeff (pderiv p) q degree) := by
  let weighted : Nat -> Q' := fun index =>
    Q'.ofNat index * cauchyTerm p q (degree + 1) index
  have hpeel := finSum_peel_left weighted (degree + 1)
  have hzero : (weighted 0).eqv 0 := by
    unfold weighted cauchyTerm
    exact Q'.eqv_trans _
      ((0 : Q') *
        (coeff p 0 * coeff q ((degree + 1) - 0))) _
      (Q'.mul_eqv_congr_right _ 0 _ Q'.ofNat_zero_eqv)
      (q_zero_mul _)
  have hterm : forall index : Nat, index < degree + 1 ->
      (weighted (index + 1)).eqv
        (coeff (pderiv p) index * coeff q (degree - index)) := by
    intro index hindex
    have hsub : (degree + 1) - (index + 1) = degree - index := by
      omega
    unfold weighted cauchyTerm
    rw [hsub]
    exact Q'.eqv_trans _
      ((Q'.ofNat (index + 1) * coeff p (index + 1)) *
        coeff q (degree - index)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat (index + 1))
          (coeff p (index + 1)) (coeff q (degree - index))))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (coeff_pderiv p index)))
  have hsum :
      (finSum (fun index => weighted (index + 1)) (degree + 1)).eqv
        (cauchyCoeff (pderiv p) q degree) := by
    unfold cauchyCoeff
    exact finSum_eqv_congr_lt _ _ (degree + 1) hterm
  exact Q'.eqv_trans _
    (weighted 0 +
      finSum (fun index => weighted (index + 1)) (degree + 1)) _
    hpeel
    (Q'.eqv_trans _
      ((0 : Q') +
        finSum (fun index => weighted (index + 1)) (degree + 1)) _
      (q_add_congr hzero (Q'.eqv_refl _))
      (Q'.eqv_trans _
        (finSum (fun index => weighted (index + 1)) (degree + 1)) _
        (q_zero_add_eqv _)
        hsum))

/-- The complementary-index-weighted half of the next Cauchy coefficient is
the Cauchy coefficient with the derivative on the right factor. -/
theorem rightWeightedCauchy (p q : Poly) (degree : Nat) :
    (finSum
      (fun index =>
        Q'.ofNat ((degree + 1) - index) *
          cauchyTerm p q (degree + 1) index)
      (degree + 2)).eqv
      (cauchyCoeff p (pderiv q) degree) := by
  let weighted : Nat -> Q' := fun index =>
    Q'.ofNat ((degree + 1) - index) *
      cauchyTerm p q (degree + 1) index
  have hlast : (weighted (degree + 1)).eqv 0 := by
    unfold weighted
    have hzero : (degree + 1) - (degree + 1) = 0 := by omega
    rw [hzero]
    exact Q'.eqv_trans _
      ((0 : Q') * cauchyTerm p q (degree + 1) (degree + 1)) _
      (Q'.mul_eqv_congr_right _ 0 _ Q'.ofNat_zero_eqv)
      (q_zero_mul _)
  have hterm : forall index : Nat, index < degree + 1 ->
      (weighted index).eqv
        (coeff p index * coeff (pderiv q) (degree - index)) := by
    intro index hindex
    have hsub : (degree + 1) - index = (degree - index) + 1 := by
      omega
    unfold weighted cauchyTerm
    rw [hsub]
    exact Q'.eqv_trans _
      ((Q'.ofNat ((degree - index) + 1) * coeff p index) *
        coeff q ((degree - index) + 1)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat ((degree - index) + 1))
          (coeff p index) (coeff q ((degree - index) + 1))))
      (Q'.eqv_trans _
        ((coeff p index * Q'.ofNat ((degree - index) + 1)) *
          coeff q ((degree - index) + 1)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            (Q'.ofNat ((degree - index) + 1)) (coeff p index)))
        (Q'.eqv_trans _
          (coeff p index *
            (Q'.ofNat ((degree - index) + 1) *
              coeff q ((degree - index) + 1))) _
          (Q'.mul_assoc_eqv (coeff p index)
            (Q'.ofNat ((degree - index) + 1))
            (coeff q ((degree - index) + 1)))
          (Q'.mul_eqv_congr_left (coeff p index) _ _
            (Q'.eqv_symm (coeff_pderiv q (degree - index))))))
  have hsum :
      (finSum weighted (degree + 1)).eqv
        (cauchyCoeff p (pderiv q) degree) := by
    unfold cauchyCoeff
    exact finSum_eqv_congr_lt _ _ (degree + 1) hterm
  change
    (finSum weighted (degree + 1) + weighted (degree + 1)).eqv
      (cauchyCoeff p (pderiv q) degree)
  exact Q'.eqv_trans _
    (finSum weighted (degree + 1) + (0 : Q')) _
    (Q'.add_eqv_congr_left _ _ 0 hlast)
    (Q'.eqv_trans _
      (finSum weighted (degree + 1)) _
      (q_add_zero_eqv _)
      hsum)

/-- Multiplying the next Cauchy coefficient by its degree splits into the
two derivative Cauchy coefficients. -/
theorem weightedCauchy_split (p q : Poly) (degree : Nat) :
    (Q'.ofNat (degree + 1) * cauchyCoeff p q (degree + 1)).eqv
      (cauchyCoeff (pderiv p) q degree +
        cauchyCoeff p (pderiv q) degree) := by
  unfold cauchyCoeff
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        Q'.ofNat (degree + 1) *
          cauchyTerm p q (degree + 1) index)
      (degree + 2)) _ ?_ ?_
  · exact const_mul_finSum
      (fun index => cauchyTerm p q (degree + 1) index)
      (Q'.ofNat (degree + 1)) (degree + 2)
  · have hsplit : forall index : Nat, index < degree + 2 ->
        (Q'.ofNat (degree + 1) *
          cauchyTerm p q (degree + 1) index).eqv
          (Q'.ofNat index * cauchyTerm p q (degree + 1) index +
            Q'.ofNat ((degree + 1) - index) *
              cauchyTerm p q (degree + 1) index) := by
      intro index hindex
      have hle : index <= degree + 1 := Nat.lt_succ_iff.mp hindex
      have hadd : index + ((degree + 1) - index) = degree + 1 := by
        omega
      have hofNat :
          (Q'.ofNat (degree + 1)).eqv
            (Q'.ofNat index +
              Q'.ofNat ((degree + 1) - index)) := by
        have h := Q'.ofNat_add_eqv index ((degree + 1) - index)
        rw [hadd] at h
        exact h
      exact Q'.eqv_trans _
        ((Q'.ofNat index + Q'.ofNat ((degree + 1) - index)) *
          cauchyTerm p q (degree + 1) index) _
        (Q'.mul_eqv_congr_right _ _ _ hofNat)
        (Q'.add_mul_eqv _ _ _)
    refine Q'.eqv_trans _
      (finSum
        (fun index =>
          Q'.ofNat index * cauchyTerm p q (degree + 1) index +
            Q'.ofNat ((degree + 1) - index) *
              cauchyTerm p q (degree + 1) index)
        (degree + 2)) _
      (finSum_eqv_congr_lt _ _ (degree + 2) hsplit) ?_
    refine Q'.eqv_trans _
      (finSum
          (fun index =>
            Q'.ofNat index * cauchyTerm p q (degree + 1) index)
          (degree + 2) +
        finSum
          (fun index =>
            Q'.ofNat ((degree + 1) - index) *
              cauchyTerm p q (degree + 1) index)
          (degree + 2)) _
      (finSum_add _ _ (degree + 2)) ?_
    exact q_add_congr
      (leftWeightedCauchy p q degree)
      (rightWeightedCauchy p q degree)

/-- Coefficient-level finite Leibniz rule for `QPoly`. -/
theorem coeff_pderiv_pmul (p q : Poly) (degree : Nat) :
    (coeff (pderiv (pmul p q)) degree).eqv
      (coeff
        (padd (pmul (pderiv p) q) (pmul p (pderiv q)))
        degree) := by
  exact Q'.eqv_trans _
    (Q'.ofNat (degree + 1) *
      coeff (pmul p q) (degree + 1)) _
    (coeff_pderiv (pmul p q) degree)
    (Q'.eqv_trans _
      (Q'.ofNat (degree + 1) *
        cauchyCoeff p q (degree + 1)) _
      (Q'.mul_eqv_congr_left _ _ _
        (coeff_pmul_eqv_cauchyCoeff p q (degree + 1)))
      (Q'.eqv_trans _
        (cauchyCoeff (pderiv p) q degree +
          cauchyCoeff p (pderiv q) degree) _
        (weightedCauchy_split p q degree)
        (Q'.eqv_trans _
          (coeff (pmul (pderiv p) q) degree +
            coeff (pmul p (pderiv q)) degree) _
          (q_add_congr
            (Q'.eqv_symm
              (coeff_pmul_eqv_cauchyCoeff (pderiv p) q degree))
            (Q'.eqv_symm
              (coeff_pmul_eqv_cauchyCoeff p (pderiv q) degree)))
          (Q'.eqv_symm
            (coeff_padd degree
              (pmul (pderiv p) q) (pmul p (pderiv q)))))))

/-- Polynomial-level coefficientwise Leibniz rule. -/
theorem pderiv_pmul (p q : Poly) :
    CoeffEqv (pderiv (pmul p q))
      (padd (pmul (pderiv p) q) (pmul p (pderiv q))) :=
  coeff_pderiv_pmul p q

/-- Coefficientwise-equivalent inputs have coefficientwise-equivalent
derivatives. -/
theorem CoeffEqv.pderiv {p q : Poly} (h : CoeffEqv p q) :
    CoeffEqv (pderiv p) (pderiv q) := by
  intro degree
  exact Q'.eqv_trans _
    (Q'.ofNat (degree + 1) * coeff p (degree + 1)) _
    (coeff_pderiv p degree)
    (Q'.eqv_trans _
      (Q'.ofNat (degree + 1) * coeff q (degree + 1)) _
      (Q'.mul_eqv_congr_left _ _ _ (h (degree + 1)))
      (Q'.eqv_symm (coeff_pderiv q degree)))

/-- Formal differentiation is additive coefficientwise. -/
theorem pderiv_padd (p q : Poly) :
    CoeffEqv (pderiv (padd p q))
      (padd (pderiv p) (pderiv q)) := by
  intro degree
  refine Q'.eqv_trans _
    (Q'.ofNat (degree + 1) *
      coeff (padd p q) (degree + 1)) _
    (coeff_pderiv (padd p q) degree) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (degree + 1) *
      (coeff p (degree + 1) + coeff q (degree + 1))) _
    (Q'.mul_eqv_congr_left _ _ _
      (coeff_padd (degree + 1) p q)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (degree + 1) * coeff p (degree + 1) +
      Q'.ofNat (degree + 1) * coeff q (degree + 1)) _
    (Q'.mul_add_eqv _ _ _) ?_
  exact Q'.eqv_trans _
    (coeff (pderiv p) degree + coeff (pderiv q) degree) _
    (q_add_congr
      (Q'.eqv_symm (coeff_pderiv p degree))
      (Q'.eqv_symm (coeff_pderiv q degree)))
    (Q'.eqv_symm (coeff_padd degree (pderiv p) (pderiv q)))

/-- Formal differentiation commutes with rational scaling coefficientwise. -/
theorem pderiv_pscale (k : Q') (p : Poly) :
    CoeffEqv (pderiv (pscale k p)) (pscale k (pderiv p)) := by
  intro degree
  refine Q'.eqv_trans _
    (Q'.ofNat (degree + 1) *
      coeff (pscale k p) (degree + 1)) _
    (coeff_pderiv (pscale k p) degree) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (degree + 1) *
      (k * coeff p (degree + 1))) _
    (Q'.mul_eqv_congr_left _ _ _
      (coeff_pscale k p (degree + 1))) ?_
  refine Q'.eqv_trans _
    (k * (Q'.ofNat (degree + 1) * coeff p (degree + 1))) _ ?_ ?_
  · exact Q'.eqv_trans _
      ((Q'.ofNat (degree + 1) * k) * coeff p (degree + 1)) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _
        ((k * Q'.ofNat (degree + 1)) * coeff p (degree + 1)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _))
  · exact Q'.eqv_trans _
      (k * coeff (pderiv p) degree) _
      (Q'.mul_eqv_congr_left k _ _
        (Q'.eqv_symm (coeff_pderiv p degree)))
      (Q'.eqv_symm (coeff_pscale k (pderiv p) degree))

end YMGap.Constructive.QPolyFormalDerivative

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QPolyFormalDerivative.coeff_scaleFrom
#print axioms YMGap.Constructive.QPolyFormalDerivative.coeff_pderiv
#print axioms YMGap.Constructive.QPolyFormalDerivative.coeff_pmul_eqv_cauchyCoeff
#print axioms YMGap.Constructive.QPolyFormalDerivative.leftWeightedCauchy
#print axioms YMGap.Constructive.QPolyFormalDerivative.rightWeightedCauchy
#print axioms YMGap.Constructive.QPolyFormalDerivative.weightedCauchy_split
#print axioms YMGap.Constructive.QPolyFormalDerivative.coeff_pderiv_pmul
#print axioms YMGap.Constructive.QPolyFormalDerivative.coeffEqv_pmul_comm
#print axioms YMGap.Constructive.QPolyFormalDerivative.coeffEqv_pmul_assoc
#print axioms YMGap.Constructive.QPolyFormalDerivative.pderiv_padd
#print axioms YMGap.Constructive.QPolyFormalDerivative.pderiv_pscale
