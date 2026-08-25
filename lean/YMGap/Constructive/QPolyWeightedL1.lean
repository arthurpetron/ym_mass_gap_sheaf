/-
# Weighted coefficient bounds for constructive rational polynomials

For a low-to-high coefficient list `p`, `weightedL1 rho p` is

    sum_i |p_i| rho^i.

The main theorem proves directly from Horner evaluation that
`|eval p z| <= weightedL1 rho p` whenever `|z| <= rho`.  This is the
constructive coefficient-to-window compiler used by finite analytic
certificates.  It assumes no decidable normalization of `Q'` polynomials.
-/

import YMGap.Constructive.QPoly
import YMGap.Constructive.CRealExp

namespace YMGap.Constructive.QPolyWeightedL1

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly

/-- Weighted coefficient `L1` norm, in Horner order. -/
def weightedL1 (rho : Q') : Poly -> Q'
  | [] => 0
  | c :: cs => Q'.abs c + rho * weightedL1 rho cs

/-- The weighted coefficient norm is nonnegative for a nonnegative radius. -/
theorem weightedL1_nonnegative
    (rho : Q') (hrho : (0 : Q') <= rho) :
    forall p : Poly, (0 : Q') <= weightedL1 rho p
  | [] => Q'.le_refl' 0
  | c :: cs =>
      Q'.zero_le_add (Q'.abs c) (rho * weightedL1 rho cs)
        (Q'.abs_nonneg c)
        (Q'.mul_nonneg rho (weightedL1 rho cs) hrho
          (weightedL1_nonnegative rho hrho cs))

/-- Horner evaluation is bounded by the weighted coefficient norm throughout
the closed radius-`rho` window. -/
theorem abs_eval_le_weightedL1
    {rho z : Q'} (hrho : (0 : Q') <= rho)
    (hz : Q'.abs z <= rho) :
    forall p : Poly, Q'.abs (eval p z) <= weightedL1 rho p
  | [] => by
      change Q'.abs (0 : Q') <= 0
      decide
  | c :: cs => by
      change Q'.abs (c + z * eval cs z) <=
        Q'.abs c + rho * weightedL1 rho cs
      have htail : Q'.abs (z * eval cs z) <=
          rho * weightedL1 rho cs := by
        refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le z (eval cs z)) ?_
        refine Q'.le_trans' _ (rho * Q'.abs (eval cs z)) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_right
            (Q'.abs z) rho (Q'.abs (eval cs z)) hz
            (Q'.abs_nonneg (eval cs z))
        · exact Q'.mul_le_mul_of_nonneg_left
            (Q'.abs (eval cs z)) (weightedL1 rho cs) rho
            (abs_eval_le_weightedL1 hrho hz cs) hrho
      exact Q'.le_trans' _ _ _ (ExpNeg.abs_add_le c (z * eval cs z))
        (Q'.add_le_add_left (Q'.abs c)
          (Q'.abs (z * eval cs z)) (rho * weightedL1 rho cs) htail)

/-- Weighted norm of polynomial addition is subadditive. -/
theorem weightedL1_padd_le
    (rho : Q') (hrho : (0 : Q') <= rho) :
    forall p q : Poly,
      weightedL1 rho (padd p q) <=
        weightedL1 rho p + weightedL1 rho q
  | [], q =>
      Q'.le_of_eqv (Q'.eqv_symm (q_zero_add_eqv (weightedL1 rho q)))
  | a :: p, [] =>
      Q'.le_of_eqv
        (Q'.eqv_symm (q_add_zero_eqv (weightedL1 rho (a :: p))))
  | a :: p, b :: q => by
      change Q'.abs (a + b) + rho * weightedL1 rho (padd p q) <=
        (Q'.abs a + rho * weightedL1 rho p) +
          (Q'.abs b + rho * weightedL1 rho q)
      have htail : rho * weightedL1 rho (padd p q) <=
          rho * (weightedL1 rho p + weightedL1 rho q) :=
        Q'.mul_le_mul_of_nonneg_left _ _ rho
          (weightedL1_padd_le rho hrho p q) hrho
      have hsum : Q'.abs (a + b) +
          rho * weightedL1 rho (padd p q) <=
          (Q'.abs a + Q'.abs b) +
            rho * (weightedL1 rho p + weightedL1 rho q) :=
        Q'.add_le_add (ExpNeg.abs_add_le a b) htail
      have hregroup :
          ((Q'.abs a + Q'.abs b) +
              rho * (weightedL1 rho p + weightedL1 rho q)).eqv
            ((Q'.abs a + rho * weightedL1 rho p) +
              (Q'.abs b + rho * weightedL1 rho q)) := by
        refine Q'.eqv_trans _
          ((Q'.abs a + Q'.abs b) +
            (rho * weightedL1 rho p + rho * weightedL1 rho q)) _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.mul_add_eqv rho
              (weightedL1 rho p) (weightedL1 rho q))) ?_
        exact q_interchange (Q'.abs a) (Q'.abs b)
          (rho * weightedL1 rho p) (rho * weightedL1 rho q)
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hregroup)

/-- Weighted norm of scalar multiplication is bounded by the scalar absolute
value times the original norm. -/
theorem weightedL1_pscale_le
    (rho : Q') (hrho : (0 : Q') <= rho) (k : Q') :
    forall p : Poly,
      weightedL1 rho (pscale k p) <=
        Q'.abs k * weightedL1 rho p
  | [] =>
      Q'.le_of_eqv (Q'.eqv_symm (q_mul_zero (Q'.abs k)))
  | c :: cs => by
      change Q'.abs (k * c) + rho * weightedL1 rho (pscale k cs) <=
        Q'.abs k * (Q'.abs c + rho * weightedL1 rho cs)
      have htail : rho * weightedL1 rho (pscale k cs) <=
          rho * (Q'.abs k * weightedL1 rho cs) :=
        Q'.mul_le_mul_of_nonneg_left _ _ rho
          (weightedL1_pscale_le rho hrho k cs) hrho
      have hsum : Q'.abs (k * c) +
          rho * weightedL1 rho (pscale k cs) <=
          (Q'.abs k * Q'.abs c) +
            rho * (Q'.abs k * weightedL1 rho cs) :=
        Q'.add_le_add (ExpNeg.abs_mul_le k c) htail
      have hregroup :
          ((Q'.abs k * Q'.abs c) +
              rho * (Q'.abs k * weightedL1 rho cs)).eqv
            (Q'.abs k * (Q'.abs c + rho * weightedL1 rho cs)) := by
        refine Q'.eqv_trans _
          ((Q'.abs k * Q'.abs c) +
            Q'.abs k * (rho * weightedL1 rho cs)) _
          (Q'.add_eqv_congr_left _ _ _ ?_) ?_
        · refine Q'.eqv_trans _ ((rho * Q'.abs k) * weightedL1 rho cs) _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv rho (Q'.abs k)
                (weightedL1 rho cs))) ?_
          refine Q'.eqv_trans _ ((Q'.abs k * rho) * weightedL1 rho cs) _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv rho (Q'.abs k))) ?_
          exact Q'.mul_assoc_eqv (Q'.abs k) rho
            (weightedL1 rho cs)
        · exact Q'.eqv_symm
            (Q'.mul_add_eqv (Q'.abs k) (Q'.abs c)
              (rho * weightedL1 rho cs))
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hregroup)

/-- A leading zero only shifts the weighted norm by one factor of `rho`. -/
theorem weightedL1_zero_cons_eqv (rho : Q') (p : Poly) :
    (weightedL1 rho ((0 : Q') :: p)).eqv
      (rho * weightedL1 rho p) := by
  change (Q'.abs (0 : Q') + rho * weightedL1 rho p).eqv
    (rho * weightedL1 rho p)
  have hzero : (Q'.abs (0 : Q')).eqv 0 := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 _ hzero)
    (q_zero_add_eqv (rho * weightedL1 rho p))

/-- The weighted coefficient norm is submultiplicative. -/
theorem weightedL1_pmul_le
    (rho : Q') (hrho : (0 : Q') <= rho) :
    forall p q : Poly,
      weightedL1 rho (pmul p q) <=
        weightedL1 rho p * weightedL1 rho q
  | [], q =>
      Q'.le_of_eqv (Q'.eqv_symm (q_zero_mul (weightedL1 rho q)))
  | a :: p, q => by
      let nq : Q' := weightedL1 rho q
      let np : Q' := weightedL1 rho p
      let productTail : Q' := weightedL1 rho (pmul p q)
      let scaledHead : Q' := weightedL1 rho (pscale a q)
      have hadd : weightedL1 rho
          (padd (pscale a q) ((0 : Q') :: pmul p q)) <=
          scaledHead + weightedL1 rho ((0 : Q') :: pmul p q) :=
        weightedL1_padd_le rho hrho _ _
      have hhead : scaledHead <= Q'.abs a * nq :=
        weightedL1_pscale_le rho hrho a q
      have hzero :
          (weightedL1 rho ((0 : Q') :: pmul p q)).eqv
            (rho * productTail) :=
        weightedL1_zero_cons_eqv rho (pmul p q)
      have hfirst : weightedL1 rho (pmul (a :: p) q) <=
          (Q'.abs a * nq) + rho * productTail := by
        exact Q'.le_trans' _ _ _ hadd
          (Q'.add_le_add hhead (Q'.le_of_eqv hzero))
      have hind : productTail <= np * nq :=
        weightedL1_pmul_le rho hrho p q
      have hsecond : (Q'.abs a * nq) + rho * productTail <=
          (Q'.abs a * nq) + rho * (np * nq) :=
        Q'.add_le_add_left (Q'.abs a * nq)
          (rho * productTail) (rho * (np * nq))
          (Q'.mul_le_mul_of_nonneg_left _ _ rho hind hrho)
      have hregroup :
          ((Q'.abs a * nq) + rho * (np * nq)).eqv
            ((Q'.abs a + rho * np) * nq) := by
        refine Q'.eqv_trans _
          ((Q'.abs a * nq) + (rho * np) * nq) _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv rho np nq))) ?_
        exact Q'.eqv_symm
          (Q'.add_mul_eqv (Q'.abs a) (rho * np) nq)
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hregroup))

/-- Polynomial negation does not increase the weighted norm. -/
theorem weightedL1_pneg_le
    (rho : Q') (hrho : (0 : Q') <= rho) (p : Poly) :
    weightedL1 rho (pneg p) <= weightedL1 rho p := by
  have hscale := weightedL1_pscale_le rho hrho (-(1 : Q')) p
  have habs : (Q'.abs (-(1 : Q'))).eqv (1 : Q') := by decide
  have hcollapse :
      (Q'.abs (-(1 : Q')) * weightedL1 rho p).eqv
        (weightedL1 rho p) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 1 _ habs)
      (Q'.one_mul_eqv (weightedL1 rho p))
  exact Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hcollapse)

/-- Polynomial subtraction is bounded by the sum of the two weighted norms. -/
theorem weightedL1_psub_le
    (rho : Q') (hrho : (0 : Q') <= rho) (p q : Poly) :
    weightedL1 rho (psub p q) <=
      weightedL1 rho p + weightedL1 rho q := by
  have hadd := weightedL1_padd_le rho hrho p (pneg q)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.add_le_add_left (weightedL1 rho p)
      (weightedL1 rho (pneg q)) (weightedL1 rho q)
      (weightedL1_pneg_le rho hrho q))

/-- Boolean check that the first `count` coefficients vanish up to
`Q'.eqv`.  A polynomial shorter than the requested prefix is implicitly
zero-padded. -/
def zeroPrefixB : Nat -> Poly -> Bool
  | 0, _ => true
  | _ + 1, [] => true
  | count + 1, c :: cs => decide (c.eqv 0) && zeroPrefixB count cs

def zeroPrefix (count : Nat) (p : Poly) : Prop :=
  zeroPrefixB count p = true

instance zeroPrefixDecidable (count : Nat) (p : Poly) :
    Decidable (zeroPrefix count p) :=
  inferInstanceAs (Decidable (zeroPrefixB count p = true))

/-- Vanishing at zero proves that the constant coefficient vanishes.  This is
the first nontrivial zero-prefix certificate, phrased through polynomial
semantics so downstream formal identities need not inspect coefficient-list
implementations. -/
theorem zeroPrefix_one_of_eval_zero
    (p : Poly) (hzero : (eval p 0).eqv 0) :
    zeroPrefix 1 p := by
  cases p with
  | nil => rfl
  | cons c cs =>
      have heval : (eval (c :: cs) 0).eqv c := by
        show (c + (0 : Q') * eval cs 0).eqv c
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left c _ 0 (q_zero_mul (eval cs 0)))
          (q_add_zero_eqv c)
      have hc : c.eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm heval) hzero
      unfold zeroPrefix zeroPrefixB
      rw [show decide (c.eqv 0) = true from decide_eq_true hc]
      rfl

/-- A checked zero prefix factors the weighted norm into the corresponding
power of the radius times the norm of the remaining coefficient tail. -/
theorem weightedL1_eqv_pow_mul_drop_of_zeroPrefix
    (rho : Q') : forall (count : Nat) (p : Poly),
    zeroPrefix count p ->
    (weightedL1 rho p).eqv
      ((rho ^ count) * weightedL1 rho (List.drop count p))
  | 0, p, _ => Q'.eqv_symm (Q'.one_mul_eqv (weightedL1 rho p))
  | count + 1, [], _ => by
      change (0 : Q').eqv ((rho ^ (count + 1)) * 0)
      exact Q'.eqv_symm (q_mul_zero (rho ^ (count + 1)))
  | count + 1, c :: cs, h => by
      have hparts := h
      unfold zeroPrefix zeroPrefixB at hparts
      rw [Bool.and_eq_true] at hparts
      have hc : c.eqv 0 := of_decide_eq_true hparts.1
      have habs : (Q'.abs c).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hc) (by decide)
      have hhead :
          (Q'.abs c + rho * weightedL1 rho cs).eqv
            (rho * weightedL1 rho cs) :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 _ habs)
          (q_zero_add_eqv (rho * weightedL1 rho cs))
      have htail := weightedL1_eqv_pow_mul_drop_of_zeroPrefix
        rho count cs hparts.2
      refine Q'.eqv_trans _ (rho * weightedL1 rho cs) _ hhead ?_
      refine Q'.eqv_trans _
        (rho * ((rho ^ count) * weightedL1 rho (List.drop count cs))) _
        (Q'.mul_eqv_congr_left rho _ _ htail) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv rho (rho ^ count)
          (weightedL1 rho (List.drop count cs)))

end YMGap.Constructive.QPolyWeightedL1

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_nonnegative
#print axioms
  YMGap.Constructive.QPolyWeightedL1.abs_eval_le_weightedL1
#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_padd_le
#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_pscale_le
#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_pmul_le
#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_psub_le
#print axioms
  YMGap.Constructive.QPolyWeightedL1.zeroPrefix_one_of_eval_zero
#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_eqv_pow_mul_drop_of_zeroPrefix
