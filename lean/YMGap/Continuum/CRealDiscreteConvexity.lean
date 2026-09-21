/-
# Discrete convexity for constructive-real sequences

A nonnegative second difference makes the successive drops of a `CReal`
sequence decrease.  Finite telescoping then bounds an arbitrary endpoint drop
by the number of steps times the first drop.  No sign condition on that first
drop is used.

This is only generic ordered additive algebra.  It introduces no carrier,
measure, positivity assumption, or uniformity claim.

# Axiom gate

The public declarations below use only the existing constructive `CReal`
equivalence and eventual order.  No classical axiom, `sorry`, or new axiom is
introduced.
-/

import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.CRealDiscreteConvexity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

/-- The drop from index `n` to index `n+1`. -/
def firstDrop (r : Nat → CReal) (n : Nat) : CReal :=
  sub (r n) (r (n+1))

/-- The displayed second difference, oriented as `firstDrop n - firstDrop (n+1)`. -/
def curvature (r : Nat → CReal) (n : Nat) : CReal :=
  add (sub (r n) (r (n+1))) (sub (r (n+2)) (r (n+1)))

private theorem qring (left right : PolyExpr)
    (h : normalize left = normalize right) (environment : Nat → Q') :
    (eval environment left).eqv (eval environment right) :=
  poly_identity_of_normal_eq left right h environment

private theorem curvature_drop_sub (r : Nat → CReal) (n : Nat) :
    Equiv (curvature r n) (sub (firstDrop r n) (firstDrop r (n+1))) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 2) (.neg (.var 1))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (by decide)
      (fun
        | 0 => (r n).approx k
        | 1 => (r (n+1)).approx k
        | _ => (r (n+2)).approx k))

private theorem czero_add_equiv (x : CReal) : Equiv (add czero x) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring (.add (.const 0) (.var 0)) (.var 0) (by decide)
      (fun _ => x.approx k))

private theorem sub_add_cancel_equiv (x y : CReal) :
    Equiv (add (sub x y) y) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => x.approx k | _ => y.approx k))

private theorem endpoint_step (r : Nat → CReal) (n : Nat) :
    Equiv (sub (r 0) (r (n+1)))
      (add (sub (r 0) (r n)) (firstDrop r n)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (by decide)
      (fun
        | 0 => (r 0).approx k
        | 1 => (r n).approx k
        | _ => (r (n+1)).approx k))

private theorem endpoint_zero (r : Nat → CReal) :
    Equiv (sub (r 0) (r 0)) czero :=
  sub_self_eqv_zero (r 0)

private theorem zero_scale (x : CReal) :
    Equiv (mul (ofQ' (Q'.ofNat 0)) x) czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring (.mul (.const 0) (.var 0)) (.const 0) (by decide)
      (fun _ => x.approx k))

private theorem scale_succ (n : Nat) (x : CReal) :
    Equiv (add (mul (ofQ' (Q'.ofNat n)) x) x)
      (mul (ofQ' (Q'.ofNat (n+1))) x) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _
      (qring
        (.add (.mul (.var 0) (.var 1)) (.var 1))
        (.mul (.add (.var 0) (.const 1)) (.var 1))
        (by decide)
        (fun | 0 => Q'.ofNat n | _ => x.approx k))
      (Q'.mul_eqv_congr_right _ _ (x.approx k)
        (Q'.eqv_symm (Q'.ofNat_add_eqv n 1))))

private theorem nonnegative_sub_le {x y : CReal}
    (h : leEv (ofQ' 0) (sub x y)) : leEv y x := by
  have hsum := leEv_add h (leEv_refl y)
  exact (leEv_congr (czero_add_equiv y) (sub_add_cancel_equiv x y)).mp hsum

/-- Nonnegative second differences make successive drops decrease. -/
theorem firstDrop_antitone (r : Nat → CReal)
    (hc : ∀ n, leEv (ofQ' 0) (curvature r n)) (n : Nat) :
    leEv (firstDrop r (n+1)) (firstDrop r n) :=
  nonnegative_sub_le
    (leEv_trans (leEv_refl (ofQ' 0))
      ((leEv_congr (Equiv.refl _) (curvature_drop_sub r n)).mp (hc n)))

/-- Every later drop is bounded by the first one; no sign hypothesis is used. -/
theorem firstDrop_le_first (r : Nat → CReal)
    (hc : ∀ n, leEv (ofQ' 0) (curvature r n)) :
    ∀ n, leEv (firstDrop r n) (firstDrop r 0)
  | 0 => leEv_refl _
  | n+1 => leEv_trans (firstDrop_antitone r hc n) (firstDrop_le_first r hc n)

/-- A discretely convex sequence has at most linear endpoint drop.

The curvature hypothesis is exactly
`0 ≤ (r n-r(n+1)) + (r(n+2)-r(n+1))`.  The conclusion does not assume
that the first drop is nonnegative. -/
theorem endpoint_drop_le_nat_mul_first (r : Nat → CReal)
    (hc : ∀ n, leEv (ofQ' 0)
      (add (sub (r n) (r (n+1))) (sub (r (n+2)) (r (n+1))))) :
    ∀ n, leEv (sub (r 0) (r n))
      (mul (ofQ' (Q'.ofNat n)) (sub (r 0) (r 1)))
  | 0 =>
      (leEv_congr (endpoint_zero r) (zero_scale (firstDrop r 0))).mpr
        (leEv_refl czero)
  | n+1 => by
      have hsum := leEv_add (endpoint_drop_le_nat_mul_first r hc n)
        (firstDrop_le_first r hc n)
      exact (leEv_congr (endpoint_step r n) (scale_succ n (firstDrop r 0)).symm).mpr hsum

end YMGap.Continuum.CRealDiscreteConvexity

#print axioms YMGap.Continuum.CRealDiscreteConvexity.firstDrop
#print axioms YMGap.Continuum.CRealDiscreteConvexity.curvature
#print axioms YMGap.Continuum.CRealDiscreteConvexity.firstDrop_antitone
#print axioms YMGap.Continuum.CRealDiscreteConvexity.firstDrop_le_first
#print axioms YMGap.Continuum.CRealDiscreteConvexity.endpoint_drop_le_nat_mul_first
