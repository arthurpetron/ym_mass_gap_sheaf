/-
Integer-facing wrapper for the constructive `Q'` polynomial normaliser.

`RingNormaliser` proves identities after evaluation in the constructive
rationals.  Evaluating its variables at embedded integers and reflecting the
result back through the denominator-one embedding gives a convenient, fully
constructive decision procedure for polynomial identities in `Int`.
-/

import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.IntRingNormaliser

open YMGap.Constructive
open YMGap.Continuum

abbrev PolyExpr := RingNormaliser.PolyExpr

/-- Integer power using the same association convention as the reflective
normaliser. -/
def intPow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => intPow x n * x

/-- Evaluation of a reflective polynomial expression in `Int`. -/
def eval (rho : Nat → Int) : PolyExpr → Int
  | .const c => c
  | .var i => rho i
  | .add x y => eval rho x + eval rho y
  | .mul x y => eval rho x * eval rho y
  | .neg x => -(eval rho x)
  | .pow x n => intPow (eval rho x) n

private theorem ofInt_neg (x : Int) :
    (-(Q'.ofInt x)).eqv (Q'.ofInt (-x)) := by
  rfl

private theorem qpow_ofInt (x : Int) : ∀ n,
    (RingNormaliser.qpow (Q'.ofInt x) n).eqv
      (Q'.ofInt (intPow x n))
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      exact Q'.eqv_trans _
        (Q'.ofInt (intPow x n) * Q'.ofInt x) _
        (Q'.mul_eqv_congr_right _ _ _ (qpow_ofInt x n))
        (Q'.eqv_symm (RingNormaliser.ofInt_mul (intPow x n) x))

/-- Reflective evaluation commutes with embedding an integer environment in
the constructive rationals. -/
theorem ring_eval_ofInt (rho : Nat → Int) : ∀ e,
    (RingNormaliser.eval (fun i => Q'.ofInt (rho i)) e).eqv
      (Q'.ofInt (eval rho e))
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (eval rho x) +
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.add_eqv_congr_right _ _ _ (ring_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (eval rho x) + Q'.ofInt (eval rho y)) _
          (Q'.add_eqv_congr_left _ _ _ (ring_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_add _ _)))
  | .mul x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (eval rho x) *
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.mul_eqv_congr_right _ _ _ (ring_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (eval rho x) * Q'.ofInt (eval rho y)) _
          (Q'.mul_eqv_congr_left _ _ _ (ring_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_mul _ _)))
  | .neg x => by
      exact Q'.eqv_trans _ (-(Q'.ofInt (eval rho x))) _
        (Q'.neg_eqv_congr _ _ (ring_eval_ofInt rho x))
        (ofInt_neg _)
  | .pow x n => by
      exact Q'.eqv_trans _
        (RingNormaliser.qpow (Q'.ofInt (eval rho x)) n) _
        (RingNormaliser.qpow_eqv_congr (ring_eval_ofInt rho x) n)
        (qpow_ofInt _ n)

/-- Kernel-checked integer polynomial identity obtained from equality of the
two reflected normal forms. -/
theorem poly_identity_of_normal_eq
    (e₁ e₂ : PolyExpr)
    (hn : RingNormaliser.normalize e₁ = RingNormaliser.normalize e₂)
    (rho : Nat → Int) : eval rho e₁ = eval rho e₂ := by
  have h := RingNormaliser.poly_identity_of_normal_eq e₁ e₂ hn
    (fun i => Q'.ofInt (rho i))
  have hl := ring_eval_ofInt rho e₁
  have hr := ring_eval_ofInt rho e₂
  have hi := Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ h hr)
  unfold Q'.eqv at hi
  change eval rho e₁ * 1 = eval rho e₂ * 1 at hi
  simpa using hi

#print axioms intPow
#print axioms eval
#print axioms ring_eval_ofInt
#print axioms poly_identity_of_normal_eq

end YMGap.Continuum.IntRingNormaliser
