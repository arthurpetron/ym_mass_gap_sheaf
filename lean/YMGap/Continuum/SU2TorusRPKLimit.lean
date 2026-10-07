/-
# Torus RP (f0): closed-inequality lemmas for the `K → ∞` passage (Q' level; NO limit object)

Nothing here defines a limit of `rpB` in `K`. We state, in Q', that an inequality holding at every truncation `K`
holds for any rational that every truncation approximates within `r K`, up to `2·r K`:

* `closed_le` : `x_K ≤ y_K`, `|x − x_K| ≤ r`, `|y − y_K| ≤ r` ⟹ `x ≤ (y + r) + r`.
* `rp_closed` : `0 ≤ rpB_K F F` for all `K` (`torus_rp_poly`), and `|x − rpB_K F F| ≤ r K` ⟹ `0 ≤ (x + r K) + r K`.
* `cs_closed` : the same for `TorusCS`, with `x = a·a` and `y = b·c` the products of the approximated values.

`RPKCauchy` states the uniform-in-`K` Cauchy bound for `rpB`; it is only defined here. It is PROVED in
`SU2TorusRPKCauchy.rpK_cauchy` at strong coupling (`2·256·β ≤ 1`), with an explicit rate that is not volume-uniform.
-/

import YMGap.Continuum.SU2TorusRPPolyCS
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.SU2TorusRPKLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup)

theorem closed_le {x y xK yK r : Q'} (h : xK ≤ yK) (hx : Q'.abs (x + -xK) ≤ r) (hy : Q'.abs (y + -yK) ≤ r) :
    x ≤ (y + r) + r := by
  have h1 : x ≤ xK + r := ExpNeg.le_add_of_abs_sub_le hx
  have hy' : Q'.abs (yK + -y) ≤ r := Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm yK y)) hy
  have h2 : yK ≤ y + r := ExpNeg.le_add_of_abs_sub_le hy'
  exact Q'.le_trans' _ _ _ h1 (Q'.add_le_add_right _ _ _ (Q'.le_trans' _ _ _ h h2))

variable {M : Nat} (hM : 1 ≤ M) (β : Q')

/-- Target (OPEN): uniform-in-`K` Cauchy bound for `rpB` at rate `r`. -/
def RPKCauchy (F G : RatPoly) (r : Nat → Q') : Prop :=
  ∀ K j : Nat, Q'.abs (rpB hM β (K + j) F G + -rpB hM β K F G) ≤ r K

theorem rp_closed {β : Q'} (hβ : (0 : Q') ≤ β) {F : RatPoly} (hF : PtSup (M := M) F) {x : Q'} {r : Nat → Q'}
    (hr : ∀ K, (0 : Q') ≤ r K) (hx : ∀ K, Q'.abs (x + -rpB hM β K F F) ≤ r K) (K : Nat) : (0 : Q') ≤ (x + r K) + r K := by
  have h0 : Q'.abs ((0 : Q') + -0) ≤ r K := Q'.le_trans' _ _ _ (by decide) (hr K)
  exact Q'.le_trans' _ _ _ (closed_le (YMGap.Continuum.SU2TorusRPPolyCS.torus_rp_poly hM K hβ F hF) h0 (hx K)) (Q'.le_refl' _)

theorem cs_closed {β : Q'} (hβ : (0 : Q') ≤ β) {F G : RatPoly} (hF : PtSup (M := M) F) (hG : PtSup (M := M) G)
    {a b c : Q'} {r : Nat → Q'}
    (ha : ∀ K, Q'.abs (a * a + -(rpB hM β K F G * rpB hM β K F G)) ≤ r K)
    (hbc : ∀ K, Q'.abs (b * c + -(rpB hM β K F F * rpB hM β K G G)) ≤ r K) (K : Nat) :
    a * a ≤ (b * c + r K) + r K :=
  closed_le (YMGap.Continuum.SU2TorusRPPolyCS.torus_cs_poly hM K hβ F G hF hG) (ha K) (hbc K)

end YMGap.Continuum.SU2TorusRPKLimit

#print axioms YMGap.Continuum.SU2TorusRPKLimit.rp_closed
#print axioms YMGap.Continuum.SU2TorusRPKLimit.cs_closed
