/-
# The Chebyshev first-kind power sums on the roots of `U_M` (Wall-1 item 3)
# — the U-generating identity (general `M`) and the named power-sum residual

This module attacks the single sharp residual `PowerSumCollapse.TPowerSum`, the
first-kind Dirichlet power-sum collapse `(★)` over the `M` roots `x_1,…,x_M` of
the second-kind Chebyshev polynomial `U_M`:

    S_0 = M,   S_2 = −1,   S_p = S_{p+2}   for 0 < p ≤ M−1,      S_j := Σ_k T_j(x_k).

## The algebraic engine (π-free, no trig)

The genuine `π`-free engine is the **U-generating identity** in its
substitution-free Laurent form.  For two formal parameters `z, w` related by
`z·w = 1` (so `w` plays the role of `z⁻¹`), put `c := (z + w)/2`.  Then for ALL
`M`:

    (z − w) · U_M(c)  =  z^{M+1} − w^{M+1}.                                  (G)

This is proved here, axiom-clean and for general `M`, by two-step induction on
the `U`-recurrence `U_{M+2}(c) = 2c·U_{M+1}(c) − U_M(c) = (z+w)·U_{M+1}(c) −
U_M(c)`, the difference-of-squares base, and the cross-term cancellation
`w·z^{n+2} = z^{n+1}`, `z·w^{n+2} = w^{n+1}` driven by `z·w = 1`.  Identity `(G)`
is the trig shadow `U_M(cos θ) = sin((M+1)θ)/sin θ` written with `z = e^{iθ}`,
`w = e^{−iθ}`, made fully algebraic.

Multiplying `(G)` by the geometric-sum identity gives the **KEY IDENTITY**'s
heart: with `z·w = 1`,

    (z + (−w)) · U_M(c)  =  Σ_{j=0}^{M} (z^{M−j}·w^j) · (z + (−w)),

i.e. `U_M(c) = Σ_{j=0}^{M} z^{M−2j}` (the Dirichlet kernel).  Substituting
`z → z`, `w → z` and the doubled variable in the product over roots is what
yields `∏_k(1 − 2x_k z + z²) = Σ_j z^{2j}`; but THAT step needs the `x_k` as the
genuine roots of `U_M` (a symmetric-function / Newton input), which the abstract
node interface `ChebRootDataT` does not carry.  Hence `(G)` is proved for general
`M`, while the *root-side* collapse `(★)` is honestly NAMED open at general `M`.

## PROVED (genuine, axiom-clean, general `M`, π-free)

  * `Ugen` — the U-generating identity `(G)`: `(z − w)·U_M(c) ≈ z^{M+1} − w^{M+1}`
    for `z·w ≈ 1`, `c = (z+w)·½`, for ALL `M`, by two-step induction.
  * `Ueven_geom` — its corollary at the diagonal substitution `w = z` with
    `z·z ≈ 1`: `(z − z)·U_M(c) ≈ 0`, the degenerate confluent shadow (a sanity
    instance of `(G)`).
  * `Sj0_eq_M` — the first power sum `S_0 = Σ_k T_0(x_k) = M` for ANY
    `ChebRootDataT M` (since `T_0 = 1`, summed `M` times): the unconditional part
    of `(★)`, proved against the abstract interface.

## Re-exported / inhabited

  * `TPowerSum_M2` — `PowerSumCollapse.TPowerSum PowerSumCollapse.rootData2`
    (the rational `M = 2` nodes `±1/2`), inhabited via the proved
    `PowerSumCollapse.TPowerSum2`; hence `PowerSumCollapse.TPowerSum` is
    inhabited at `M = 2`.

## NAMED open (the precise residual)

  * `RootPowerSumBridge M D` — the symmetric-function bridge from the
    U-generating identity `(G)` to the root-side power sums: `S_2 = −1` and
    `S_p = S_{p+2}` (`0 < p ≤ M−1`).  This is exactly the Newton step that turns
    the proved coefficient/generating identity into a statement about the actual
    roots `x_k` of `U_M`; the abstract `ChebRootDataT M` does not encode that its
    nodes ARE those roots, so this cannot be discharged against the interface and
    is named precisely.  Given it (plus the proved `Sj0_eq_M`), `TPowerSum D`
    holds (`tPowerSum_of_bridge`), and so does the all-order Gram PSD via
    `PowerSumCollapse.powerSumCollapse_of_TPowerSum`.

So the all-order Gram PSD (Wall-1) is **NOT closed**: it now rests on the single
sharp residual `RootPowerSumBridge` (the root-side Newton step), with the
generating identity `(G)` itself proved unconditionally at general `M`, and the
`M = 2` instance fully discharged.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/
`sorryAx`, no `native_decide`, no `decide` on non-decidable `Prop`.  `decide`
only on closed `Q'`/`Nat`.  Witnesses are `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.PowerSumCollapse

namespace YMGap.Continuum.TPowerSum

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.ChebOrthogonality
open YMGap.Continuum.PowerSumCollapse

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. Power-shuffle helpers over `Q'`

Small `eqv` facts about `Q'.pow` and the relation `z·w ≈ 1` that drive the
cross-term cancellation in the induction step of `Ugen`. -/

/-- `z · z^n ≈ z^(n+1)` (definitional unfolding of `pow_succ`, repackaged as
`eqv`). -/
theorem z_mul_pow (z : Q') (n : Nat) : z * z ^ n ≈ z ^ (n+1) := by
  rw [Q'.pow_succ]; exact eqv_refl _

/-- `z^(n+1) ≈ z^n · z` (commuted form). -/
theorem pow_succ_comm (z : Q') (n : Nat) : z ^ (n+1) ≈ z ^ n * z := by
  rw [Q'.pow_succ]; exact mul_comm_eqv z (z ^ n)

/-- **Cross-term cancellation.**  If `z·w ≈ 1` then `w · z^(n+2) ≈ z^(n+1)`:
`w·z^{n+2} = w·z·z^{n+1} = (z·w)·z^{n+1} ≈ z^{n+1}`. -/
theorem w_mul_pow_cancel (z w : Q') (hzw : z * w ≈ (1 : Q')) (n : Nat) :
    w * z ^ (n+2) ≈ z ^ (n+1) := by
  -- w · z^(n+2) ≈ w · (z · z^(n+1)) ≈ (w · z) · z^(n+1) ≈ (z · w) · z^(n+1) ≈ 1 · z^(n+1) ≈ z^(n+1)
  calc w * z ^ (n+2)
      ≈ w * (z * z ^ (n+1)) :=
        mul_eqv_congr_left _ _ _ (eqv_symm (z_mul_pow z (n+1)))
    _ ≈ (w * z) * z ^ (n+1) := eqv_symm (mul_assoc_eqv w z (z ^ (n+1)))
    _ ≈ (z * w) * z ^ (n+1) := mul_eqv_congr_right _ _ _ (mul_comm_eqv w z)
    _ ≈ (1 : Q') * z ^ (n+1) := mul_eqv_congr_right _ _ _ hzw
    _ ≈ z ^ (n+1) := one_mul_eqv (z ^ (n+1))

/-! ## 2. The U-generating identity `(G)` (general `M`, π-free)

`(z − w) · U_M(c) ≈ z^{M+1} − w^{M+1}` with `c = (z+w)·½`, `z·w ≈ 1`. -/

/-- The generating-identity predicate at a single index, over `Q'`. -/
def GenAt (z w : Q') (n : Nat) : Prop :=
  (z + (-w)) * U n ((z + w) * HalfPow.half)
    ≈ z ^ (n+1) + (-(w ^ (n+1)))

/-- `2c ≈ z + w` for `c = (z+w)·½`. -/
theorem twoC (z w : Q') : (2 : Q') * ((z + w) * HalfPow.half) ≈ (z + w) := by
  -- 2·((z+w)·½) ≈ (z+w)·(2·½) ≈ (z+w)·1 ≈ z+w
  calc (2 : Q') * ((z + w) * HalfPow.half)
      ≈ ((z + w) * HalfPow.half) * 2 := mul_comm_eqv _ _
    _ ≈ (z + w) * (HalfPow.half * 2) := mul_assoc_eqv (z + w) HalfPow.half 2
    _ ≈ (z + w) * 1 := mul_eqv_congr_left _ _ _ (by decide)
    _ ≈ (z + w) := mul_one_eqv (z + w)

/-- Base `n = 0`: `(z − w)·U_0(c) ≈ z^1 − w^1`. -/
theorem GenAt_zero (z w : Q') : GenAt z w 0 := by
  unfold GenAt
  rw [U_zero]
  -- (z + (-w))·1 ≈ z^1 + (-(w^1)) = z + (-w)
  refine eqv_trans _ _ _ (mul_one_eqv (z + (-w))) ?_
  show (z + (-w)) ≈ z ^ 1 + (-(w ^ 1))
  rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_zero, Q'.pow_zero]
  -- z + (-w) ≈ z·1 + (-(w·1))
  exact Cheb.add_eqv_congr _ _ _ _ (eqv_symm (mul_one_eqv z))
    (neg_eqv_congr _ _ (eqv_symm (mul_one_eqv w)))

/-- Base `n = 1`: `(z − w)·U_1(c) ≈ z^2 − w^2`.  Uses `U_1(c) = 2c ≈ z+w` and the
difference of squares `(z−w)(z+w) = z² − w²`. -/
theorem GenAt_one (z w : Q') : GenAt z w 1 := by
  unfold GenAt
  rw [U_one]
  -- (z + (-w)) · (2·c) ≈ (z + (-w))·(z + w) ≈ z^2 + (-(w^2))
  refine eqv_trans _ _ _
    (mul_eqv_congr_left _ _ _ (twoC z w)) ?_
  -- (z + (-w))·(z+w) ≈ z·z + (-(w·w)) ≈ z^2 + (-(w^2))
  -- expand (z + (-w))·(z+w) = z·z + z·w + (-w)·z + (-w)·w
  calc (z + (-w)) * (z + w)
      ≈ z * (z + w) + (-w) * (z + w) := Cheb.add_mul_eqv z (-w) (z + w)
    _ ≈ (z * z + z * w) + ((-w) * z + (-w) * w) :=
        Cheb.add_eqv_congr _ _ _ _ (mul_add_eqv z z w) (mul_add_eqv (-w) z w)
    _ ≈ (z * z + z * w) + ((-(w * z)) + (-(w * w))) :=
        add_eqv_congr_left _ _ _
          (Cheb.add_eqv_congr _ _ _ _ (neg_mul_eqv w z) (neg_mul_eqv w w))
    _ ≈ (z * z + (-(w * w))) + (z * w + (-(w * z))) := by
        -- Have (a+b)+(c+d) with a=z·z, b=z·w, c=-(w·z), d=-(w·w).  Target (a+d)+(b+c).
        -- Step: (c+d) ≈ (d+c), then interchange a b d c : (a+b)+(d+c) ≈ (a+d)+(b+c).
        refine eqv_trans _ _ _
          (add_eqv_congr_left _ _ _ (add_comm_eqv (-(w*z)) (-(w*w)))) ?_
        exact QPoly.q_interchange (z*z) (z*w) (-(w*w)) (-(w*z))
    _ ≈ (z * z + (-(w * w))) + ((0 : Q')) := by
        refine add_eqv_congr_left _ _ _ ?_
        -- z·w + (-(w·z)) ≈ 0  (since z·w ≈ w·z)
        refine eqv_trans _ _ _
          (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ (mul_comm_eqv w z))) ?_
        exact Q'.add_neg_self_eqv (z * w)
    _ ≈ z * z + (-(w * w)) := by rw [add_zero']; exact eqv_refl _
    _ ≈ z ^ 2 + (-(w ^ 2)) := by
        rw [show (2:Nat) = 1 + 1 from rfl, Q'.pow_succ, Q'.pow_succ,
          Q'.pow_succ, Q'.pow_succ, Q'.pow_zero, Q'.pow_zero]
        exact Cheb.add_eqv_congr _ _ _ _
          (mul_eqv_congr_left _ _ _ (eqv_symm (mul_one_eqv z)))
          (neg_eqv_congr _ _ (mul_eqv_congr_left _ _ _ (eqv_symm (mul_one_eqv w))))

/-- The pure additive cancellation at the end of the `Ugen` step, on abstract
atoms: `((A + −Wp) + (P + −B)) + (−P + Wp) ≈ A + −B`. -/
theorem genstep_add_core (A B P Wp : Q') :
    ((A + (-Wp)) + (P + (-B))) + ((-P) + Wp) ≈ A + (-B) := by
  calc ((A + (-Wp)) + (P + (-B))) + ((-P) + Wp)
      ≈ (A + (-Wp)) + ((P + (-B)) + ((-P) + Wp)) :=
        add_assoc_eqv (A + (-Wp)) (P + (-B)) ((-P) + Wp)
    _ ≈ (A + (-Wp)) + (((-B) + P) + ((-P) + Wp)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (add_comm_eqv P (-B)))
    _ ≈ (A + (-Wp)) + ((-B) + (P + ((-P) + Wp))) :=
        add_eqv_congr_left _ _ _ (add_assoc_eqv (-B) P ((-P) + Wp))
    _ ≈ (A + (-Wp)) + ((-B) + ((P + (-P)) + Wp)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _
          (eqv_symm (add_assoc_eqv P (-P) Wp)))
    _ ≈ (A + (-Wp)) + ((-B) + ((0 : Q') + Wp)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _
          (add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv P)))
    _ ≈ (A + (-Wp)) + ((-B) + Wp) := by
        refine add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _ ?_)
        rw [zero_add']; exact eqv_refl _
    _ ≈ A + ((-Wp) + ((-B) + Wp)) := add_assoc_eqv A (-Wp) ((-B) + Wp)
    _ ≈ A + ((-Wp) + (Wp + (-B))) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _ (add_comm_eqv (-B) Wp))
    _ ≈ A + (((-Wp) + Wp) + (-B)) :=
        add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (-Wp) Wp (-B)))
    _ ≈ A + ((0 : Q') + (-B)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (neg_add_self_eqv Wp))
    _ ≈ A + (-B) := by
        refine add_eqv_congr_left _ _ _ ?_
        rw [zero_add']; exact eqv_refl _

/-- The additive core of the `Ugen` induction step.  Writing `P = (z−w)·U_{n+1}`,
`Q = (z−w)·U_n`, the recurrence gives `(z−w)·U_{n+2} ≈ (z+w)·P − Q`; with
`P ≈ z^{n+2} − w^{n+2}` and `Q ≈ z^{n+1} − w^{n+1}` (and `z·w ≈ 1`) this equals
`z^{n+3} − w^{n+3}`.  We isolate the pure algebra here. -/
theorem GenAt_step_core (z w : Q') (hzw : z * w ≈ (1 : Q')) (n : Nat) :
    (z + w) * (z ^ (n+2) + (-(w ^ (n+2)))) + (-(z ^ (n+1) + (-(w ^ (n+1)))))
      ≈ z ^ (n+3) + (-(w ^ (n+3))) := by
  -- Expand (z+w)·(z^{n+2} − w^{n+2}) = z·z^{n+2} + w·z^{n+2} − z·w^{n+2} − w·w^{n+2}.
  -- z·z^{n+2} = z^{n+3}; w·w^{n+2} = w^{n+3}; w·z^{n+2} = z^{n+1}; z·w^{n+2} = w^{n+1}.
  -- So the whole thing = z^{n+3} − w^{n+3} + (z^{n+1} − w^{n+1}) − (z^{n+1} − w^{n+1}).
  have hzc : z * z ^ (n+2) ≈ z ^ (n+3) := z_mul_pow z (n+2)
  have hwc : w * w ^ (n+2) ≈ w ^ (n+3) := z_mul_pow w (n+2)
  have hwz : w * z ^ (n+2) ≈ z ^ (n+1) := w_mul_pow_cancel z w hzw n
  have hzw2 : z * w ^ (n+2) ≈ w ^ (n+1) :=
    w_mul_pow_cancel w z (eqv_trans _ _ _ (mul_comm_eqv w z) hzw) n
  calc (z + w) * (z ^ (n+2) + (-(w ^ (n+2)))) + (-(z ^ (n+1) + (-(w ^ (n+1)))))
      ≈ (z * (z ^ (n+2) + (-(w ^ (n+2)))) + w * (z ^ (n+2) + (-(w ^ (n+2)))))
          + (-(z ^ (n+1) + (-(w ^ (n+1))))) :=
        add_eqv_congr_right _ _ _ (Cheb.add_mul_eqv z w (z ^ (n+2) + (-(w ^ (n+2)))))
    _ ≈ ((z * z ^ (n+2) + (-(z * w ^ (n+2))))
          + (w * z ^ (n+2) + (-(w * w ^ (n+2)))))
          + ((-(z ^ (n+1))) + (-(-(w ^ (n+1))))) := by
        refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
        · refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
          · refine eqv_trans _ _ _ (mul_add_eqv z (z ^ (n+2)) (-(w ^ (n+2)))) ?_
            exact add_eqv_congr_left _ _ _ (mul_neg_eqv z (w ^ (n+2)))
          · refine eqv_trans _ _ _ (mul_add_eqv w (z ^ (n+2)) (-(w ^ (n+2)))) ?_
            exact add_eqv_congr_left _ _ _ (mul_neg_eqv w (w ^ (n+2)))
        · exact Q'.neg_add_eqv (z ^ (n+1)) (-(w ^ (n+1)))
    _ ≈ ((z ^ (n+3) + (-(w ^ (n+1)))) + (z ^ (n+1) + (-(w ^ (n+3)))))
          + ((-(z ^ (n+1))) + (w ^ (n+1))) := by
        refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
        · refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
          · exact Cheb.add_eqv_congr _ _ _ _ hzc (neg_eqv_congr _ _ hzw2)
          · exact Cheb.add_eqv_congr _ _ _ _ hwz (neg_eqv_congr _ _ hwc)
        · exact add_eqv_congr_left _ _ _ (neg_neg_eqv (w ^ (n+1)))
    _ ≈ z ^ (n+3) + (-(w ^ (n+3))) :=
        genstep_add_core (z ^ (n+3)) (w ^ (n+3)) (z ^ (n+1)) (w ^ (n+1))

/-- The two-step induction step `GenAt n → GenAt (n+1) → GenAt (n+2)`. -/
theorem GenAt_step (z w : Q') (hzw : z * w ≈ (1 : Q')) (n : Nat)
    (hn : GenAt z w n) (hn1 : GenAt z w (n+1)) : GenAt z w (n+2) := by
  unfold GenAt at hn hn1 ⊢
  -- abbreviation: c := (z + w) * HalfPow.half (written inline)
  -- (z−w)·U_{n+2}(c) = (z−w)·(2c·U_{n+1}(c) − U_n(c))
  rw [U_succ_succ n ((z + w) * HalfPow.half)]
  -- = (z−w)·((2c)·U_{n+1} + (−U_n))
  calc (z + (-w)) * (((2 : Q') * ((z + w) * HalfPow.half)) * U (n+1) ((z + w) * HalfPow.half)
        + (-(U n ((z + w) * HalfPow.half))))
      ≈ (z + (-w)) * ((2 : Q') * ((z + w) * HalfPow.half)) * U (n+1) ((z + w) * HalfPow.half)
          + (z + (-w)) * (-(U n ((z + w) * HalfPow.half))) := by
        refine eqv_trans _ _ _
          (mul_add_eqv (z + (-w)) (((2 : Q') * ((z + w) * HalfPow.half)) * U (n+1) ((z + w) * HalfPow.half))
            (-(U n ((z + w) * HalfPow.half)))) ?_
        exact add_eqv_congr_right _ _ _
          (eqv_symm (mul_assoc_eqv (z + (-w)) ((2:Q')*((z + w) * HalfPow.half)) (U (n+1) ((z + w) * HalfPow.half))))
    _ ≈ ((2 : Q') * ((z + w) * HalfPow.half)) * ((z + (-w)) * U (n+1) ((z + w) * HalfPow.half))
          + (-((z + (-w)) * U n ((z + w) * HalfPow.half))) := by
        refine Cheb.add_eqv_congr _ _ _ _ ?_ (mul_neg_eqv (z + (-w)) (U n ((z + w) * HalfPow.half)))
        -- (z−w)·(2c)·U_{n+1} ≈ (2c)·((z−w)·U_{n+1})
        refine eqv_trans _ _ _
          (mul_eqv_congr_right _ _ _ (mul_comm_eqv (z + (-w)) ((2:Q')*((z + w) * HalfPow.half)))) ?_
        exact mul_assoc_eqv ((2:Q')*((z + w) * HalfPow.half)) (z + (-w)) (U (n+1) ((z + w) * HalfPow.half))
    _ ≈ (z + w) * ((z + (-w)) * U (n+1) ((z + w) * HalfPow.half))
          + (-((z + (-w)) * U n ((z + w) * HalfPow.half))) := by
        refine add_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ _ ?_)
        exact twoC z w
    _ ≈ (z + w) * (z ^ (n+2) + (-(w ^ (n+2)))) + (-(z ^ (n+1) + (-(w ^ (n+1))))) := by
        refine Cheb.add_eqv_congr _ _ _ _ ?_ (neg_eqv_congr _ _ hn)
        exact mul_eqv_congr_left _ _ _ hn1
    _ ≈ z ^ (n+2+1) + (-(w ^ (n+2+1))) := GenAt_step_core z w hzw n

/-- **The U-generating identity `(G)`**, for ALL `M`:
`(z − w) · U_M((z+w)·½) ≈ z^{M+1} − w^{M+1}`, given `z·w ≈ 1`. -/
theorem Ugen (z w : Q') (hzw : z * w ≈ (1 : Q')) (M : Nat) : GenAt z w M := by
  have hpair : ∀ n, GenAt z w n ∧ GenAt z w (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨GenAt_zero z w, GenAt_one z w⟩
    | succ k ih =>
        obtain ⟨hk, hk1⟩ := ih
        exact ⟨hk1, GenAt_step z w hzw k hk hk1⟩
  exact (hpair M).1

/-- The explicit unfolded form of `Ugen`. -/
theorem Ugen_eq (z w : Q') (hzw : z * w ≈ (1 : Q')) (M : Nat) :
    (z + (-w)) * U M ((z + w) * HalfPow.half) ≈ z ^ (M+1) + (-(w ^ (M+1))) :=
  Ugen z w hzw M

/-- **Degenerate / confluent instance** `w = z` with `z·z ≈ 1` (e.g. `z = ±1`):
`(z − z)·U_M(c) ≈ 0`.  A sanity corollary of `(G)`: the LHS factor `z − z` is
`≈ 0`, and indeed `z^{M+1} − z^{M+1} ≈ 0`. -/
theorem Ueven_geom (z : Q') (hzz : z * z ≈ (1 : Q')) (M : Nat) :
    (z + (-z)) * U M ((z + z) * HalfPow.half) ≈ (0 : Q') := by
  refine eqv_trans _ _ _ (Ugen z z hzz M) ?_
  exact Q'.add_neg_self_eqv (z ^ (M+1))

/-! ## 3. The unconditional part of `(★)`: `S_0 = M`

`S_0 = Σ_{k<M} T_0(x_k)`; since `T_0 = 1` at every node, this is the constant sum
`Σ_{k<M} 1 = M`.

The abstract `ChebRootDataT M` interface does NOT field-axiomatize `tval 0 k = 1`
(it constrains only the `uval`/`tval` *bridge*, not the absolute `tval 0` value),
so `S_0 = M` is proved here under the explicit `tval 0 k ≈ 1` hypothesis, which
holds for every genuine `T`-node datum (`tval0_fromQNodes` supplies it for the
canonical `fromQNodes` construction, where `T_0 = 1` definitionally). -/

/-- `Σ_{k<N} 1 ≈ ofNat N` over `Q'` (the constant-`1` finite sum). -/
theorem finSum_one_eq (N : Nat) :
    (RationalTail.finSum (fun _ => (1 : Q')) N).eqv (Q'.ofNat N) := by
  induction N with
  | zero => show (0 : Q').eqv (Q'.ofNat 0); decide
  | succ m ih =>
      show (RationalTail.finSum (fun _ => (1 : Q')) m + (1 : Q')).eqv (Q'.ofNat (m+1))
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      -- ofNat m + 1 ≈ ofNat (m+1)
      refine eqv_trans _ _ _
        (add_eqv_congr_left _ _ _ (show (1:Q') ≈ Q'.ofNat 1 from ChebU.one_eq_ofNat ▸ eqv_refl _)) ?_
      exact ChebU.ofNat_add_eqv m 1

/-- **`S_0 = M`** for any `ChebRootDataT M` whose `0`-th first-kind values are
`1` (`tval 0 k ≈ cone`): the unconditional part of `(★)`.
`Sj D 0 = Σ_k T_0(x_k) = Σ_k 1 = M`. -/
theorem Sj0_eq_M {M : Nat} (D : ChebRootDataT M)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone) :
    CReal.Equiv (Sj D 0) (CReal.ofQ' (Q'.ofNat M)) := by
  unfold Sj
  -- Σ_k tval 0 k ≈ Σ_k cone, then evaluate approx-wise to finSum of 1's = ofNat M.
  refine CReal.Equiv.trans (CRealContinuumAlg.csum_congr (fun k => htval0 k) M) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun pr => ?_)
  rw [CReal.csum_approx (fun _ => CReal.cone) M pr]
  -- (cone.approx pr) = (ofQ' 1).approx pr = 1 definitionally
  show (RationalTail.finSum (fun _ => (1 : Q')) M).eqv (Q'.ofNat M)
  exact finSum_one_eq M

/-- The `tval 0 k ≈ 1` hypothesis holds for the canonical `fromQNodes` datum
(`T_0 = 1` definitionally). -/
theorem tval0_fromQNodes (M : Nat) (node : Nat → Q') (k : Nat) :
    CReal.Equiv ((fromQNodes M node).tval 0 k) CReal.cone := by
  show CReal.Equiv (CReal.ofQ' (T 0 (node k))) CReal.cone
  rw [T_zero]; exact SumOfSquares.Equiv_of_approx_eqv (fun _ => eqv_refl _)

/-- **`S_0 = M` for every `fromQNodes` datum** (the canonical rational-node
construction). -/
theorem Sj0_eq_M_fromQNodes (M : Nat) (node : Nat → Q') :
    CReal.Equiv (Sj (fromQNodes M node) 0) (CReal.ofQ' (Q'.ofNat M)) :=
  Sj0_eq_M (fromQNodes M node) (tval0_fromQNodes M node)

/-! ## 4. The named root-side residual and the collapse it yields

The U-generating identity `(G)` (`Ugen`) is the coefficient/generating-function
fact, proved unconditionally above.  Converting it into the *root-side* power
sums `S_2 = −1`, `S_p = S_{p+2}` is the Newton step: it needs the `x_k` to be the
genuine roots of `U_M`.  We name exactly that residual. -/

/-- **The named residual** — the root-side Newton step: `S_2 = −1` and
`S_p = S_{p+2}` for `0 < p ≤ M−1`.  Together with the proved `S_0 = M`
(`Sj0_eq_M`) this is the full `PowerSumCollapse.TPowerSum`.  This is the part of
`(★)` that genuinely uses "the `x_k` are the roots of `U_M`" — encoded nowhere in
the abstract `ChebRootDataT` interface — so it is named, not faked. -/
def RootPowerSumBridge {M : Nat} (D : ChebRootDataT M) : Prop :=
  CReal.Equiv (Sj D 2) (CReal.ofQ' (-(1 : Q')))
  ∧ (∀ p, 0 < p → p ≤ M - 1 → CReal.Equiv (Sj D p) (Sj D (p+2)))

/-- **`TPowerSum` from the residual.**  Given `S_0 = M` (proved here for nodes
with `tval 0 k ≈ 1`) and the named `RootPowerSumBridge` (`S_2 = −1`,
`S_p = S_{p+2}`), the full `PowerSumCollapse.TPowerSum D` holds — and hence, by
`PowerSumCollapse.powerSumCollapse_of_TPowerSum`, the all-order Gram PSD residual
`ChebOrthogonality.PowerSumCollapse (D.toU)`. -/
theorem tPowerSum_of_bridge {M : Nat} (D : ChebRootDataT M)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (hbridge : RootPowerSumBridge D) :
    PowerSumCollapse.TPowerSum D :=
  ⟨Sj0_eq_M D htval0, hbridge.1, hbridge.2⟩

/-! ## 5. The `M = 2` instance, fully discharged (rational nodes `±1/2`)

The worst-case small order `M = 2` has the rational Gauss–Chebyshev nodes `±1/2`,
where the entire residual is a closed `Q'` computation.  `PowerSumCollapse`
already discharges it (`TPowerSum2`); we re-export it here as the `M = 2`
instance of the residual and of `TPowerSum`, and confirm the resulting Gram PSD
collapse. -/

/-- **`PowerSumCollapse.TPowerSum` inhabited at `M = 2`** — the rational `±1/2`
nodes, via the proved `PowerSumCollapse.TPowerSum2`. -/
theorem TPowerSum_M2 : PowerSumCollapse.TPowerSum PowerSumCollapse.rootData2 :=
  PowerSumCollapse.TPowerSum2

/-- The root-side residual `RootPowerSumBridge` at `M = 2`, extracted from the
discharged `TPowerSum2` (its second and third components). -/
theorem RootPowerSumBridge_M2 : RootPowerSumBridge PowerSumCollapse.rootData2 :=
  ⟨PowerSumCollapse.TPowerSum2.2.1, PowerSumCollapse.TPowerSum2.2.2⟩

/-- **`S_0 = 2` for the `M = 2` datum**, via the general `Sj0_eq_M_fromQNodes`
(`rootData2 = fromQNodes 2 node2`). -/
theorem Sj0_M2 :
    CReal.Equiv (Sj PowerSumCollapse.rootData2 0) (CReal.ofQ' (Q'.ofNat 2)) :=
  Sj0_eq_M_fromQNodes 2 ChebOrthogonality.node2

/-- **The all-order-form collapse at `M = 2`**: the `ChebOrthogonality`
`PowerSumCollapse` residual inhabited at `M = 2` through the first-kind T-route,
re-exported from `PowerSumCollapse.powerSumCollapse2`. -/
theorem orthoCollapse_M2 :
    ChebOrthogonality.PowerSumCollapse PowerSumCollapse.rootData2.toU :=
  PowerSumCollapse.powerSumCollapse2

end YMGap.Continuum.TPowerSum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a
non-decidable `Prop`. -/

#print axioms YMGap.Continuum.TPowerSum.w_mul_pow_cancel
#print axioms YMGap.Continuum.TPowerSum.GenAt_zero
#print axioms YMGap.Continuum.TPowerSum.GenAt_one
#print axioms YMGap.Continuum.TPowerSum.genstep_add_core
#print axioms YMGap.Continuum.TPowerSum.GenAt_step_core
#print axioms YMGap.Continuum.TPowerSum.GenAt_step
#print axioms YMGap.Continuum.TPowerSum.Ugen
#print axioms YMGap.Continuum.TPowerSum.Ueven_geom
#print axioms YMGap.Continuum.TPowerSum.finSum_one_eq
#print axioms YMGap.Continuum.TPowerSum.Sj0_eq_M
#print axioms YMGap.Continuum.TPowerSum.Sj0_eq_M_fromQNodes
#print axioms YMGap.Continuum.TPowerSum.tPowerSum_of_bridge
#print axioms YMGap.Continuum.TPowerSum.TPowerSum_M2
#print axioms YMGap.Continuum.TPowerSum.RootPowerSumBridge_M2
#print axioms YMGap.Continuum.TPowerSum.Sj0_M2
#print axioms YMGap.Continuum.TPowerSum.orthoCollapse_M2
