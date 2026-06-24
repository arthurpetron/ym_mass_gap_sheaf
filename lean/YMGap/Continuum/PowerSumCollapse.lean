/-
# The power-sum collapse for the Gauss–Chebyshev-`U` quadrature (Wall-1 item 3)

The discrete-orthogonality reproduction `Σ_k (1−x_k²) U_i(x_k) U_j(x_k) =
((M+1)/2)·δ_{ij}` (the load-bearing Gram-PSD kernel) is, by the already-proved
product linearization (`ChebOrthogonality.orthogonality_reduces_to_moments`),
reduced to the **single-`U` weighted node moments**

    Q_M(U_p) = Σ_{k=1}^{M} (1 − x_k²) U_p(x_k)
             = (M+1)/2   (p = 0),     = 0   (0 < p ≤ M−1),

over the `M` roots `x_k` of `U_M`.  This module attacks that residual
(`ChebOrthogonality.PowerSumCollapse`).

## The route — the first-kind power-sum bridge (Christoffel/Dirichlet folding)

The genuine, `π`-free engine is the **weight-fold bridge**, in its fraction-free
(doubled) form

    2·(1 − x²)·U_p(x)  =  T_p(x) − T_{p+2}(x)      (PROVED, all `p`, all `x`),

with `T` the first-kind Chebyshev polynomial.  (Trig shadow:
`2 sin²θ · sin((p+1)θ)/sinθ = 2 sinθ·sin((p+1)θ) = cos pθ − cos (p+2)θ`.)  Summed
over the nodes, this turns the single-`U` moment into a difference of
**first-kind power sums**

    2·Q_M(U_p)  =  S_p − S_{p+2},      S_j := Σ_{k=1}^{M} T_j(x_k),

so the entire collapse reduces to the *single* Dirichlet-kernel power-sum fact

    S_0 = M,   S_2 = −1,   and   S_p = S_{p+2}  for 0 < p ≤ M−1                (★)

— `S_0 − S_2 = M + 1` on the diagonal (`2·Q_M(U_0) = M+1`), and `S_p = S_{p+2}`
(same parity) off-diagonal (`2·Q_M(U_p) = 0`).  This is a strictly *smaller* and
structurally *sharper* residual than the original two-part `PowerSumCollapse`: a
single first-kind power-sum identity on the roots of `U_M` (the genuine
Newton / discrete-DFT step).

## PROVED (genuine, axiom-clean, general `M`, `π`-free)

  * `cheb_recurrence_match` — generic two-step matcher: two `Q'`-sequences
    sharing the second-kind recurrence `f(p+2) ≈ 2x·f(p+1) − f(p)` and agreeing
    at `p = 0, 1` agree at all `p`.
  * `weightU2_recur` / `Tdiff_recur` — both sides of the (doubled) bridge satisfy
    the recurrence.
  * **`weightU2_eq_Tdiff`** — the bridge `2(1−x²)·U_p = T_p − T_{p+2}` for ALL
    `p` and ALL `x`, by the matcher.  This is the load-bearing new identity.
  * `ChebRootDataT` — the node interface augmented with first-kind node values
    `tval p k = T_p(x_k)` and the per-node bridge.  `toU` forgets `tval` to a
    plain `ChebOrthogonality.ChebRootData`.
  * `Sj` / `moment_eq_half_Sdiff` — `Q_M(U_p) = ½·(S_p − S_{p+2})`, the moment
    through the first-kind power sums `S_j = Σ_{k<M} tval j k`.
  * **`powerSumCollapse_of_TPowerSum`** — given the named residual `TPowerSum`
    `(★)`, the full `ChebOrthogonality.PowerSumCollapse (D.toU)` follows.
    Genuine and unconditional in `(★)`.
  * **`M = 2` end-to-end through the T-route** — the rational instance
    `rootData2 : ChebRootDataT 2` (nodes `±1/2`), its `TPowerSum2` discharged by
    `decide`, hence `PowerSumCollapse (rootData2.toU)` and the diagonal value
    `(2+1)/2 = 3/2` reproduced via `ChebOrthogonality.chebU_orthogonality_diag0`.

## NAMED open (the residual — strictly sharper than before)

  * `TPowerSum D` — the first-kind Dirichlet power-sum collapse `(★)`:
    `S_0 = M`, `S_2 = −1`, `S_p = S_{p+2}` for `0 < p ≤ M−1`.  The ONLY
    general-`M` input left.  Discharged unconditionally at `M = 2`.

The all-order Gram PSD is therefore still REDUCED, not closed: it now rests on
the single sharp residual `(★)` (down from the two-part `PowerSumCollapse`),
plus the proved product linearization.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` via `omega`/`Nat`/`Int`
helpers).  No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no
`decide` on non-decidable `Prop`.  `decide` only on closed `Q'`/`Nat`.
Witnesses (`ChebRootDataT`) are `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.ChebOrthogonality

namespace YMGap.Continuum.PowerSumCollapse

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.ChebOrthogonality

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The generic two-step recurrence matcher over `Q'` -/

/-- The second-kind recurrence `h(p+2) ≈ (2x)·h(p+1) + (−h(p))`. -/
def SatRecur (x : Q') (h : Nat → Q') : Prop :=
  ∀ p, h (p+2) ≈ ((2 : Q') * x) * h (p+1) + (-(h p))

/-- **Generic two-step matcher.**  If `f, g` satisfy the same recurrence and
agree at `0, 1`, they agree at all `p`. -/
theorem cheb_recurrence_match (x : Q') (f g : Nat → Q')
    (hf : SatRecur x f) (hg : SatRecur x g)
    (h0 : f 0 ≈ g 0) (h1 : f 1 ≈ g 1) :
    ∀ p, f p ≈ g p := by
  have hpair : ∀ p, (f p ≈ g p) ∧ (f (p+1) ≈ g (p+1)) := by
    intro p
    induction p with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
        obtain ⟨hk, hk1⟩ := ih
        refine ⟨hk1, ?_⟩
        refine eqv_trans _ _ _ (hf k) ?_
        refine eqv_trans _ _ _ ?_ (eqv_symm (hg k))
        exact Cheb.add_eqv_congr _ _ _ _
          (mul_eqv_congr_left _ _ _ hk1) (neg_eqv_congr _ _ hk)
  exact fun p => (hpair p).1

/-! ## 2. The two sides of the (doubled) bridge -/

/-- The weight `1 − x² = 1 + (−(x·x))`. -/
def wQ (x : Q') : Q' := (1 : Q') + (-(x * x))

/-- LHS sequence `p ↦ 2·(1−x²)·U_p(x)`. -/
def weightU2 (x : Q') (p : Nat) : Q' := (2 : Q') * (wQ x * U p x)

/-- RHS sequence `p ↦ T_p(x) − T_{p+2}(x)`. -/
def Tdiff (x : Q') (p : Nat) : Q' := T p x + (-(T (p+2) x))

/-! ### LHS recurrence: a constant multiple of `U` respects the recurrence -/

/-- The all-atom core of the LHS recurrence: `2·(c·(d·A + (−B))) ≈ d·(2·(c·A)) +
(−(2·(c·B)))` for atoms `c, d, A, B` (here `d = 2x`, `c = 1−x²`). -/
theorem weightU2_recur_atoms (c d A B : Q') :
    (2 : Q') * (c * (d * A + (-B)))
      ≈ d * ((2 : Q') * (c * A)) + (-((2 : Q') * (c * B))) := by
  calc (2 : Q') * (c * (d * A + (-B)))
      ≈ (2 : Q') * (c * (d * A) + c * (-B)) :=
        mul_eqv_congr_left _ _ _ (mul_add_eqv c (d * A) (-B))
    _ ≈ (2 : Q') * (c * (d * A)) + (2 : Q') * (c * (-B)) :=
        mul_add_eqv _ _ _
    _ ≈ d * ((2 : Q') * (c * A)) + (-((2 : Q') * (c * B))) := by
        refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
        · refine eqv_trans _ _ _
            (mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv c d A))) ?_
          refine eqv_trans _ _ _
            (mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv c d))) ?_
          refine eqv_trans _ _ _
            (mul_eqv_congr_left _ _ _ (mul_assoc_eqv d c A)) ?_
          refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv 2 d (c * A))) ?_
          refine eqv_trans _ _ _
            (mul_eqv_congr_right _ _ _ (mul_comm_eqv 2 d)) ?_
          exact mul_assoc_eqv d 2 (c * A)
        · refine eqv_trans _ _ _
            (mul_eqv_congr_left _ _ _ (mul_neg_eqv c B)) ?_
          exact mul_neg_eqv 2 (c * B)

theorem weightU2_recur (x : Q') : SatRecur x (weightU2 x) := by
  intro p
  unfold weightU2
  rw [U_succ_succ p x]
  exact weightU2_recur_atoms (wQ x) ((2:Q') * x) (U (p+1) x) (U p x)

/-! ### RHS recurrence: `T_p − T_{p+2}` respects the recurrence

`g(p+2) = T(p+2) − T(p+4)`, and using `T(p+2) = 2x·T(p+1) − T p` and
`T(p+4) = 2x·T(p+3) − T(p+2)`, the identity reduces to a purely additive identity
in the atoms `e = (2x)·T(p+1)`, `f = (2x)·T(p+3)`, `c = T p`. -/

/-- The additive core: `(e + (−c)) + (−(f + (−(e + (−c))))) ≈ (e + (−f)) +
(−(c + (−(e + (−c)))))`.  Both sides are `2e − f − 2c`. -/
theorem add_core (e f c : Q') :
    (e + (-c)) + (-(f + (-(e + (-c)))))
      ≈ (e + (-f)) + (-(c + (-(e + (-c))))) := by
  -- Normalize both sides to E := (e + e) + ((-f) + ((-c) + (-c))).
  have hL : (e + (-c)) + (-(f + (-(e + (-c))))) ≈ (e + e) + ((-f) + ((-c) + (-c))) := by
    -- −(f + −(e + −c)) ≈ (−f) + (e + (−c))
    have h1 : (-(f + (-(e + (-c))))) ≈ (-f) + (e + (-c)) :=
      eqv_trans _ _ _ (Q'.neg_add_eqv f (-(e + (-c))))
        (add_eqv_congr_left _ _ _ (neg_neg_eqv (e + (-c))))
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ h1) ?_
    -- (e + (−c)) + ((−f) + (e + (−c)))  ≈  E
    -- regroup to (e + e) + ((−f) + ((−c) + (−c)))
    calc (e + (-c)) + ((-f) + (e + (-c)))
        ≈ (e + (-c)) + ((e + (-f)) + (-c)) :=
          add_eqv_congr_left _ _ _
            (eqv_trans _ _ _ (eqv_symm (add_assoc_eqv (-f) e (-c)))
              (add_eqv_congr_right _ _ _ (add_comm_eqv (-f) e)))
      _ ≈ (e + (-c)) + (e + ((-f) + (-c))) :=
          add_eqv_congr_left _ _ _ (add_assoc_eqv e (-f) (-c))
      _ ≈ ((e + (-c)) + e) + ((-f) + (-c)) :=
          eqv_symm (add_assoc_eqv (e + (-c)) e ((-f) + (-c)))
      _ ≈ (e + ((-c) + e)) + ((-f) + (-c)) :=
          add_eqv_congr_right _ _ _ (add_assoc_eqv e (-c) e)
      _ ≈ (e + (e + (-c))) + ((-f) + (-c)) :=
          add_eqv_congr_right _ _ _ (add_eqv_congr_left _ _ _ (add_comm_eqv (-c) e))
      _ ≈ ((e + e) + (-c)) + ((-f) + (-c)) :=
          add_eqv_congr_right _ _ _ (eqv_symm (add_assoc_eqv e e (-c)))
      _ ≈ (e + e) + ((-c) + ((-f) + (-c))) :=
          add_assoc_eqv (e + e) (-c) ((-f) + (-c))
      _ ≈ (e + e) + (((-c) + (-f)) + (-c)) :=
          add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (-c) (-f) (-c)))
      _ ≈ (e + e) + (((-f) + (-c)) + (-c)) :=
          add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (add_comm_eqv (-c) (-f)))
      _ ≈ (e + e) + ((-f) + ((-c) + (-c))) :=
          add_eqv_congr_left _ _ _ (add_assoc_eqv (-f) (-c) (-c))
  have hR : (e + (-f)) + (-(c + (-(e + (-c))))) ≈ (e + e) + ((-f) + ((-c) + (-c))) := by
    have h1 : (-(c + (-(e + (-c))))) ≈ (-c) + (e + (-c)) :=
      eqv_trans _ _ _ (Q'.neg_add_eqv c (-(e + (-c))))
        (add_eqv_congr_left _ _ _ (neg_neg_eqv (e + (-c))))
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ h1) ?_
    calc (e + (-f)) + ((-c) + (e + (-c)))
        ≈ (e + (-f)) + (((-c) + e) + (-c)) :=
          add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (-c) e (-c)))
      _ ≈ (e + (-f)) + ((e + (-c)) + (-c)) :=
          add_eqv_congr_left _ _ _
            (add_eqv_congr_right _ _ _ (add_comm_eqv (-c) e))
      _ ≈ (e + (-f)) + (e + ((-c) + (-c))) :=
          add_eqv_congr_left _ _ _ (add_assoc_eqv e (-c) (-c))
      _ ≈ ((e + (-f)) + e) + ((-c) + (-c)) :=
          eqv_symm (add_assoc_eqv (e + (-f)) e ((-c) + (-c)))
      _ ≈ (e + ((-f) + e)) + ((-c) + (-c)) :=
          add_eqv_congr_right _ _ _ (add_assoc_eqv e (-f) e)
      _ ≈ (e + (e + (-f))) + ((-c) + (-c)) :=
          add_eqv_congr_right _ _ _ (add_eqv_congr_left _ _ _ (add_comm_eqv (-f) e))
      _ ≈ ((e + e) + (-f)) + ((-c) + (-c)) :=
          add_eqv_congr_right _ _ _ (eqv_symm (add_assoc_eqv e e (-f)))
      _ ≈ (e + e) + ((-f) + ((-c) + (-c))) :=
          add_assoc_eqv (e + e) (-f) ((-c) + (-c))
  exact eqv_trans _ _ _ hL (eqv_symm hR)

theorem Tdiff_recur (x : Q') : SatRecur x (Tdiff x) := by
  intro p
  -- Goal: Tdiff x (p+2) ≈ (2x)·Tdiff x (p+1) + (−(Tdiff x p)), i.e.
  --   (T(p+2) + −T(p+4)) ≈ (2x)·(T(p+1) + −T(p+3)) + (−(T p + −T(p+2)))
  unfold Tdiff
  -- Replace T(p+2) and T(p+4) by the recurrence (as definitional `=`).
  have hT2 : T (p+2) x = ((2:Q') * x) * T (p+1) x + (-(T p x)) := T_succ_succ p x
  have hT4 : T (p+2+2) x = ((2:Q') * x) * T (p+3) x + (-(T (p+2) x)) := T_succ_succ (p+2) x
  rw [hT4, hT2]
  -- Now goal is in atoms d·a, d·b, cc with d = 2x, a = T(p+1), b = T(p+3), cc = T p.
  -- LHS: (d·a + (−cc)) + (−((d·b) + (−((d·a) + (−cc)))))
  -- RHS: d·(a + (−b)) + (−(cc + (−((d·a) + (−cc)))))
  -- Distribute d·(a + (−b)) ≈ (d·a) + (−(d·b)); then apply add_core.
  refine eqv_trans _ _ _ ?_
    (Cheb.add_eqv_congr _ _ _ _
      (eqv_symm (eqv_trans _ _ _ (mul_add_eqv ((2:Q')*x) (T (p+1) x) (-(T (p+3) x)))
        (add_eqv_congr_left _ _ _ (mul_neg_eqv ((2:Q')*x) (T (p+3) x)))))
      (eqv_refl _))
  exact add_core (((2:Q')*x) * T (p+1) x) (((2:Q')*x) * T (p+3) x) (T p x)

/-! ## 3. The bridge `2·(1−x²)·U_p = T_p − T_{p+2}` -/

/-- `(2:Q')·1 ≈ 2` and `1 + 1 = 2` definitionally helper. -/
private theorem two_mul_one : (2 : Q') * (1 : Q') ≈ (2 : Q') := mul_one_eqv 2

/-- `2·(1 + (−s)) ≈ 2 + (−(2·s))`. -/
private theorem two_one_sub (s : Q') : (2 : Q') * ((1 : Q') + (-s)) ≈ (2 : Q') + (-((2 : Q') * s)) := by
  calc (2 : Q') * ((1 : Q') + (-s))
      ≈ (2 : Q') * 1 + (2 : Q') * (-s) := mul_add_eqv _ _ _
    _ ≈ (2 : Q') + (-((2 : Q') * s)) :=
        Cheb.add_eqv_congr _ _ _ _ two_mul_one (mul_neg_eqv 2 s)
/-- `(2x)·((2x)·x) ≈ 2·((x·x)·(2x))` — a pure multiplicative rearrangement
(both are `4x³`). -/
private theorem cube_assoc (x : Q') :
    ((2:Q') * x) * (((2:Q') * x) * x) ≈ (2:Q') * ((x * x) * ((2:Q') * x)) := by
  -- LHS = (2x)·((2x)·x) ; RHS = 2·((x·x)·(2x))
  calc ((2:Q') * x) * (((2:Q') * x) * x)
      ≈ (((2:Q') * x) * ((2:Q') * x)) * x := eqv_symm (mul_assoc_eqv _ _ _)
    _ ≈ ((2:Q') * x) * ((2:Q') * x) * x := eqv_refl _
    _ ≈ (2:Q') * ((x * x) * ((2:Q') * x)) := by
        -- rearrange ((2x)(2x))x  to  2·((x·x)(2x)) ; route via commutativity.
        refine eqv_trans _ _ _ (mul_comm_eqv (((2:Q')*x)*((2:Q')*x)) x) ?_
        -- x·((2x)(2x)) ≈ 2·((x·x)(2x))
        refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (mul_assoc_eqv (2:Q') x ((2:Q')*x))) ?_
        -- x·(2·(x·(2x)))
        refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv x (2:Q') (x*((2:Q')*x)))) ?_
        -- (x·2)·(x·(2x))
        refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv x (2:Q'))) ?_
        -- (2·x)·(x·(2x))
        refine eqv_trans _ _ _ (mul_assoc_eqv (2:Q') x (x*((2:Q')*x))) ?_
        -- 2·(x·(x·(2x)))
        refine mul_eqv_congr_left _ _ _ ?_
        exact eqv_symm (mul_assoc_eqv x x ((2:Q')*x))

/-- The `p = 1` base identity, generalized over the abbreviations `dx = 2x` and
`cube = dx·(dx·x)` (introduced as ordinary variables to keep the additive algebra
readable without the Mathlib `set` tactic). -/
theorem base1_identity_gen (x dx cube : Q') (hdx : dx = (2:Q') * x)
    (hcube : cube = dx * (dx * x)) :
    (2 : Q') * (((1 : Q') + (-(x * x))) * dx)
      ≈ x + (-(dx * (dx * x + (-(1:Q'))) + (-(x)))) := by
  -- ===== LHS ===== 2·((1 + (−(x·x)))·dx) ≈ (dx + dx) + (−(2·((x·x)·dx)))
  have hL : (2 : Q') * (((1 : Q') + (-(x * x))) * dx) ≈ (dx + dx) + (-((2:Q') * ((x*x)*dx))) := by
    have e1 : ((1 : Q') + (-(x * x))) * dx ≈ dx + (-((x*x)*dx)) :=
      eqv_trans _ _ _ (Cheb.add_mul_eqv 1 (-(x*x)) dx)
        (Cheb.add_eqv_congr _ _ _ _ (one_mul_eqv dx) (neg_mul_eqv (x*x) dx))
    refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ e1) ?_
    refine eqv_trans _ _ _ (mul_add_eqv (2:Q') dx (-((x*x)*dx))) ?_
    exact Cheb.add_eqv_congr _ _ _ _ (two_mul_eqv dx) (mul_neg_eqv 2 ((x*x)*dx))
  -- ===== RHS ===== x + (−((dx·(dx·x + (−1))) + (−x))) ≈ ((x+x)+dx) + (−cube)
  have hR : x + (-((dx * (dx * x + (-(1:Q')))) + (-(x))))
      ≈ ((x + x) + dx) + (-cube) := by
    -- dx·(dx·x + (−1)) ≈ cube + (−dx)
    have e2 : dx * (dx * x + (-(1:Q'))) ≈ cube + (-dx) :=
      eqv_trans _ _ _ (mul_add_eqv dx (dx*x) (-(1:Q')))
        (Cheb.add_eqv_congr _ _ _ _
          (Q'.eqv_of_eq hcube.symm)
          (eqv_trans _ _ _ (mul_neg_eqv dx 1) (neg_eqv_congr _ _ (mul_one_eqv dx))))
    -- (cube + (−dx)) + (−x) , negate, add x
    refine eqv_trans _ _ _
      (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _
        (add_eqv_congr_right _ _ _ e2))) ?_
    -- x + (−((cube + (−dx)) + (−x)))
    -- −((cube + (−dx)) + (−x)) ≈ (−cube) + (dx + x)
    have e3 : (-(((cube + (-dx)) + (-x)))) ≈ (-cube) + (dx + x) := by
      refine eqv_trans _ _ _ (Q'.neg_add_eqv (cube + (-dx)) (-x)) ?_
      -- -(cube+(-dx)) + (-(-x))  ≈  ((-cube)+dx) + x  ≈  (-cube)+(dx+x)
      refine eqv_trans _ _ _
        (Cheb.add_eqv_congr _ _ _ _
          (eqv_trans _ _ _ (Q'.neg_add_eqv cube (-dx))
            (add_eqv_congr_left _ _ _ (neg_neg_eqv dx)))
          (neg_neg_eqv x)) ?_
      exact add_assoc_eqv (-cube) dx x
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ e3) ?_
    -- x + ((−cube) + (dx + x)) ≈ ((x+x)+dx) + (−cube)
    calc x + ((-cube) + (dx + x))
        ≈ (x + (-cube)) + (dx + x) := eqv_symm (add_assoc_eqv x (-cube) (dx + x))
      _ ≈ (x + (-cube)) + (x + dx) := add_eqv_congr_left _ _ _ (add_comm_eqv dx x)
      _ ≈ ((x + (-cube)) + x) + dx := eqv_symm (add_assoc_eqv (x + (-cube)) x dx)
      _ ≈ (x + ((-cube) + x)) + dx := add_eqv_congr_right _ _ _ (add_assoc_eqv x (-cube) x)
      _ ≈ (x + (x + (-cube))) + dx := add_eqv_congr_right _ _ _
            (add_eqv_congr_left _ _ _ (add_comm_eqv (-cube) x))
      _ ≈ ((x + x) + (-cube)) + dx := add_eqv_congr_right _ _ _ (eqv_symm (add_assoc_eqv x x (-cube)))
      _ ≈ (x + x) + ((-cube) + dx) := add_assoc_eqv (x + x) (-cube) dx
      _ ≈ (x + x) + (dx + (-cube)) := add_eqv_congr_left _ _ _ (add_comm_eqv (-cube) dx)
      _ ≈ ((x + x) + dx) + (-cube) := eqv_symm (add_assoc_eqv (x + x) dx (-cube))
  -- Now relate the two normal forms:  (dx+dx) + (−(2·((x·x)·dx)))  vs  ((x+x)+dx) + (−cube)
  refine eqv_trans _ _ _ hL (eqv_trans _ _ _ ?_ (eqv_symm hR))
  -- dx + dx ≈ (x+x) + dx  (since dx = 2x ≈ x + x) ; and 2·((x·x)·dx) ≈ cube.
  refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
  · -- dx + dx ≈ (x + x) + dx
    refine add_eqv_congr_right _ _ _ ?_
    rw [hdx]; exact two_mul_eqv x
  · -- −(2·((x·x)·dx)) ≈ −cube ; cube = dx·(dx·x) = (2x)·((2x)·x); use cube_assoc
    refine neg_eqv_congr _ _ ?_
    -- 2·((x·x)·dx) ≈ cube
    rw [hcube, hdx]
    exact eqv_symm (cube_assoc x)

/-- The `p = 1` base identity (the concrete instance used by the bridge). -/
theorem base1_identity (x : Q') :
    (2 : Q') * (((1 : Q') + (-(x * x))) * ((2 : Q') * x))
      ≈ x + (-(((2:Q') * x) * (((2:Q') * x) * x + (-(1:Q'))) + (-(x)))) :=
  base1_identity_gen x ((2:Q') * x) (((2:Q') * x) * (((2:Q') * x) * x)) rfl rfl


/-- **The weight-fold bridge (doubled).**  For all `p` and all `x`,
`2·(1−x²)·U_p(x) ≈ T_p(x) − T_{p+2}(x)`. -/
theorem weightU2_eq_Tdiff (x : Q') (p : Nat) :
    weightU2 x p ≈ Tdiff x p := by
  refine cheb_recurrence_match x (weightU2 x) (Tdiff x)
    (weightU2_recur x) (Tdiff_recur x) ?_ ?_ p
  · -- p = 0: 2·((1−x²)·1) ≈ T0 − T2 = 1 − ((2x)x − 1).  Both ≈ 2 + (−(2·(x·x))).
    show (2 : Q') * (wQ x * U 0 x) ≈ T 0 x + (-(T 2 x))
    rw [U_zero, T_zero, T_succ_succ 0 x, T_one, T_zero]
    unfold wQ
    -- LHS: 2·((1 + (−(x·x)))·1) ; RHS: 1 + (−((2x)·x + (−1)))
    have hL : (2 : Q') * (((1 : Q') + (-(x * x))) * 1)
        ≈ (2 : Q') + (-((2 : Q') * (x * x))) :=
      eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (mul_one_eqv _)) (two_one_sub (x * x))
    have hR : (1 : Q') + (-(((2 : Q') * x) * x + (-(1 : Q'))))
        ≈ (2 : Q') + (-((2 : Q') * (x * x))) := by
      -- 1 + (−((2x)x + (−1))) ≈ 1 + ((−((2x)x)) + 1) ≈ (1+1) + (−(2·(x·x)))
      have h1 : (-(((2 : Q') * x) * x + (-(1 : Q')))) ≈ (-(((2 : Q') * x) * x)) + 1 :=
        eqv_trans _ _ _ (Q'.neg_add_eqv (((2 : Q') * x) * x) (-(1:Q')))
          (add_eqv_congr_left _ _ _ (neg_neg_eqv 1))
      refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ h1) ?_
      -- 1 + ((−((2x)x)) + 1) ≈ (1 + 1) + (−((2x)x)) ; (2x)x ≈ 2·(x·x)
      refine eqv_trans _ _ _ (eqv_symm (add_assoc_eqv 1 (-(((2:Q')*x)*x)) 1)) ?_
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (add_comm_eqv 1 (-(((2:Q')*x)*x)))) ?_
      refine eqv_trans _ _ _ (add_assoc_eqv (-(((2:Q')*x)*x)) 1 1) ?_
      refine eqv_trans _ _ _ (add_comm_eqv (-(((2:Q')*x)*x)) ((1:Q')+1)) ?_
      -- (1+1) + (−((2x)x)) ; 1+1 = 2 (rfl); (2x)x ≈ 2(x·x)
      show ((1:Q') + 1) + (-(((2:Q')*x)*x)) ≈ (2:Q') + (-((2:Q') * (x*x)))
      exact add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ (mul_assoc_eqv 2 x x))
    exact eqv_trans _ _ _ hL (eqv_symm hR)
  · -- p = 1: 2·((1−x²)·2x) ≈ T1 − T3.  Both ≈ 4x + (−(4·((x·x)·x))).
    show (2 : Q') * (wQ x * U 1 x) ≈ T 1 x + (-(T 3 x))
    rw [U_one, T_one]
    rw [show (3:Nat) = 1 + 2 from rfl, T_succ_succ 1 x, T_succ_succ 0 x, T_one, T_zero]
    unfold wQ
    -- LHS: 2·((1 + (−(x·x)))·(2x)) ; RHS: x + (−((2x)·((2x)·x + (−1)) + (−x)))
    -- Both reduce to N := ((x+x)+(x+x)) + (−(cube)) with cube = the 4x³ monomial.
    exact base1_identity x

/-! ## 4. The node interface augmented with first-kind values

`ChebRootDataT M` extends the per-node data of `ChebOrthogonality.ChebRootData`
with first-kind node values `tval p k = T_p(x_k)` and the **per-node bridge**
`wt k · uval p k ≈ ½·(tval p k − tval (p+2) k)` (the `CReal` shadow of the proved
`Q'` bridge `weightU2_eq_Tdiff`).  `toU` forgets `tval` back to a plain
`ChebRootData`, so any `ChebOrthogonality` consumer applies. -/

/-- Constructive-real reflexivity (local). -/
private theorem cEq_refl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- **Augmented node data.**  `Type`-level (MLTT/HoTT-valid). -/
structure ChebRootDataT (M : Nat) where
  /-- The `M` nodes. -/
  x : Nat → CReal
  /-- Second-kind node values `uval p k = U_p(x_k)`. -/
  uval : Nat → Nat → CReal
  /-- First-kind node values `tval p k = T_p(x_k)`. -/
  tval : Nat → Nat → CReal
  /-- The node weight `wt k = 1 − x_k²`. -/
  wt : Nat → CReal
  /-- `uval 0 k = U_0(x_k) = 1`. -/
  uval_zero : ∀ k, CReal.Equiv (uval 0 k) CReal.cone
  /-- Per-node second-kind fold (the Dirichlet step). -/
  uval_fold : ∀ n k, CReal.Equiv
    (CReal.mul (CReal.mul (CReal.ofQ' 2) (x k)) (uval (n+1) k))
    (CReal.add (uval (n+2) k) (uval n k))
  /-- **Per-node bridge** `wt k · uval p k ≈ ½·(tval p k − tval (p+2) k)`. -/
  uval_bridge : ∀ p k, CReal.Equiv
    (CReal.mul (wt k) (uval p k))
    (CReal.mul (CReal.ofQ' HalfPow.half)
      (CReal.add (tval p k) (CReal.neg (tval (p+2) k))))

/-- Forget the first-kind data to a plain `ChebOrthogonality.ChebRootData`. -/
def ChebRootDataT.toU {M : Nat} (D : ChebRootDataT M) : ChebRootData M where
  x := D.x
  uval := D.uval
  wt := D.wt
  uval_zero := D.uval_zero
  uval_fold := D.uval_fold

/-! ## 5. The first-kind power sums and the doubled-moment identity -/

/-- The first-kind power sum `S_j = Σ_{k<M} tval j k`. -/
def Sj {M : Nat} (D : ChebRootDataT M) (j : Nat) : CReal :=
  CReal.csum (fun k => D.tval j k) M

/-- `−(P + Q) ≈ (−P) + (−Q)` at `CReal` level (pointwise). -/
private theorem cneg_add (P Q : CReal) :
    CReal.Equiv (CReal.neg (CReal.add P Q)) (CReal.add (CReal.neg P) (CReal.neg Q)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show (-((P.approx p) + (Q.approx p))).eqv ((-(P.approx p)) + (-(Q.approx p)))
    exact Q'.neg_add_eqv (P.approx p) (Q.approx p))

/-- `csum` of a negation is the negation of the `csum`. -/
private theorem csum_neg (A : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum (fun k => CReal.neg (A k)) n) (CReal.neg (CReal.csum A n)) := by
  induction n with
  | zero => exact cEq_refl _
  | succ m ih =>
      -- csum (neg A) (m+1) = (csum (neg A) m) + (neg (A m))
      -- neg (csum A (m+1)) = neg ((csum A m) + (A m)) ≈ (neg (csum A m)) + (neg (A m))
      show CReal.Equiv (CReal.add (CReal.csum (fun k => CReal.neg (A k)) m) (CReal.neg (A m)))
        (CReal.neg (CReal.add (CReal.csum A m) (A m)))
      refine CReal.Equiv.trans (Pivot2.add_congr ih (cEq_refl _)) ?_
      exact CReal.Equiv.symm (cneg_add (CReal.csum A m) (A m))

/-- `Σ_k (a_k − b_k) ≈ (Σ a_k) − (Σ b_k)` for `CReal`. -/
private theorem csum_sub (A B : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum (fun k => CReal.add (A k) (CReal.neg (B k))) n)
      (CReal.add (CReal.csum A n) (CReal.neg (CReal.csum B n))) := by
  refine CReal.Equiv.trans (CRealAlg.csum_add A (fun k => CReal.neg (B k)) n) ?_
  exact Pivot2.add_congr (cEq_refl _) (csum_neg B n)

/-- **The doubled-moment identity** `Q_M(U_p) = ½·(S_p − S_{p+2})`, i.e. the
single-`U` moment is half the first-kind power-sum difference, from the per-node
bridge and `csum` linearity. -/
theorem moment_eq_half_Sdiff {M : Nat} (D : ChebRootDataT M) (p : Nat) :
    CReal.Equiv (moment D.toU p)
      (CReal.mul (CReal.ofQ' HalfPow.half) (CReal.add (Sj D p) (CReal.neg (Sj D (p+2))))) := by
  -- moment = Σ_k wt·uval p ≈ Σ_k ½(tval p − tval(p+2))
  --        ≈ ½·Σ_k (tval p − tval(p+2)) ≈ ½·(S_p − S_{p+2}).
  unfold moment weightedNodeSum ChebRootDataT.toU
  refine CReal.Equiv.trans (CRealContinuumAlg.csum_congr (fun k => D.uval_bridge p k) M) ?_
  refine CReal.Equiv.trans
    (CRealContinuumAlg.csum_const_mul (CReal.ofQ' HalfPow.half)
      (fun k => CReal.add (D.tval p k) (CReal.neg (D.tval (p+2) k))) M) ?_
  -- ½·Σ(tval p − tval(p+2)) ≈ ½·(S_p − S_{p+2})
  exact CRealContinuumAlg.cmul_congr_right (csum_sub (fun k => D.tval p k) (fun k => D.tval (p+2) k) M)

/-! ## 6. The named residual `TPowerSum` and the collapse it yields -/

/-- **The named residual — the first-kind Dirichlet power-sum collapse `(★)`.**
For the roots of `U_M`: `S_0 = M`, `S_2 = −1`, and `S_p = S_{p+2}` for
`0 < p ≤ M−1`.  The trig shadow is the closed Dirichlet sum
`Σ_{k=1}^{M} cos(jkπ/(M+1))`.  This is the ONLY general-`M` input the collapse
needs beyond the proved bridge. -/
def TPowerSum {M : Nat} (D : ChebRootDataT M) : Prop :=
  CReal.Equiv (Sj D 0) (CReal.ofQ' (Q'.ofNat M))
  ∧ CReal.Equiv (Sj D 2) (CReal.ofQ' (-(1 : Q')))
  ∧ (∀ p, 0 < p → p ≤ M - 1 → CReal.Equiv (Sj D p) (Sj D (p+2)))

/-- **`½·(M + 1) ≈ mkPos (M+1) 2` over `Q'`.**  Both sides have numerator `M+1`
and denominator `2`; the cross-multiplication is `(M+1)·2 = (M+1)·2`. -/
theorem half_times_succ (M : Nat) :
    (HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).eqv (Q'.mkPos ((M : Int) + 1) 2 (by decide)) := by
  -- Cross-multiplication form of `eqv`.
  show (HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).num
        * ((Q'.mkPos ((M : Int) + 1) 2 (by decide)).den : Int)
      = (Q'.mkPos ((M : Int) + 1) 2 (by decide)).num
        * ((HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).den : Int)
  -- Numerators.  (a*b).num = a.num*b.num ; (a+b).num = a.num*b.den + b.num*a.den (rfl).
  have hLnum : (HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).num = (M : Int) + 1 := by
    show HalfPow.half.num * ((Q'.ofNat M + (-(-(1 : Q')))).num) = (M : Int) + 1
    show (1 : Int) * (((Q'.ofNat M).num) * (((-(-(1 : Q'))).den : Int))
        + ((-(-(1 : Q'))).num) * ((Q'.ofNat M).den : Int)) = (M : Int) + 1
    show (1 : Int) * ((Int.ofNat M) * (1 : Int) + (1 : Int) * (1 : Int)) = (M : Int) + 1
    simp only [Int.ofNat_eq_natCast]; omega
  have hLden : ((HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).den : Int) = 2 := by
    show ((HalfPow.half.den * (Q'.ofNat M + (-(-(1 : Q')))).den : Nat) : Int) = 2
    show ((2 * 1 : Nat) : Int) = 2
    decide
  have hRnum : (Q'.mkPos ((M : Int) + 1) 2 (by decide)).num = (M : Int) + 1 :=
    Q'.mkPos_num ((M : Int) + 1) 2 (by decide)
  have hRden : ((Q'.mkPos ((M : Int) + 1) 2 (by decide)).den : Int) = 2 := by
    rw [Q'.mkPos_den ((M : Int) + 1) 2 (by decide)]; rfl
  rw [hLnum, hLden, hRnum, hRden]

/-- `X + (−X) ≈ czero` (additive inverse). -/
private theorem csub_self (X : CReal) : CReal.Equiv (CReal.add X (CReal.neg X)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show ((X.approx p) + (-(X.approx p))).eqv (0 : Q')
    exact Q'.add_neg_self_eqv (X.approx p))

/-- `c · czero ≈ czero`. -/
private theorem cmul_czero (c : CReal) : CReal.Equiv (CReal.mul c CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show ((c.approx p) * (0 : Q')).eqv (0 : Q')
    exact Q'.mul_zero_eqv (c.approx p))

/-- `½·(ofQ' M − ofQ'(−1)) ≈ ofQ' (mkPos (M+1) 2)`, the diagonal value. -/
private theorem half_M_plus_one (M : Nat) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' HalfPow.half)
        (CReal.add (CReal.ofQ' (Q'.ofNat M)) (CReal.neg (CReal.ofQ' (-(1 : Q'))))))
      (CReal.ofQ' (Q'.mkPos ((M : Int) + 1) 2 (by decide))) := by
  -- ofQ' M + (−ofQ'(−1)) = ofQ'(M + 1), then ½·ofQ'(M+1) = ofQ'(½·(M+1)) = ofQ'(mkPos(M+1) 2).
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right
      (show CReal.Equiv (CReal.add (CReal.ofQ' (Q'.ofNat M)) (CReal.neg (CReal.ofQ' (-(1 : Q')))))
        (CReal.ofQ' (Q'.ofNat M + (-(-(1 : Q')))))
        from cEq_refl _)) ?_
  -- ½·ofQ'(M + (−(−1))) ≈ ofQ'(mkPos (M+1) 2)
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (CRealContinuumAlg.cofQ'_mul HalfPow.half (Q'.ofNat M + (-(-(1 : Q')))))) ?_
  -- ofQ'(half·(M + 1)) ≈ ofQ'(mkPos(M+1) 2) : reduce to a Q'.eqv
  refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
  -- both approxes are the constants; reduce to half·(M+1) ≈ mkPos(M+1) 2
  show (HalfPow.half * (Q'.ofNat M + (-(-(1 : Q'))))).eqv (Q'.mkPos ((M : Int) + 1) 2 (by decide))
  -- half·(ofNat M + 1) ≈ mkPos (M+1) 2
  exact half_times_succ M

/-- **The collapse.**  Given the first-kind power-sum residual `TPowerSum`, the
full `ChebOrthogonality.PowerSumCollapse (D.toU)` holds: `Q_M(U_0) = (M+1)/2` and
`Q_M(U_p) = 0` for `0 < p ≤ M − 1`. -/
theorem powerSumCollapse_of_TPowerSum {M : Nat} (D : ChebRootDataT M)
    (h : TPowerSum D) :
    ChebOrthogonality.PowerSumCollapse D.toU := by
  obtain ⟨hS0, hS2, hSeq⟩ := h
  refine ⟨?_, ?_⟩
  · -- moment 0 ≈ ½(S_0 − S_2) ≈ ½(M − (−1)) ≈ (M+1)/2
    refine CReal.Equiv.trans (moment_eq_half_Sdiff D 0) ?_
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_right (Pivot2.add_congr hS0 (Pivot2.neg_congr hS2))) ?_
    exact half_M_plus_one M
  · -- moment p ≈ ½(S_p − S_{p+2}) ≈ ½·0 ≈ 0
    intro p hp hpM
    refine CReal.Equiv.trans (moment_eq_half_Sdiff D p) ?_
    -- S_p ≈ S_{p+2}, so S_p − S_{p+2} ≈ 0, hence ½·0 ≈ 0 (= czero).
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_right
        (Pivot2.add_congr (hSeq p hp hpM) (cEq_refl (CReal.neg (Sj D (p+2)))))) ?_
    -- ½·(S_{p+2} + (−S_{p+2})) ≈ ½·0 ≈ czero
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_right (csub_self (Sj D (p+2)))) ?_
    exact cmul_czero (CReal.ofQ' HalfPow.half)

/-! ## 7. A generic `ofQ'`-based node datum, and the fully-concrete `M = 2`

For rational nodes (the worst-case small order `M = 2` has the rational nodes
`±1/2`) the entire `ChebRootDataT` is `ofQ'` of `Q'`-evaluations.  The three
per-node fields then reduce to `Q'` facts: `uval_zero` to `U_0 = 1`, `uval_fold`
to the proved `twoX_U_fold`, and `uval_bridge` to the proved bridge
`weightU2_eq_Tdiff` (halved).  Only `TPowerSum` carries the node-specific
Dirichlet content, discharged by `decide` at `M = 2`. -/

/-- `half·(2·X) ≈ X` over `Q'` (since `half·2 ≈ 1`). -/
private theorem half_two_mul (X : Q') : HalfPow.half * ((2 : Q') * X) ≈ X := by
  refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv HalfPow.half 2 X)) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_right (HalfPow.half * 2) 1 X (by decide)) ?_
  exact one_mul_eqv X

/-- The per-node bridge over `Q'`: `wQ x · U_p x ≈ ½·(T_p x − T_{p+2} x)` (the
proved doubled bridge, halved). -/
theorem qbridge (x : Q') (p : Nat) :
    wQ x * U p x ≈ HalfPow.half * (T p x + (-(T (p+2) x))) := by
  -- 2·(wQ·U p) ≈ T p − T(p+2)  ⟹  wQ·U p ≈ ½·(T p − T(p+2)) via half·(2·X) = X.
  refine eqv_trans _ _ _ (eqv_symm (half_two_mul (wQ x * U p x))) ?_
  exact mul_eqv_congr_left _ _ _ (weightU2_eq_Tdiff x p)

/-- **Generic `ofQ'` node datum** from a rational node assignment `node : Nat → Q'`.
The per-node fields hold for ANY rational nodes (they are pure `U`/`T` identities);
node-specificity is confined to `TPowerSum`. -/
def fromQNodes (M : Nat) (node : Nat → Q') : ChebRootDataT M where
  x k := CReal.ofQ' (node k)
  uval p k := CReal.ofQ' (U p (node k))
  tval p k := CReal.ofQ' (T p (node k))
  wt k := CReal.ofQ' (wQ (node k))
  uval_zero k := by
    -- ofQ'(U 0 node) ≈ cone : U 0 = 1, cone = ofQ' 1
    show CReal.Equiv (CReal.ofQ' (U 0 (node k))) CReal.cone
    rw [U_zero]; exact cEq_refl _
  uval_fold n k := by
    -- (ofQ' 2 · ofQ' node)·ofQ'(U(n+1)) ≈ ofQ'(U(n+2)) + ofQ'(U n)
    show CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' 2) (CReal.ofQ' (node k))) (CReal.ofQ' (U (n+1) (node k))))
      (CReal.add (CReal.ofQ' (U (n+2) (node k))) (CReal.ofQ' (U n (node k))))
    -- LHS ≈ ofQ'((2·node)·U(n+1)) ; RHS = ofQ'(U(n+2) + U n).  Reduce to Q'.
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (((2 : Q') * node k) * U (n+1) (node k)).eqv (U (n+2) (node k) + U n (node k))
    exact twoX_U_fold n (node k)
  uval_bridge p k := by
    show CReal.Equiv
      (CReal.mul (CReal.ofQ' (wQ (node k))) (CReal.ofQ' (U p (node k))))
      (CReal.mul (CReal.ofQ' HalfPow.half)
        (CReal.add (CReal.ofQ' (T p (node k))) (CReal.neg (CReal.ofQ' (T (p+2) (node k))))))
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (wQ (node k) * U p (node k)).eqv
      (HalfPow.half * (T p (node k) + (-(T (p+2) (node k)))))
    exact qbridge (node k) p

/-- The `M = 2` node datum on the rational Gauss–Chebyshev nodes `±1/2`. -/
def rootData2 : ChebRootDataT 2 := fromQNodes 2 ChebOrthogonality.node2

/-- `Sj (fromQNodes M node) j ≈ ofQ'(Σ_{k<M} T_j(node k))` — the first-kind power
sum is `ofQ'` of the rational power sum. -/
theorem Sj_fromQNodes (M : Nat) (node : Nat → Q') (j : Nat) :
    CReal.Equiv (Sj (fromQNodes M node) j)
      (CReal.ofQ' (RationalTail.finSum (fun k => T j (node k)) M)) := by
  -- Sj = csum (fun k => ofQ'(T j (node k))) M ; its approx is finSum of T-values.
  refine SumOfSquares.Equiv_of_approx_eqv (fun pr => ?_)
  show ((Sj (fromQNodes M node) j).approx pr).eqv (RationalTail.finSum (fun k => T j (node k)) M)
  unfold Sj fromQNodes
  rw [CReal.csum_approx (fun k => CReal.ofQ' (T j (node k))) M pr]
  exact Q'.eqv_refl _

/-- **`TPowerSum` at `M = 2`** — the rational first-kind power sums at `±1/2`:
`S_0 = Σ T_0 = 2`, `S_2 = Σ T_2(±1/2) = 2·(2·¼−1) = −1`, and `S_1 = Σ T_1 =
½+(−½) = 0 = S_3` (`S_3 = Σ T_3(±1/2) = ½·(…)` also `0` by oddness).  All by
`decide` on the closed `Q'` finite sums. -/
theorem TPowerSum2 : TPowerSum rootData2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- S_0 ≈ ofQ' 2
    refine CReal.Equiv.trans (Sj_fromQNodes 2 ChebOrthogonality.node2 0) ?_
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (RationalTail.finSum (fun k => T 0 (ChebOrthogonality.node2 k)) 2).eqv (Q'.ofNat 2)
    decide
  · -- S_2 ≈ ofQ'(−1)
    refine CReal.Equiv.trans (Sj_fromQNodes 2 ChebOrthogonality.node2 2) ?_
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (RationalTail.finSum (fun k => T 2 (ChebOrthogonality.node2 k)) 2).eqv (-(1 : Q'))
    decide
  · -- S_p ≈ S_{p+2} for 0 < p ≤ 1, i.e. p = 1 : S_1 ≈ S_3 (both 0).
    intro p hp hpM
    have hp1 : p = 1 := by omega
    subst hp1
    refine CReal.Equiv.trans (Sj_fromQNodes 2 ChebOrthogonality.node2 1) ?_
    refine CReal.Equiv.symm (CReal.Equiv.trans (Sj_fromQNodes 2 ChebOrthogonality.node2 3) ?_)
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (RationalTail.finSum (fun k => T 3 (ChebOrthogonality.node2 k)) 2).eqv
      (RationalTail.finSum (fun k => T 1 (ChebOrthogonality.node2 k)) 2)
    decide

/-- **`PowerSumCollapse` at `M = 2`, via the T-route** — the named residual of
`ChebOrthogonality` inhabited for the `M = 2` node datum, entirely through the
first-kind power-sum bridge. -/
theorem powerSumCollapse2 : ChebOrthogonality.PowerSumCollapse rootData2.toU :=
  powerSumCollapse_of_TPowerSum rootData2 TPowerSum2

/-- **The `M = 2` diagonal reproduction** `Σ_k wt_k·U_0(x_k)·U_0(x_k) = (2+1)/2 =
3/2`, reproduced through the T-route (`powerSumCollapse2` feeding
`ChebOrthogonality.chebU_orthogonality_diag0`). -/
theorem orthogonality_diag0_M2 :
    CReal.Equiv (ChebOrthogonality.orthoSum rootData2.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((2 : Int) + 1) 2 (by decide))) :=
  ChebOrthogonality.chebU_orthogonality_diag0 rootData2.toU powerSumCollapse2

end YMGap.Continuum.PowerSumCollapse

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `omega`/`Nat`/`Int` helpers).  No
`Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a
non-decidable `Prop`. -/

#print axioms YMGap.Continuum.PowerSumCollapse.cheb_recurrence_match
#print axioms YMGap.Continuum.PowerSumCollapse.weightU2_recur
#print axioms YMGap.Continuum.PowerSumCollapse.Tdiff_recur
#print axioms YMGap.Continuum.PowerSumCollapse.add_core
#print axioms YMGap.Continuum.PowerSumCollapse.base1_identity
#print axioms YMGap.Continuum.PowerSumCollapse.weightU2_eq_Tdiff
#print axioms YMGap.Continuum.PowerSumCollapse.qbridge
#print axioms YMGap.Continuum.PowerSumCollapse.moment_eq_half_Sdiff
#print axioms YMGap.Continuum.PowerSumCollapse.half_times_succ
#print axioms YMGap.Continuum.PowerSumCollapse.powerSumCollapse_of_TPowerSum
#print axioms YMGap.Continuum.PowerSumCollapse.Sj_fromQNodes
#print axioms YMGap.Continuum.PowerSumCollapse.TPowerSum2
#print axioms YMGap.Continuum.PowerSumCollapse.powerSumCollapse2
#print axioms YMGap.Continuum.PowerSumCollapse.orthogonality_diag0_M2
