/-
# Wall 2 — the differentiated Jacobi-triple-product residual (G2)

This module builds the `K_t`-side of the residual convergence `Rtrunc M ≈ R`
named in `UTelescope.Kt_nonneg_of_residual`, and characterises sharply the single
analytic obligation that remains.

## What is GENUINELY closed here (new, axiom-clean content)

1. **The quadratic–geometric majorant `Σ (n+1)² (a·a)ⁿ` summability.**  The
   `K_t` series `K_t(x) = a^{-1} Σ_{n≥1} n·a^{n²}·U_{n-1}(x)` has term magnitude
   `|(n+1)·a^{(n+1)²}·U_n(x)| ≤ (n+1)²·a^{(n+1)²}` (using `|U_n|≤n+1`,
   `ChebU.absU_le`).  The polynomial factor `(n+1)²` is absorbed into the
   super-geometric Gaussian decay `a^{(n+1)²}` by SQUARING the existing
   multiplicative Bernoulli bound `bernoulli_pow` (`HKConvGen`): from
   `(1+n(1−a))·aⁿ ≤ 1` one gets `n·aⁿ ≤ 1/(1−a)`, hence (squaring)
   `n²·(a·a)ⁿ ≤ 1/(1−a)²` — closed here as `nsq_aa_pow_le`.  Combined with
   `a^{(n+1)²} ≤ a^{(n+1)}·(a·a)ⁿ` (Gaussian-vs-geometric, `gauss_le_geo`) this
   gives the geometric majorant `(n+1)²·a^{(n+1)²} ≤ Cmaj a · aⁿ` at base `a`
   (`dTermMaj_le`), exactly the `pow_base_le`/geometric-engine interface.

2. **`Dseries M = Σ_{n<M} dTerm a x n` as a convergent `CReal`** for ALL
   `a ∈ (0,1)`, `−1 ≤ x ≤ 1`, with explicit base-`a` modulus
   (`dSeriesCReal`, via `HKConvGen.crealOfGeoIncrementBase`).  This is the
   genuine constructive realisation of the heat-kernel series `K_t` (up to the
   rational prefactor `a^{-1}`); its `approx N = dPartial a x N`.

3. **The conditional closure `Kt ≥ 0`** (`Kt_geRat_zero_of_diff`): GIVEN the
   single residual identity `(DIFF)` — the differentiated-JTP equality of the
   `Dseries` limit with the product object `R = ϑ₃·S` — `K_t ≥ 0` follows, by
   feeding `dSeriesCReal`, `R_geRat_zero_gen`, and the residual into
   `UTelescope.Kt_nonneg_of_residual`.

## The ONE remaining obligation, stated sharply (honest, AGENTS.md Rule 6)

`(DIFF)` / `Rtrunc M ≈ R` is **NOT** plumbing: it is the term-by-term
differentiation of the convergent JTP product (a double-limit interchange
`lim_h lim_L = lim_L lim_h`), equivalently the differentiated-Jacobi identity
`Σ n a^{n²} sin nθ = (sin θ/2)·ϑ₃·S`.  It introduces no new POSITIVITY content
(positivity is already in `ThetaConvGen.R_geRat_zero_gen`); it is the single
analytic engine still required.  We expose it as the named `Prop` `DiffJTP`
(NOT discharged) and prove only the conditional `DiffJTP → K_t ≥ 0`.  The
explicit log-derivative modulus that a constructive proof of `DiffJTP` would
carry is `O((a·a)ᵏ)` (documented in `docs/jtp-convergence-notes.md §2.3`); the
`K_t`-side geometric modulus needed to even STATE the residual at the `CReal`
level is delivered here (item 2).

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`.  `DiffJTP` is a hypothesis, not a `sorry`.
-/

import YMGap.Continuum.UTelescope
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.DiffProduct
import YMGap.Constructive.Reals

namespace YMGap.Continuum.JTPIdentity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HKPos
open YMGap.Continuum.Cheb
open YMGap.Constructive.RationalTail

/-! ## 1. The quadratic–geometric majorant `n²·(a·a)ⁿ ≤ 1/(1−a)²`

The existing multiplicative Bernoulli `HKConvGen.bernoulli_pow` gives
`bScale (1+(−a)) n · aⁿ ≤ 1`, and `ofNat n · (1−a) ≤ bScale (1+(−a)) n`
(`ofNat_mul_le_bScale`).  Chaining: `(ofNat n · (1−a)) · aⁿ ≤ 1`, i.e.
`ofNat n · aⁿ ≤ 1/(1−a)` after dividing by `1−a > 0`.  Squaring gives the
quadratic bound. -/

/-- `0 ≤ ofNat n` for every `n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- `g a = 1 + (−a) = 1 − a`, the Bernoulli gap. -/
def gA (a : Q') : Q' := 1 + (-a)

theorem gA_pos {a : Q'} (ha1 : a < (1 : Q')) : (0 : Q') < gA a := HKPos.one_sub_pos ha1

theorem gA_nonneg {a : Q'} (ha1 : a < (1 : Q')) : (0 : Q') ≤ gA a := Q'.le_of_lt (gA_pos ha1)

/-- **The linear bound `(ofNat n · (1−a)) · aⁿ ≤ 1`.**  Directly from
`ofNat n · (1−a) ≤ bScale (1+(−a)) n` (`ofNat_mul_le_bScale`) and the
multiplicative Bernoulli `bScale (1+(−a)) n · aⁿ ≤ 1` (`bernoulli_pow`). -/
theorem n_gA_pow_le_one {a : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a < (1 : Q')) (n : Nat) :
    (Q'.ofNat n * gA a) * a ^ n ≤ (1 : Q') := by
  have hgnn : (0 : Q') ≤ gA a := gA_nonneg ha1
  have hpow_nn : (0 : Q') ≤ a ^ n := Q'.pow_nonneg a ha0 n
  -- (ofNat n · g) · aⁿ ≤ (bScale g n) · aⁿ ≤ 1
  have h1 : (Q'.ofNat n * gA a) * a ^ n ≤ bScale (gA a) n * a ^ n :=
    Q'.mul_le_mul_of_nonneg_right _ _ (a ^ n)
      (HKConvGen.ofNat_mul_le_bScale hgnn n) hpow_nn
  exact Q'.le_trans' _ _ _ h1
    (HKConvGen.bernoulli_pow ha0 (Q'.le_of_lt ha1) n)

/-- `divPos 1 (gA a)` (`= 1/(1−a)`) is positive for `a < 1`. -/
theorem invG_pos {a : Q'} (ha1 : a < (1 : Q')) : (0 : Q') < HKConv.divPos 1 (gA a) :=
  HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)

theorem invG_nonneg {a : Q'} (ha1 : a < (1 : Q')) : (0 : Q') ≤ HKConv.divPos 1 (gA a) :=
  Q'.le_of_lt (invG_pos ha1)

/-- **The linear majorant `ofNat n · aⁿ ≤ 1/(1−a)`.**  From `n_gA_pow_le_one`
multiplied through by `1/(1−a)` and the cancellation `(1/(1−a))·(1−a) ≃ 1`. -/
theorem n_pow_le_invG {a : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a < (1 : Q')) (n : Nat) :
    Q'.ofNat n * a ^ n ≤ HKConv.divPos 1 (gA a) := by
  have hgnum : 0 < (gA a).num := CReal.num_pos_of_pos (gA_pos ha1)
  have hInv_nn : (0 : Q') ≤ HKConv.divPos 1 (gA a) := invG_nonneg ha1
  -- Multiply `n_gA_pow_le_one` by H := 1/(1−a) ≥ 0:
  --   ((ofNat n · g) · aⁿ)·H ≤ 1·H = H,  and LHS ≃ (ofNat n · aⁿ)·(g·H) ≃ ofNat n · aⁿ.
  have hbase := n_gA_pow_le_one ha0 ha1 n
  have hmul : ((Q'.ofNat n * gA a) * a ^ n) * HKConv.divPos 1 (gA a)
      ≤ (1 : Q') * HKConv.divPos 1 (gA a) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hInv_nn
  -- RHS ≃ H
  have hR : ((1 : Q') * HKConv.divPos 1 (gA a)).eqv (HKConv.divPos 1 (gA a)) :=
    Q'.one_mul_eqv _
  -- LHS ≃ ofNat n · aⁿ  (since (g·H) ≃ 1)
  have hgH : (gA a * HKConv.divPos 1 (gA a)).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (gA a) (HKConv.divPos 1 (gA a)))
      (HKConv.divPos_mul_eqv hgnum)
  have hL : (((Q'.ofNat n * gA a) * a ^ n) * HKConv.divPos 1 (gA a)).eqv
      (Q'.ofNat n * a ^ n) := by
    -- ((N·g)·p)·H ≃ (N·p)·(g·H) ≃ (N·p)·1 ≃ N·p
    -- first regroup ((N·g)·p)·H ≃ (N·p)·(g·H)
    have step1 : (((Q'.ofNat n * gA a) * a ^ n) * HKConv.divPos 1 (gA a)).eqv
        ((Q'.ofNat n * a ^ n) * (gA a * HKConv.divPos 1 (gA a))) := by
      -- (N·g)·p ≃ (N·p)·g, then ((N·p)·g)·H ≃ (N·p)·(g·H)
      have e1 : ((Q'.ofNat n * gA a) * a ^ n).eqv ((Q'.ofNat n * a ^ n) * gA a) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat n) (gA a) (a ^ n)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ (Q'.mul_comm_eqv (gA a) (a ^ n))) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (a ^ n) (gA a))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (HKConv.divPos 1 (gA a)) e1) ?_
      exact Q'.mul_assoc_eqv (Q'.ofNat n * a ^ n) (gA a) (HKConv.divPos 1 (gA a))
    refine Q'.eqv_trans _ _ _ step1 ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat n * a ^ n) _ _ hgH) ?_
    exact Q'.mul_one_eqv (Q'.ofNat n * a ^ n)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) ?_
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hR)

/-- `a^(n+n) ≃ (a·a)^n`.  (`aⁿ·aⁿ ≃ a^(n+n)` then regroup; induction on `n`.) -/
theorem aa_pow_eqv (a : Q') (n : Nat) : (a ^ (n + n)).eqv ((a * a) ^ n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ k ih =>
    have he : (k + 1) + (k + 1) = (k + k) + 2 := by omega
    show (a ^ ((k + 1) + (k + 1))).eqv ((a * a) * (a * a) ^ k)
    rw [he]
    refine Q'.eqv_trans _ _ _ (Q'.pow_add_eqv a (k + k) 2) ?_
    have ha2 : (a ^ 2).eqv (a * a) := by
      show (a * (a * (1 : Q'))).eqv (a * a)
      exact Q'.mul_eqv_congr_left a _ _ (Q'.mul_one_eqv a)
    refine Q'.eqv_trans _ _ _
      (Cheb.mul_eqv_congr _ _ _ _ ih ha2) ?_
    exact Q'.mul_comm_eqv ((a * a) ^ k) (a * a)

/-- **The quadratic–geometric majorant `(ofNat n · ofNat n)·(a·a)ⁿ ≤ H²`**,
`H = 1/(1−a)`.  Squaring `n_pow_le_invG`: `(ofNat n · aⁿ)² ≤ H²`, and
`(ofNat n · aⁿ)² ≃ (ofNat n · ofNat n)·(a·a)ⁿ`. -/
theorem nsq_aa_pow_le {a : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a < (1 : Q')) (n : Nat) :
    (Q'.ofNat n * Q'.ofNat n) * (a * a) ^ n
      ≤ HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a) := by
  have hnp_nn : (0 : Q') ≤ Q'.ofNat n * a ^ n :=
    Q'.mul_nonneg _ _ (ofNat_nonneg n) (Q'.pow_nonneg a ha0 n)
  have hInv_nn : (0 : Q') ≤ HKConv.divPos 1 (gA a) := invG_nonneg ha1
  have hbase := n_pow_le_invG ha0 ha1 n
  -- (N·aⁿ)·(N·aⁿ) ≤ H·H
  have hsq : (Q'.ofNat n * a ^ n) * (Q'.ofNat n * a ^ n)
      ≤ HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat n * a ^ n) hbase hnp_nn) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ (HKConv.divPos 1 (gA a)) hbase hInv_nn
  -- (N·aⁿ)·(N·aⁿ) ≃ (N·N)·(aⁿ·aⁿ) ≃ (N·N)·(a·a)ⁿ
  have hre : ((Q'.ofNat n * a ^ n) * (Q'.ofNat n * a ^ n)).eqv
      ((Q'.ofNat n * Q'.ofNat n) * (a * a) ^ n) := by
    -- (N·p)·(N·p) ≃ (N·N)·(p·p) using the int_regroup-style commute, then p·p ≃ (a·a)ⁿ.
    have hcomm : ((Q'.ofNat n * a ^ n) * (Q'.ofNat n * a ^ n)).eqv
        ((Q'.ofNat n * Q'.ofNat n) * (a ^ n * a ^ n)) := by
      -- (N·p)·(N·p) ≃ N·(p·(N·p)) ≃ N·((p·N)·p) ≃ N·((N·p)·p) ≃ (N·N)·(p·p)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (Q'.ofNat n) (a ^ n) (Q'.ofNat n * a ^ n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (a ^ n) (Q'.ofNat n) (a ^ n)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
          (Q'.mul_eqv_congr_right _ _ (a ^ n) (Q'.mul_comm_eqv (a ^ n) (Q'.ofNat n)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
          (Q'.mul_assoc_eqv (Q'.ofNat n) (a ^ n) (a ^ n))) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.ofNat n) (a ^ n * a ^ n))
    -- aⁿ·aⁿ ≃ (a·a)ⁿ : aⁿ·aⁿ ≃ a^(n+n), and (a·a)ⁿ ≃ a^(n+n)
    have hpp : (a ^ n * a ^ n).eqv ((a * a) ^ n) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv a n n)) ?_
      -- a^(n+n) ≃ (a·a)ⁿ : induction-free via mul_pow-style; use pow_mul-equivalent.
      exact aa_pow_eqv a n
    refine Q'.eqv_trans _ _ _ hcomm ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat n * Q'.ofNat n) _ _ hpp
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hre) hsq

/-! ## 2. The Gaussian-vs-geometric exponent bound `a^{(n+1)²} ≤ a^{(n+1)}·(a·a)ⁿ`

`(n+1)² = (n+1) + 2·(n+1−1)·? ` — concretely `(n+1)² = (n+1) + (n+1)·n` and
`(n+1)·n ≥ 2n`, so `a^{(n+1)²} = a^{(n+1)}·a^{(n+1)·n} ≤ a^{(n+1)}·a^{2n}
= a^{(n+1)}·(a·a)ⁿ` for `a ∈ (0,1)` (powers antitone). -/

/-- `(n+1)·n` (the Gaussian–geometric exponent gap) is `≥ 2·n`. -/
theorem succ_mul_ge_two_mul (n : Nat) : 2 * n ≤ (n + 1) * n := by
  have h : (n + 1) * n = n * n + n := Nat.succ_mul n n
  -- 2n ≤ n*n + n  ⟺  n ≤ n*n, which holds since n ≤ n*n for all n.
  have hn : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · omega
    · calc n = 1 * n := (Nat.one_mul n).symm
        _ ≤ n * n := Nat.mul_le_mul_right n hp
  omega

/-- **`a^{(n+1)²} ≤ a^{(n+1)}·(a·a)ⁿ`** for `0 < a < 1`.  Splits the exponent
`(n+1)² = (n+1) + (n+1)·n` and dominates `a^{(n+1)·n} ≤ a^{2n} = (a·a)ⁿ`. -/
theorem gauss_le_geo {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (n : Nat) :
    a ^ ((n + 1) * (n + 1)) ≤ a ^ (n + 1) * (a * a) ^ n := by
  -- (n+1)² = (n+1) + (n+1)·n
  have hexp : (n + 1) * (n + 1) = (n + 1) + (n + 1) * n := by
    rw [Nat.mul_succ]; omega
  rw [hexp]
  -- a^((n+1)+(n+1)·n) ≃ a^(n+1)·a^((n+1)·n) ≤ a^(n+1)·a^(2n) = a^(n+1)·(a·a)^n
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.pow_add_eqv a (n + 1) ((n + 1) * n))) ?_
  refine Q'.mul_le_mul_of_nonneg_left _ _ (a ^ (n + 1)) ?_
    (Q'.pow_nonneg a (Q'.le_of_lt ha0) (n + 1))
  -- a^((n+1)·n) ≤ a^(2n) (antitone, since 2n ≤ (n+1)·n) ; a^(2n) ≃ (a·a)^n
  refine Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt ha0) (Q'.le_of_lt ha1)
      (succ_mul_ge_two_mul n)) ?_
  -- a^(2n) = a^(n+n) ≃ (a·a)^n
  have h2n : 2 * n = n + n := by omega
  rw [h2n]
  exact Q'.le_of_eqv (aa_pow_eqv a n)

/-! ## 3. The `K_t`-side partial sums `Dseries M = Σ_{n<M} dTerm a x n` as a `CReal`

`dTerm a x n = ofNat(n+1)·a^{(n+1)²}·U_n(x)` is the `n`-th heat-kernel summand
(`K_t = a^{-1}·Σ`, the rational prefactor `a^{-1}` is carried separately).  Its
two-sided magnitude bound `|dTerm n| ≤ ofNat(n+1)²·a^{(n+1)²}` (via `|U_n|≤n+1`,
`ChebU.absU_le`) is dominated by the geometric majorant `Cmaj a · aⁿ`
(`dTermMaj_le`), so the partial sums converge as a `CReal` via the general-base
engine. -/

/-- The `n`-th `K_t` summand `ofNat(n+1)·a^{(n+1)²}·U_n(x)`. -/
def dTerm (a x : Q') (n : Nat) : Q' :=
  (Q'.ofNat (n + 1) * a ^ ((n + 1) * (n + 1))) * U n x

/-- The `K_t`-side partial sum `Σ_{n<M} dTerm a x n`. -/
def dPartial (a x : Q') (M : Nat) : Q' := finSum (dTerm a x) M

@[simp] theorem dPartial_succ (a x : Q') (M : Nat) :
    dPartial a x (M + 1) = dPartial a x M + dTerm a x M := rfl

/-- The geometric-majorant constant `Cmaj a = (a · (H·H)) · (1/(a·a))`,
`H = 1/(1−a)`.  (`= a·H²/(a·a)`, the constant in `(n+1)²·a^{(n+1)²} ≤ Cmaj·aⁿ`.) -/
def Cmaj (a : Q') : Q' :=
  (a * (HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))) * HKConv.divPos 1 (a * a)

theorem Cmaj_nonneg {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    (0 : Q') ≤ Cmaj a := by
  refine Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.le_of_lt ha0)
    (Q'.mul_nonneg _ _ (invG_nonneg ha1) (invG_nonneg ha1))) ?_
  exact HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))

/-- The quadratic majorant shifted to index `n+1`:
`ofNat(n+1)·ofNat(n+1)·(a·a)ⁿ ≤ (H·H)·(1/(a·a))`.  From `nsq_aa_pow_le` at
`n+1` (`(n+1)²·(a·a)^{n+1} ≤ H²`) divided by `(a·a)`. -/
theorem nsq_succ_aa_pow_le {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (n : Nat) :
    (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a * a) ^ n
      ≤ (HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a)) * HKConv.divPos 1 (a * a) := by
  have haa0 : (0 : Q') < a * a := HKPos.q_mul_pos ha0 ha0
  have haanum : 0 < (a * a).num := CReal.num_pos_of_pos haa0
  have hInvaa_nn : (0 : Q') ≤ HKConv.divPos 1 (a * a) :=
    HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))
  -- base : (n+1)²·(a·a)^{n+1} ≤ H²
  have hbase := nsq_aa_pow_le (Q'.le_of_lt ha0) ha1 (n + 1)
  -- multiply by 1/(a·a) ≥ 0
  have hmul : ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a * a) ^ (n + 1))
        * HKConv.divPos 1 (a * a)
      ≤ (HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a)) * HKConv.divPos 1 (a * a) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hInvaa_nn
  refine Q'.le_trans' _ _ _ ?_ hmul
  -- LHS target ≃ ((N·N)·(a·a)^{n+1})·(1/(a·a))   [since (a·a)ⁿ ≃ (a·a)^{n+1}·(1/(a·a))]
  refine Q'.le_of_eqv ?_
  -- (N·N)·(a·a)ⁿ ≃ ((N·N)·(a·a)^{n+1})·(1/(a·a))
  -- since (a·a)^{n+1}·(1/(a·a)) ≃ (a·a)ⁿ
  have hcancel : ((a * a) ^ (n + 1) * HKConv.divPos 1 (a * a)).eqv ((a * a) ^ n) := by
    -- (a·a)^{n+1} = (a·a)·(a·a)ⁿ ; (a·a)·(1/(a·a)) ≃ 1
    show ((a * a) * (a * a) ^ n * HKConv.divPos 1 (a * a)).eqv ((a * a) ^ n)
    -- ((a·a)·p)·D ≃ p·((a·a)·D) ≃ p·1 ≃ p
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (HKConv.divPos 1 (a * a))
        (Q'.mul_comm_eqv (a * a) ((a * a) ^ n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv ((a * a) ^ n) (a * a) (HKConv.divPos 1 (a * a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ((a * a) ^ n) _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a * a) (HKConv.divPos 1 (a * a)))
          (HKConv.divPos_mul_eqv haanum))) ?_
    exact Q'.mul_one_eqv ((a * a) ^ n)
  -- (N·N)·(a·a)ⁿ ≃ (N·N)·((a·a)^{n+1}·(1/(a·a))) ≃ ((N·N)·(a·a)^{n+1})·(1/(a·a))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) _ _ (Q'.eqv_symm hcancel)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) ((a * a) ^ (n + 1))
      (HKConv.divPos 1 (a * a)))

/-- **The geometric term-majorant `ofNat(n+1)²·a^{(n+1)²} ≤ Cmaj a · aⁿ`.**
Chains `gauss_le_geo` (`a^{(n+1)²} ≤ a^{n+1}·(a·a)ⁿ`), the quadratic bound
`nsq_succ_aa_pow_le`, and `a^{n+1} = a·aⁿ`. -/
theorem dTermMaj_le {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (n : Nat) :
    (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * a ^ ((n + 1) * (n + 1))
      ≤ Cmaj a * a ^ n := by
  have hNsq_nn : (0 : Q') ≤ Q'.ofNat (n + 1) * Q'.ofNat (n + 1) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (ofNat_nonneg _)
  -- Step 1: (N·N)·a^{(n+1)²} ≤ (N·N)·(a^{n+1}·(a·a)ⁿ)
  have step1 : (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * a ^ ((n + 1) * (n + 1))
      ≤ (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a ^ (n + 1) * (a * a) ^ n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (gauss_le_geo ha0 ha1 n) hNsq_nn
  refine Q'.le_trans' _ _ _ step1 ?_
  -- (N·N)·(a^{n+1}·(a·a)ⁿ) ≃ a^{n+1}·((N·N)·(a·a)ⁿ) ≤ a^{n+1}·(H²·(1/(a·a)))
  have hreassoc : ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a ^ (n + 1) * (a * a) ^ n)).eqv
      (a ^ (n + 1) * ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a * a) ^ n)) := by
    -- (N·N)·(p·q) ≃ (N·N)·(q·p) ≃ ... ≃ p·((N·N)·q)   with p = a^{n+1}, q = (a·a)ⁿ
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (a ^ (n + 1)) ((a * a) ^ n))) ?_
    -- (N·N)·((a·a)ⁿ·a^{n+1}) ≃ ((N·N)·(a·a)ⁿ)·a^{n+1} ≃ a^{n+1}·((N·N)·(a·a)ⁿ)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) ((a * a) ^ n)
        (a ^ (n + 1)))) ?_
    exact Q'.mul_comm_eqv ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a * a) ^ n) (a ^ (n + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
  have hap_nn : (0 : Q') ≤ a ^ (n + 1) := Q'.pow_nonneg a (Q'.le_of_lt ha0) (n + 1)
  have step2 : a ^ (n + 1) * ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * (a * a) ^ n)
      ≤ a ^ (n + 1) * ((HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
          * HKConv.divPos 1 (a * a)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (nsq_succ_aa_pow_le ha0 ha1 n) hap_nn
  refine Q'.le_trans' _ _ _ step2 ?_
  -- a^{n+1}·K ≃ (a·aⁿ)·K ≃ (a·K)·aⁿ = Cmaj·aⁿ,  K = H²·(1/(a·a))
  refine Q'.le_of_eqv ?_
  -- a^{n+1} = a·aⁿ
  show (a ^ (n + 1) * ((HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
          * HKConv.divPos 1 (a * a))).eqv (Cmaj a * a ^ n)
  -- a^{n+1} = a·aⁿ (defeq via pow_succ), so LHS = (a·aⁿ)·K
  show ((a * a ^ n) * ((HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
          * HKConv.divPos 1 (a * a))).eqv (Cmaj a * a ^ n)
  -- (a·aⁿ)·K ≃ aⁿ·(a·K) ≃ (a·K)·aⁿ  and Cmaj = a·K (defeq)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a (a ^ n))) ?_
  -- ((aⁿ·a)·K) ≃ aⁿ·(a·K)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (a ^ n) a ((HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
          * HKConv.divPos 1 (a * a))) ?_
  -- aⁿ·(a·K) ≃ (a·K)·aⁿ ;  Cmaj = (a·(H·H))·(1/(a·a)), so (a·K) ≃ Cmaj via assoc
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (a ^ n) (a * ((HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
          * HKConv.divPos 1 (a * a)))) ?_
  -- (a·((H·H)·(1/(a·a))))·aⁿ ≃ ((a·(H·H))·(1/(a·a)))·aⁿ = Cmaj·aⁿ
  refine Q'.mul_eqv_congr_right _ _ (a ^ n) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv a (HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a))
      (HKConv.divPos 1 (a * a)))

/-! ### The two-sided single-step increment bound `|dTerm l| ≤ Cmaj a · aˡ` -/

/-- The nonnegative coefficient `coef a l = ofNat(l+1)·a^{(l+1)²} ≥ 0`. -/
theorem dCoef_nonneg {a : Q'} (ha0 : (0 : Q') < a) (l : Nat) :
    (0 : Q') ≤ Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1)) :=
  Q'.mul_nonneg _ _ (ofNat_nonneg _) (Q'.pow_nonneg a (Q'.le_of_lt ha0) _)

/-- `coef·ofNat(l+1) ≤ Cmaj a · aˡ` — the magnitude bound, via `dTermMaj_le`
after reassociating `coef·ofNat(l+1) = ofNat(l+1)²·a^{(l+1)²}`. -/
theorem dCoef_mul_le {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (l : Nat) :
    (Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) * Q'.ofNat (l + 1)
      ≤ Cmaj a * a ^ l := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (dTermMaj_le (x := x) ha0 ha1 l)
  -- (N·p)·N ≃ (N·N)·p
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat (l + 1)) (a ^ ((l + 1) * (l + 1))) (Q'.ofNat (l + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (l + 1)) _ _
      (Q'.mul_comm_eqv (a ^ ((l + 1) * (l + 1))) (Q'.ofNat (l + 1)))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (Q'.ofNat (l + 1)) (Q'.ofNat (l + 1)) (a ^ ((l + 1) * (l + 1))))

/-- **Upper increment bound** `dTerm a x l ≤ Cmaj a · aˡ` on `[−1,1]`. -/
theorem dTerm_le {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    dTerm a x l ≤ Cmaj a * a ^ l := by
  have hcoef_nn : (0 : Q') ≤ Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1)) :=
    dCoef_nonneg ha0 l
  obtain ⟨hUub, hUlb⟩ := ChebU.absU_le l x hx1 hx
  -- dTerm = coef · U l x ≤ coef · ofNat(l+1)
  have hbd : dTerm a x l ≤ (Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) * Q'.ofNat (l + 1) :=
    Q'.mul_le_of_bounds hcoef_nn (ofNat_nonneg _)
      (by -- −coef ≤ coef
          have : -(Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) ≤ (0 : Q') := by
            have h := Q'.neg_le_neg hcoef_nn
            rwa [show (-(0 : Q')) = 0 from rfl] at h
          exact Q'.le_trans' _ _ _ this hcoef_nn)
      (Q'.le_refl' _) hUlb hUub
  exact Q'.le_trans' _ _ _ hbd (dCoef_mul_le (x := x) ha0 ha1 l)

/-- **Lower increment bound** `−(dTerm a x l) ≤ Cmaj a · aˡ` on `[−1,1]`. -/
theorem neg_dTerm_le {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    -(dTerm a x l) ≤ Cmaj a * a ^ l := by
  have hcoef_nn : (0 : Q') ≤ Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1)) :=
    dCoef_nonneg ha0 l
  obtain ⟨hUub, hUlb⟩ := ChebU.absU_le l x hx1 hx
  -- −dTerm = coef · (−U l x) ; −U l x ∈ [−ofNat(l+1), ofNat(l+1)]
  have hndlo : -(Q'.ofNat (l + 1)) ≤ -(U l x) := Q'.neg_le_neg hUub
  have hndhi : -(U l x) ≤ Q'.ofNat (l + 1) :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hUlb) (Q'.le_of_eqv (Q'.neg_neg_eqv (Q'.ofNat (l + 1))))
  have hbd : (Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) * (-(U l x))
      ≤ (Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) * Q'.ofNat (l + 1) :=
    Q'.mul_le_of_bounds hcoef_nn (ofNat_nonneg _)
      (by have : -(Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) ≤ (0 : Q') := by
            have h := Q'.neg_le_neg hcoef_nn
            rwa [show (-(0 : Q')) = 0 from rfl] at h
          exact Q'.le_trans' _ _ _ this hcoef_nn)
      (Q'.le_refl' _) hndlo hndhi
  -- coef·(−U) ≃ −(coef·U) = −dTerm
  have heq : ((Q'.ofNat (l + 1) * a ^ ((l + 1) * (l + 1))) * (-(U l x))).eqv
      (-(dTerm a x l)) := Q'.mul_neg_eqv _ (U l x)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) ?_
  exact Q'.le_trans' _ _ _ hbd (dCoef_mul_le (x := x) ha0 ha1 l)

/-! ### `Dseries` as a convergent `CReal` -/

/-- **THE `K_t`-side series as a convergent `CReal`** for ALL `a ∈ (0,1)`,
`−1 ≤ x ≤ 1`.  `approx N = dPartial a x N = Σ_{n<N} dTerm a x n`, with the
explicit base-`a` geometric modulus at constant `Cmaj a`.  This is the genuine
constructive realisation of `K_t·a` (the heat-kernel Chebyshev series, modulo the
rational prefactor `a^{-1}`). -/
def dSeriesCReal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal :=
  HKConvGen.crealOfGeoIncrementBase (dPartial a x) (Cmaj a) a
    (Cmaj_nonneg ha0 ha1) ha0 ha1
    -- hup : dPartial (l+1) ≤ dPartial l + geoIncrBase (Cmaj a) a l
    (fun l => by
      rw [dPartial_succ]
      exact Q'.add_le_add_left (dPartial a x l) (dTerm a x l)
        (HKConvGen.geoIncrBase (Cmaj a) a l) (dTerm_le ha0 ha1 hx hx1 l))
    -- hlo : dPartial l ≤ dPartial (l+1) + geoIncrBase (Cmaj a) a l
    (fun l => by
      rw [dPartial_succ]
      -- dPartial l ≤ (dPartial l + dTerm l) + Cmaj·aˡ  ⟸  0 ≤ dTerm l + Cmaj·aˡ
      refine Q'.le_trans' _ _ _ ?_
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.add_assoc_eqv (dPartial a x l) (dTerm a x l)
            (HKConvGen.geoIncrBase (Cmaj a) a l))))
      refine Q'.add_le_self_of_nonneg (dPartial a x l)
        (dTerm a x l + HKConvGen.geoIncrBase (Cmaj a) a l) ?_
      -- 0 ≤ dTerm l + Cmaj·aˡ  ⟺  −(Cmaj·aˡ) ≤ dTerm l
      have hlo := neg_dTerm_le ha0 ha1 hx hx1 l
      -- −(Cmaj·aˡ) ≤ dTerm l  (from −dTerm ≤ Cmaj·aˡ)
      have hlo' : -(Cmaj a * a ^ l) ≤ dTerm a x l := by
        have h1 : -(dTerm a x l) ≤ Cmaj a * a ^ l := hlo
        have h2 := Q'.neg_le_neg h1
        refine Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.neg_neg_eqv (dTerm a x l)))
      have h3 : -(Cmaj a * a ^ l) + Cmaj a * a ^ l
          ≤ dTerm a x l + HKConvGen.geoIncrBase (Cmaj a) a l :=
        Q'.add_le_add_right _ _ (Cmaj a * a ^ l) hlo'
      refine Q'.le_trans' _ _ _ ?_ h3
      exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (Cmaj a * a ^ l)))
    -- modulus
    (fun ε hε => by
      have hKpos : 0 < (Cmaj a * HKConv.divPos 1 (1 + (-a))).num := by
        have hCmaj_pos : (0 : Q') < Cmaj a := by
          have hHH : (0 : Q') < HKConv.divPos 1 (gA a) * HKConv.divPos 1 (gA a) :=
            HKPos.q_mul_pos (invG_pos ha1) (invG_pos ha1)
          have hInvaa : (0 : Q') < HKConv.divPos 1 (a * a) :=
            HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
          exact HKPos.q_mul_pos (HKPos.q_mul_pos ha0 hHH) hInvaa
        have hDpos : (0 : Q') < HKConv.divPos 1 (1 + (-a)) :=
          HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
        exact CReal.num_pos_of_pos (HKPos.q_mul_pos hCmaj_pos hDpos)
      refine ⟨HKConv.divPos ε (Cmaj a * HKConv.divPos 1 (1 + (-a))),
        HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
      exact HKConv.divPos_mul_eqv hKpos)

@[simp] theorem dSeriesCReal_approx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) :
    (dSeriesCReal ha0 ha1 hx hx1).approx N = dPartial a x N := rfl

/-! ## 4. The differentiated-JTP residual and the conditional `K_t ≥ 0`

`R = ϑ₃·S` is the manifestly-nonnegative product object (`ThetaConvGen`), with
limit `≥ 0` for ALL `a ∈ (0,1)` (`R_geRat_zero_gen`).  `dSeriesCReal` is the
genuine `K_t`-side series (this module).

### THE FACTOR-`1/2` CORRECTION (a soundness fix, AGENTS.md Rule 6)

The differentiated-JTP identity of `docs/jtp-convergence-notes.md §2.1(C)` reads
`K_t(x) = ϑ₃(θ)·S(x)/(2a)`, equivalently — in the `U`-grading carried here, where
`dSeriesCReal = Σ_{n≥1} n·a^{n²}·U_{n−1}(x) = D(θ)/sin θ` — the identity
`Dseries = (sin θ/2)·ϑ₃·S`, i.e.

    `dSeriesCReal  ≈  (1/2)·(ϑ₃·S)`.                                          (DIFF)

The crucial half-factor was DROPPED in the previous round, which stated the
residual as `dSeriesCReal ≈ ϑ₃·S` (no `1/2`).  That statement is **numerically
false**: at every `a ∈ (0,1)`, `θ ∈ (0,π)`, `ϑ₃·S = 2·dSeriesCReal` exactly
(verified to 40 digits; ratio `= 2.0` at `a = 0.2,0.3,0.5,0.8`).  We CORRECT it:
the genuine residual is `(DIFF)` above, with the `(1/2)` carried by `Rhalf`.
Closing the un-halved version would have closed a FALSE equality; the named
obligation must be the true identity, so `DiffJTP` now targets `Rhalf`.

`(DIFF)` is NOT a finite identity (the two sides live in different gradings at
every truncation, §2.3 of the notes; see the sharp finding below); it is a
term-by-term differentiation of the convergent product, a double-limit
interchange `lim_h lim_L = lim_L lim_h` with explicit `O((a·a)ᵏ)` log-derivative
modulus.  We do NOT discharge it (it is the one genuinely-hard analytic engine
still required); we expose it as a named hypothesis and prove the conditional
closure `DiffJTP → K_t ≥ 0`. -/

/-- **`R = ϑ₃·S` as a `CReal`** (the bare product object), for ALL `a ∈ (0,1)`,
`−1 ≤ x ≤ 1`.  NOTE: this is `2·dSeriesCReal` in the limit, NOT `dSeriesCReal`;
the differentiated-JTP residual links `dSeriesCReal` to `Rhalf = (1/2)·Rproduct`
below, not to `Rproduct`. -/
def Rproduct {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal :=
  CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1)
    (HKConvGen.sConvCReal_general ha0 ha1 hx)

/-- Every approximation of `Rproduct` is `≥ 0` (both factors have nonneg
approximations). -/
theorem Rproduct_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (n : Nat) : (0 : Q') ≤ (Rproduct ha0 ha1 hx hx1).approx n := by
  show (0 : Q') ≤ (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1).approx n
      * (HKConvGen.sConvCReal_general ha0 ha1 hx).approx n
  exact Q'.mul_nonneg _ _
    (ThetaConvGen.thetaConvCRealGen_approx_nonneg ha0 ha1 hx hx1 n)
    (HKConvGen.sConvCReal_general_approx_nonneg ha0 ha1 hx n)

/-- **`Rhalf = (1/2)·ϑ₃·S` as a `CReal`** — the CORRECT product object the
differentiated-JTP residual links to.  `approx n = half · (ϑ₃·S).approx n`.  In
the limit `Rhalf = dSeriesCReal` (the factor-`1/2`-corrected identity `(DIFF)`). -/
def Rhalf {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal :=
  CReal.mul (CReal.ofQ' HalfPow.half) (Rproduct ha0 ha1 hx hx1)

/-- Every approximation of `Rhalf` is `≥ 0` (`half ≥ 0` and `Rproduct.approx ≥ 0`). -/
theorem Rhalf_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (n : Nat) : (0 : Q') ≤ (Rhalf ha0 ha1 hx hx1).approx n := by
  show (0 : Q') ≤ (CReal.ofQ' HalfPow.half).approx n * (Rproduct ha0 ha1 hx hx1).approx n
  exact Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Rproduct_approx_nonneg ha0 ha1 hx hx1 n)

/-- **The differentiated Jacobi-triple-product residual `(DIFF)` (named `Prop`).**
The single remaining analytic obligation of Wall 2: the `K_t`-side series
`dSeriesCReal` and the (HALVED) product object `Rhalf = (1/2)·ϑ₃·S` have the same
limit.  Equivalently `Σ_{n≥1} n a^{n²} sin nθ = (sin θ/2)·ϑ₃(θ)·S(cos θ)` — the
`(sin θ/2)` factor is the `1/2` of `Rhalf` (the `1/sin θ` is folded into the
`U`-grading of `dSeriesCReal`).  NOT discharged here — it is the term-by-term
differentiation of a convergent product (a genuine double-limit interchange), the
one analysis engine still required. -/
def DiffJTP {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Prop :=
  CReal.Equiv (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)

/-- `CReal.Equiv` is reflexive (one-slack tolerance is met with `ε`). -/
theorem Equiv_refl (A : CReal) : CReal.Equiv A A :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- **THE CONDITIONAL CLOSURE: `DiffJTP → K_t ≥ 0`.**  Given the differentiated-JTP
residual `(DIFF)` (`dSeriesCReal ≈ Rhalf`, with the corrected `1/2` factor), the
heat-kernel series `K_t = dSeriesCReal` is `≥ 0` (`ExpPos.geRat … 0`).  Routes
through `UTelescope.Kt_nonneg_of_residual` with the constant truncation family
`Rtrunc M = dSeriesCReal` (so `hTrunc` is reflexivity and `hConv` is exactly
`(DIFF)`), and `Rhalf`'s approximation nonnegativity from `Rhalf_approx_nonneg`.
The ONLY open input is `DiffJTP`. -/
theorem Kt_geRat_zero_of_diff {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (hDiff : DiffJTP ha0 ha1 hx hx1) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  UTelescope.Kt_nonneg_of_residual
    (dSeriesCReal ha0 ha1 hx hx1)
    (Rhalf ha0 ha1 hx hx1)
    (fun _ => dSeriesCReal ha0 ha1 hx hx1)
    (fun _ => Equiv_refl (dSeriesCReal ha0 ha1 hx hx1))
    (fun _ => hDiff)
    (Rhalf_approx_nonneg ha0 ha1 hx hx1)

/-! ## 5. Bridge to the finite-difference Leibniz engine (`DiffProduct.lean`)

`DiffProduct.leibniz` closes the FINITE skeleton of the differentiation — the
discrete product rule
`∏_{k<L} f k − ∏_{k<L} g k ≈ Σ_{j<L} pre f j·(f j − g j)·∏_{j<k<L} g k` — for ALL
`L`, as pure `Q'` algebra.  The residual `DiffJTP` is EXACTLY the abstract
`DiffProduct.ProductDerivativeLimit` (the double-limit interchange feeding off
that finite skeleton) specialised to the heat-kernel `K_t`-series and the product
object `R = ϑ₃·S`.  We record this identification and re-expose the conditional
closure through it, so the single open analytic obligation is the named
`ProductDerivativeLimit` whose finite core is the proven `leibniz`. -/

/-- **`DiffJTP` IS the `ProductDerivativeLimit` obligation** for the heat-kernel
series vs the (HALVED) product object `Rhalf = (1/2)·ϑ₃·S`.  Definitional
(`CReal.Equiv` on both sides), recorded to connect the named residual to the
finite-difference Leibniz engine of `DiffProduct.lean` (whose `leibniz` is the
proven finite core).  NOTE: the obligation targets `Rhalf`, not the bare
`Rproduct` — the factor-`1/2` correction (see §4). -/
theorem DiffJTP_eq_productDerivativeLimit {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    DiffJTP ha0 ha1 hx hx1
      = DiffProduct.ProductDerivativeLimit
          (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1) :=
  rfl

/-- **Conditional closure via the product-derivative obligation.**  Given the
abstract `ProductDerivativeLimit` linking the `K_t`-series and `Rhalf = (1/2)·ϑ₃·S`
(whose finite core `DiffProduct.leibniz` is proven), `K_t = dSeriesCReal ≥ 0`.
Same content as `Kt_geRat_zero_of_diff`, oriented through `DiffProduct`. -/
theorem Kt_geRat_zero_of_productDerivativeLimit {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (hPDL : DiffProduct.ProductDerivativeLimit
              (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_diff ha0 ha1 hx hx1 hPDL

/-! ## 6. Closure through the genuine C¹-uniform-limit engine (`TsumDeriv.lean`)

`DiffProduct.C1ToEquiv` is the named `Σ`-obligation that specialises the generic
Bishop C¹-limit engine `TsumDeriv.fdDeriv_of_unif` to the heat-kernel / Jacobi
factors: it carries the `C1Inputs` modulus data for the theta-product family plus
the derivative-value identification.  Given such an instance linking `dSeriesCReal`
and `Rhalf`, both `DiffJTP` and the unconditional-shaped `K_t ≥ 0` follow.  This
threads the heat-kernel positivity through the ACTUAL analysis engine — the part
that commutes `d/dθ` with the limit — rather than a black-box `Prop`.

The single remaining open input is therefore exactly `C1ToEquiv` (equivalently its
`C1Inputs` field, the `O((a·a)^k)`-modulus theta-product differentiation data); the
engine and the conditional closure are both discharged. -/

/-- **`C1ToEquiv → DiffJTP`.**  The named C¹-engine instantiation obligation (for
the heat-kernel series `dSeriesCReal` and the halved product `Rhalf`) discharges
the differentiated-JTP residual `DiffJTP`. -/
theorem DiffJTP_of_c1 {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1ToEquiv (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    DiffJTP ha0 ha1 hx hx1 :=
  DiffProduct.productDerivativeLimit_of_c1 H

/-- **THE ENGINE-ROUTED CLOSURE: `C1ToEquiv → K_t ≥ 0`.**  Given the C¹-limit-engine
instantiation data for the heat-kernel theta-product family, the heat-kernel series
`K_t = dSeriesCReal ≥ 0`.  The positivity flows through `TsumDeriv.fdDeriv_of_unif`
(the genuine "derivative of the limit = uniform limit of derivatives" theorem) via
the `C1Inputs` carried by `C1ToEquiv`; the sole open input is that instantiation
datum.  Same downstream consequence as `Kt_geRat_zero_of_diff`. -/
theorem Kt_geRat_zero_of_c1 {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1ToEquiv (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_diff ha0 ha1 hx hx1 (DiffJTP_of_c1 ha0 ha1 hx hx1 H)

/-! ### Closure through the DERIVATIVE-UNIQUENESS route (Route A)

`DiffProduct.C1UniqInputs` packages the Route-A instantiation: two finite-difference
derivatives (series side + product side) of the SAME limit function `F = ϑ₃`, plus a
realisation map.  The genuine `TsumDeriv.fdDeriv_unique` engine collapses the two
derivative values to a `Q'`-equality, and the realisation lifts it to the `CReal`
bridge.  This routes `K_t ≥ 0` through the actual uniqueness theorem rather than a
raw differentiated-identity assumption, relocating the residual to the
UNdifferentiated Jacobi identity (`ϑ₃^{ser} = ϑ₃^{prod}`, common `F`) + realisation. -/

/-- **`C1UniqInputs → DiffJTP`** (the uniqueness-routed residual closure). -/
theorem DiffJTP_of_uniq {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputs (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    DiffJTP ha0 ha1 hx hx1 :=
  DiffProduct.productDerivativeLimit_of_uniq H

/-- **THE UNIQUENESS-ROUTED CLOSURE: `C1UniqInputs → K_t ≥ 0`.**  Given the Route-A
instantiation data (two common-`F` finite-difference derivatives + realisation), the
heat-kernel series `K_t = dSeriesCReal ≥ 0`.  Positivity flows through the genuine
`TsumDeriv.fdDeriv_unique` (CoRN `Derivative_I_unique` analogue), not a black-box
`Prop`. -/
theorem Kt_geRat_zero_of_uniq {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputs (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_diff ha0 ha1 hx hx1 (DiffJTP_of_uniq ha0 ha1 hx hx1 H)

/-! ### Closure through the CReal-LEVEL uniqueness route (Route B)

`DiffProduct.C1UniqInputsCReal` discharges the `Q'→CReal` realisation gap of Route
A through the genuine constructive-real cancellation
(`CReal.Equiv_of_abs_sub_le_all_pos`, the CoRN infinitesimal lemma): rather than a
hand-supplied `dser ≈ dprod → CReal.Equiv …` lift, it consumes the checkable
infinitesimal-difference bound on the two `CReal` realisations.  Both the
`Q'`-uniqueness engine (`fdDeriv_unique`) and the `CReal`-cancellation engine are
fully discharged; the sole open input is the infinitesimal-difference bound (the
matched-truncation + undifferentiated-Jacobi content). -/

/-- **`C1UniqInputsCReal → DiffJTP`** (the CReal-uniqueness-routed residual closure). -/
theorem DiffJTP_of_uniq_creal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputsCReal (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    DiffJTP ha0 ha1 hx hx1 :=
  DiffProduct.productDerivativeLimit_of_uniq_creal H

/-- **THE CReal-UNIQUENESS-ROUTED CLOSURE: `C1UniqInputsCReal → K_t ≥ 0`.**
Positivity flows through BOTH the genuine `TsumDeriv.fdDeriv_unique` (value
equality) and the genuine `CReal.Equiv_of_abs_sub_le_all_pos` (the infinitesimal
cancellation lifting it to the `CReal` bridge); the sole open input is the
infinitesimal-difference bound. -/
theorem Kt_geRat_zero_of_uniq_creal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputsCReal (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_diff ha0 ha1 hx hx1 (DiffJTP_of_uniq_creal ha0 ha1 hx hx1 H)

/-! ### Closure through the CReal-VALUED derivative-uniqueness route (Route A,
unconditional layer)

`DiffProduct.C1UniqInputsCRealDeriv` is the sharpest form of the residual: the
series side `dSeriesCReal` and the product side `Rhalf` are each exhibited as a
`CReal`-VALUED finite-difference derivative (`TsumDeriv.FDDerivDataC`) of the SAME
`CReal`-valued limit `F = ϑ₃` at `θ`.  The `CReal.Equiv` is then produced ENTIRELY by
the genuine `TsumDeriv.fdDeriv_uniqueC` engine — NO rational→real realisation lift
(Route A's `realise`) and NO infinitesimal-difference bound (Route B's
`infinitesimal`).  The whole remaining input is two common-`F` `CReal`
finite-difference derivatives. -/

/-- **`C1UniqInputsCRealDeriv → DiffJTP`** (the CReal-derivative-uniqueness closure). -/
theorem DiffJTP_of_uniq_creal_deriv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputsCRealDeriv
            (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    DiffJTP ha0 ha1 hx hx1 :=
  DiffProduct.productDerivativeLimit_of_uniq_creal_deriv H

/-- **THE CReal-DERIVATIVE-UNIQUENESS-ROUTED CLOSURE: `C1UniqInputsCRealDeriv →
K_t ≥ 0`.**  Positivity flows through the genuine `CReal`-valued uniqueness engine
`TsumDeriv.fdDeriv_uniqueC` alone (no realisation lift, no infinitesimal bound); the
sole open input is the two common-`F` `CReal` finite-difference derivatives (series
side + product side of the one limit `ϑ₃`). -/
theorem Kt_geRat_zero_of_uniq_creal_deriv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : DiffProduct.C1UniqInputsCRealDeriv
            (dSeriesCReal ha0 ha1 hx hx1) (Rhalf ha0 ha1 hx hx1)) :
    ExpPos.geRat (dSeriesCReal ha0 ha1 hx hx1) 0 :=
  Kt_geRat_zero_of_diff ha0 ha1 hx hx1 (DiffJTP_of_uniq_creal_deriv ha0 ha1 hx hx1 H)

end YMGap.Continuum.JTPIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`finSum`/`decide`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`.  `DiffJTP` is a
named hypothesis (the single open analytic obligation), NOT a `sorry`. -/

#print axioms YMGap.Continuum.JTPIdentity.nsq_aa_pow_le
#print axioms YMGap.Continuum.JTPIdentity.gauss_le_geo
#print axioms YMGap.Continuum.JTPIdentity.dTermMaj_le
#print axioms YMGap.Continuum.JTPIdentity.dTerm_le
#print axioms YMGap.Continuum.JTPIdentity.neg_dTerm_le
#print axioms YMGap.Continuum.JTPIdentity.dSeriesCReal
#print axioms YMGap.Continuum.JTPIdentity.Rproduct_approx_nonneg
#print axioms YMGap.Continuum.JTPIdentity.Rhalf_approx_nonneg
#print axioms YMGap.Continuum.JTPIdentity.Equiv_refl
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_diff
#print axioms YMGap.Continuum.JTPIdentity.DiffJTP_eq_productDerivativeLimit
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_productDerivativeLimit
#print axioms YMGap.Continuum.JTPIdentity.DiffJTP_of_c1
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_c1
#print axioms YMGap.Continuum.JTPIdentity.DiffJTP_of_uniq
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_uniq
#print axioms YMGap.Continuum.JTPIdentity.DiffJTP_of_uniq_creal
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_uniq_creal
#print axioms YMGap.Continuum.JTPIdentity.DiffJTP_of_uniq_creal_deriv
#print axioms YMGap.Continuum.JTPIdentity.Kt_geRat_zero_of_uniq_creal_deriv
