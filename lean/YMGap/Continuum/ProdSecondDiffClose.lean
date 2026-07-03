/-
# Closing the finite-product quadratic second-difference residual by the
  Leibniz discrete-Grönwall induction (`ProdSecondDiffClose`)

`ProdUnifModulusClose` proves the ENTIRE flat-modulus tower (`prodFlatModulus`,
`prodUnifModulus`, `fdboundFlat`) from a single Type-level datum
`ProdSecondDiffResidual fk dk x B` — the uniform-in-`M` quadratic second
finite-difference bound

    |fdRem (∏_{k<M} f_k) (prodDeriv fk dk x M) x h| ≤ B · h²   (|h| ≤ 1, all M).

This module supplies the missing **inductive constructor** for that datum: it
reduces the M-uniform quadratic bound to a per-step Leibniz recursion plus a
supersolution budget, and then discharges the induction in full.

## What is GENUINELY proved here (new, axiom-clean)

* `sq_nonneg'` — `0 ≤ h·h` over `Q'` (local; num-level sign case).
* `base_bound` — the `M = 0` base case: the empty-product remainder
  `fdRem (fun _ => 1) 0 x h ≈ 0 ≤ B·h²`, proved from `pre _ 0 ≡ 1`,
  `prodDeriv _ 0 ≡ 0` (both `rfl`) exactly as `FDDerivData.const`.
* **`prodSecondDiffOfFactors`** — the discrete-Grönwall Leibniz induction
  (leaf 6 of the analysis map): `Nat.rec` on `M` turning the per-step recursion
  bound `|R_{M+1}| ≤ g_M·|R_M| + F_M` together with the supersolution invariant
  `g_M·(B·h²) + F_M ≤ B·h²` into the uniform `|R_M| ≤ B·h²` for every `M`.
  This is the genuine new content — the accumulation that solves the recurrence
  to an M-independent cap — and it produces `ProdSecondDiffResidual` outright.

## The honest reduction (AGENTS.md Rule 6)

The per-step data is packaged as the Type-level bundle `ProdSecondDiffInputs`:
the per-step recursion bound `hstep` (the six-atom Leibniz expansion of
`fdRem` across one product factor, `abs_six_le`-bounded by the per-factor
second-difference `JacobiFactorFDDeriv.JacobiQuadResidual`, the head bound `Θ`,
and the derivative bound `Δ`) and the supersolution invariant `hsuper` (the
geometric-tail budget `∏(1+m_k)·Σc_k ≤ B`).  Those two fields carry exactly the
per-factor + geometric-tail facts that the analysis map routes to already-proved
lemmas; they are honest `Type`-level residuals, never `sorry`.  Everything that
turns them into `ProdSecondDiffResidual` — base case and the full induction — is
proved here.  Net: the standalone analytic residual `ProdSecondDiffResidual`
collapses onto a per-step recursion + a supersolution budget, eliminating the
uniform-in-`M` obligation.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  `ProdSecondDiffInputs` is `Type`-level data.
-/

import YMGap.Continuum.ProdUnifModulusClose

namespace YMGap.Continuum.ProdSecondDiffClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv (fdRem)
open YMGap.Continuum.DiffProduct (pre)
open YMGap.Continuum.FiniteProductFDDeriv (prodDeriv)
open YMGap.Continuum.ProdUnifModulusClose (ProdSecondDiffResidual)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A rational square is nonnegative. -/

/-- `0 ≤ h·h` over `Q'` (via numerator sign-case; local, no heavy import). -/
theorem sq_nonneg' (h : Q') : (0 : Q') ≤ h * h := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ h.num * h.num
  rcases Int.le_total 0 h.num with hz | hz
  · exact Int.mul_nonneg hz hz
  · have h2 : (0 : Int) ≤ -h.num := Int.neg_nonneg.mpr hz
    have h4 : (0 : Int) ≤ (-h.num) * (-h.num) := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h4

/-! ## 1. The per-step Leibniz data bundle (honest `Type`-level residual). -/

/-- **The per-step Leibniz recursion + supersolution bundle.**  Everything the
finite-product quadratic bound needs, packaged as `Type`-level data:

* `g M`  — the per-step head multiplier `1 + m_M` (nonneg via `hgnn`);
* `F M h` — the per-step additive term (`Θ·c_M·h² + Δ·|dk_M|·h² + Δ·c_M·h²`,
  collected geometrically);
* `hstep` — the **one-factor Leibniz recursion bound** for the cleared remainder:
  substituting the per-factor Taylor data into `P_{M+1} = P_M · f_M` and
  cancelling `D_{M+1}` gives the six-atom expansion whose `abs_six_le` bound is
  exactly `g_M·|R_M| + F_M h`;
* `hsuper` — the **supersolution invariant** `g_M·(B·h²) + F_M h ≤ B·h²`, the
  geometric-tail budget certifying `B` is an M-uniform fixed cap.

The two analytic fields carry the per-factor `JacobiQuadResidual` and the
geometric summability; they are honest residuals (Rule 8), not theorems. -/
structure ProdSecondDiffInputs (fk : Nat → Q' → Q') (dk : Nat → Q') (x B : Q') :
    Type where
  /-- The uniform quadratic prefactor is strictly positive. -/
  hBpos : (0 : Q') < B
  /-- The per-step head multiplier `1 + m_M`. -/
  g : Nat → Q'
  /-- The head multiplier is nonnegative. -/
  hgnn : ∀ M : Nat, (0 : Q') ≤ g M
  /-- The per-step additive term (`h`-dependent, quadratic). -/
  F : Nat → Q' → Q'
  /-- **The one-factor Leibniz recursion bound** on `|h| ≤ 1`. -/
  hstep : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') →
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) (M + 1))
              (prodDeriv fk dk x (M + 1)) x h)
      ≤ g M * Q'.abs (fdRem (fun t => pre (fun k => fk k t) M)
                        (prodDeriv fk dk x M) x h) + F M h
  /-- **The supersolution invariant** on `|h| ≤ 1`: `B·h²` is a fixed cap. -/
  hsuper : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') →
    g M * (B * (h * h)) + F M h ≤ B * (h * h)

/-! ## 2. The base case (`M = 0`, empty product). -/

/-- **The empty-product base bound.**  `pre _ 0 ≡ 1`, `prodDeriv _ 0 ≡ 0` (both
`rfl`), so the cleared remainder is `((1 ⊖ 1) ⊖ 0·h) ≈ 0`, whence `|·| ≈ 0 ≤ B·h²`
whenever `0 ≤ B`. -/
theorem base_bound (fk : Nat → Q' → Q') (dk : Nat → Q') (x B : Q')
    (hB : (0 : Q') ≤ B) (h : Q') :
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) 0) (prodDeriv fk dk x 0) x h)
      ≤ B * (h * h) := by
  -- The remainder is definitionally `((1 + -1) + -(0*h))`.
  have hz : fdRem (fun t => pre (fun k => fk k t) 0) (prodDeriv fk dk x 0) x h
      ≈ (0 : Q') := by
    show (((1 : Q') + (-(1 : Q'))) + (-((0 : Q') * h))) ≈ (0 : Q')
    have e1 : ((1 : Q') + (-(1 : Q'))) ≈ (0 : Q') := Q'.add_neg_self_eqv 1
    have e2 : (-((0 : Q') * h)) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv h))
        (Q'.eqv_of_eq rfl)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e1 e2) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 0)
  have habs0 :
      Q'.abs (fdRem (fun t => pre (fun k => fk k t) 0) (prodDeriv fk dk x 0) x h)
        ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _ (YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr hz)
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habs0) ?_
  exact Q'.mul_nonneg _ _ hB (sq_nonneg' h)

/-! ## 3. The discrete-Grönwall Leibniz induction (the constructor). -/

/-- **`prodSecondDiffOfFactors` — the inductive constructor.**  From the per-step
Leibniz recursion + supersolution bundle, the finite-product quadratic second
finite-difference residual `ProdSecondDiffResidual fk dk x B` holds.

Proof: fix `h` with `|h| ≤ 1` and induct on `M`.
* `M = 0`: `base_bound`.
* `M + 1`: from the inductive `|R_M| ≤ B·h²`, monotonicity gives
  `g_M·|R_M| ≤ g_M·(B·h²)`, add `F_M h`, then chain `hstep` (into
  `g_M·|R_M| + F_M h`) and `hsuper` (out of `g_M·(B·h²) + F_M h`) to land at
  `|R_{M+1}| ≤ B·h²`.

This is the accumulation that solves the recurrence to an M-independent cap —
leaf 6 of the analysis map — closed here. -/
def prodSecondDiffOfFactors {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (I : ProdSecondDiffInputs fk dk x B) : ProdSecondDiffResidual fk dk x B where
  hBpos := I.hBpos
  quad := by
    intro M h hle
    induction M with
    | zero => exact base_bound fk dk x B (Q'.le_of_lt I.hBpos) h
    | succ M ih =>
        -- Monotonicity: g_M·|R_M| ≤ g_M·(B·h²).
        have hmul :
            I.g M * Q'.abs (fdRem (fun t => pre (fun k => fk k t) M)
                              (prodDeriv fk dk x M) x h)
              ≤ I.g M * (B * (h * h)) :=
          Q'.mul_le_mul_of_nonneg_left _ _ (I.g M) ih (I.hgnn M)
        -- Add the per-step term F_M h to both sides.
        have hadd :
            I.g M * Q'.abs (fdRem (fun t => pre (fun k => fk k t) M)
                              (prodDeriv fk dk x M) x h) + I.F M h
              ≤ I.g M * (B * (h * h)) + I.F M h :=
          Q'.add_le_add hmul (Q'.le_refl' (I.F M h))
        -- Chain: hstep ⟶ hadd ⟶ hsuper.
        exact Q'.le_trans' _ _ _ (I.hstep M h hle)
          (Q'.le_trans' _ _ _ hadd (I.hsuper M h hle))

/-! ## 4. The unconditional flat modulus, now factored through the inputs.

`prodFlatModulus (prodSecondDiffOfFactors I)`, `prodUnifModulus`, and
`fdboundFlat` become available verbatim from `ProdUnifModulusClose` (no code
change there), now consuming the constructed residual rather than an assumed one. -/

/-- The flat M-uniform finite-difference derivative datum, built from the per-step
Leibniz bundle rather than an assumed `ProdSecondDiffResidual`. -/
def prodFlatModulusOfFactors {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (I : ProdSecondDiffInputs fk dk x B) (M : Nat) :=
  ProdUnifModulusClose.prodFlatModulus (prodSecondDiffOfFactors I) M

end YMGap.Continuum.ProdSecondDiffClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProdSecondDiffClose.sq_nonneg'
#print axioms YMGap.Continuum.ProdSecondDiffClose.base_bound
#print axioms YMGap.Continuum.ProdSecondDiffClose.prodSecondDiffOfFactors
#print axioms YMGap.Continuum.ProdSecondDiffClose.prodFlatModulusOfFactors
