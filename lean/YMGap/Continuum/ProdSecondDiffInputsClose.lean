/-
# Inhabiting the finite-product second-difference residual via a RUNNING cap
  (`ProdSecondDiffInputsClose`)

`ProdSecondDiffClose.ProdSecondDiffInputs` packages the per-step Leibniz recursion
`hstep` together with a **flat** supersolution invariant

    hsuper :  g_M · (B · h²) + F_M h  ≤  B · h²        (one fixed `B`, every `M`).

For the theta / Jacobi product the head multiplier is
`g_M = |fk M x| + |dk M|` with `fk M x = 1 + amp·(2x + amp) ≥ 1` on `x ≥ 0`
(half the Chebyshev domain), so `g_M ≥ 1` and the flat invariant demands
`c_M ≤ (1 − g_M)·B < 0 ≤ c_M`, which is **unsatisfiable for every `B` and every
such `M`**.  The flat-`B` supersolution field is a genuine wall, not bookkeeping.

## The restructure this module provides

We replace the flat supersolution by a **monotone running cap** `B_M` obeying the
honest step invariant

    g_M · (B_M · h²) + F_M h  ≤  B_{M+1} · h²,

and prove the discrete-Grönwall induction against it, producing the SAME datum
`ProdUnifModulusClose.ProdSecondDiffResidual fk dk x B` (a single global `B`), so
everything downstream (`prodFlatModulus`, `prodUnifModulus`, `fdboundFlat`) is
untouched.  Concretely we take the closed-form running cap

    runningCap g c 0     = 0
    runningCap g c (M+1) = g_M · runningCap g c M + c_M          (c_M ≥ F_M h / h²)

whose step invariant is PROVED here (`runningCap_capstep`) — no sign constraint on
`g_M`, so unlike `hsuper` it is satisfiable.

## What is GENUINELY proved here (new, axiom-clean)

* `runningCap` / `runningCap_capstep` — the running-cap step invariant, proved
  from `g_M ≥ 0`, `F_M h ≤ c_M·h²` and `0 ≤ h²` (no upper bound on `g_M`).
* `prodSecondDiffOfRunning` — the discrete-Grönwall induction against the running
  cap, producing `ProdSecondDiffResidual fk dk x B` from the running-cap bundle.
* `hstep_of_vanishing` — the per-factor Leibniz recursion bound `hstep` itself,
  DISCHARGED from the single hypothesis that the factor's own finite-difference
  remainder vanishes (`fdRem (fk M) (dk M) x h ≈ 0`), via `mul_rem_expand` +
  `abs_six_le`.  For the Jacobi factors this hypothesis is
  `DkProducerClose.jacFdRem_vanishes`.

## The two honest residual fields (AGENTS.md Rule 6/8)

`ProdSecondDiffRunningInputs` carries exactly two `Type`-level residuals:
`hstep` (dischargeable by `hstep_of_vanishing`) and `hBrun_le` (the global-cap
finiteness `runningCap g c M ≤ B`, i.e. the geometric-`q²` summability already
built in `JTPInstance`).  Everything turning them into `ProdSecondDiffResidual`
is proved here.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.ProdSecondDiffClose
import YMGap.Continuum.MulCombinatorClose

namespace YMGap.Continuum.ProdSecondDiffInputsClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv (fdRem)
open YMGap.Continuum.DiffProduct (pre)
open YMGap.Continuum.FiniteProductFDDeriv (prodDeriv abs_six_le)
open YMGap.Continuum.ProdUnifModulusClose (ProdSecondDiffResidual)
open YMGap.Continuum.ProdSecondDiffClose (base_bound sq_nonneg')
open YMGap.Continuum.MulCombinatorClose (mul_rem_expand)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The running cap and its step invariant. -/

/-- **The monotone running cap.**  `B_0 = 0`, `B_{M+1} = g_M·B_M + c_M`.  With
`c_M ≥ 0` and `g_M ≥ 0` this is nondecreasing; its finiteness as `M → ∞` is the
geometric-`q²` summability (an honest residual), but each `B_M` is a concrete
rational and the step invariant below holds with NO upper bound on `g_M`. -/
def runningCap (g c : Nat → Q') : Nat → Q'
  | 0     => 0
  | M + 1 => g M * runningCap g c M + c M

@[simp] theorem runningCap_zero (g c : Nat → Q') : runningCap g c 0 = 0 := rfl

@[simp] theorem runningCap_succ (g c : Nat → Q') (M : Nat) :
    runningCap g c (M + 1) = g M * runningCap g c M + c M := rfl

/-- **The running-cap step invariant** (the satisfiable replacement for `hsuper`).
From `g_M ≥ 0`, `F_M h ≤ c_M·h²` and `0 ≤ h²`,

    g_M · (B_M · h²) + F_M h  ≤  B_{M+1} · h².

Crucially this needs NO upper bound on `g_M` (the flat invariant `hsuper` failed
precisely because it did).  Proof: reassociate `g_M·(B_M·h²) = (g_M·B_M)·h²`,
bound `F_M h ≤ c_M·h²`, then refactor `(g_M·B_M)·h² + c_M·h² = (g_M·B_M+c_M)·h²`. -/
theorem runningCap_capstep (g c : Nat → Q')
    (F : Nat → Q' → Q')
    (hFc : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') → F M h ≤ c M * (h * h))
    (M : Nat) (h : Q') (hh : Q'.abs h ≤ (1 : Q')) :
    g M * (runningCap g c M * (h * h)) + F M h
      ≤ runningCap g c (M + 1) * (h * h) := by
  have e1 : g M * (runningCap g c M * (h * h))
      ≤ (g M * runningCap g c M) * (h * h) :=
    Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (g M) (runningCap g c M) (h * h)))
  have e3 : g M * (runningCap g c M * (h * h)) + F M h
      ≤ (g M * runningCap g c M) * (h * h) + c M * (h * h) :=
    Q'.add_le_add e1 (hFc M h hh)
  have e4 : (g M * runningCap g c M) * (h * h) + c M * (h * h)
      ≈ (g M * runningCap g c M + c M) * (h * h) :=
    Q'.eqv_symm (Q'.add_mul_eqv (g M * runningCap g c M) (c M) (h * h))
  exact Q'.le_trans' _ _ _ e3 (Q'.le_of_eqv e4)

/-! ## 2. The per-step Leibniz recursion + running-cap bundle. -/

/-- **The running-cap per-step bundle.**  Same per-step data as
`ProdSecondDiffClose.ProdSecondDiffInputs`, but with the flat supersolution
`hsuper` (unsatisfiable, `g_M ≥ 1`) replaced by:

* `c` / `hcnn` / `hFc` — the per-step additive coefficient `c_M ≥ 0` with
  `F_M h ≤ c_M·h²` (the running-cap increment);
* `hBrun_le` — the **global-cap finiteness** `runningCap g c M ≤ B` (the honest
  geometric-`q²` summability residual).

`hstep` is the one-factor Leibniz recursion bound (dischargeable by
`hstep_of_vanishing`). -/
structure ProdSecondDiffRunningInputs
    (fk : Nat → Q' → Q') (dk : Nat → Q') (x B : Q') : Type where
  /-- The global quadratic prefactor is strictly positive. -/
  hBpos : (0 : Q') < B
  /-- The per-step head multiplier `g_M = |fk M x| + |dk M|`. -/
  g : Nat → Q'
  /-- The head multiplier is nonnegative. -/
  hgnn : ∀ M : Nat, (0 : Q') ≤ g M
  /-- The per-step additive coefficient. -/
  c : Nat → Q'
  /-- The additive coefficient is nonnegative. -/
  hcnn : ∀ M : Nat, (0 : Q') ≤ c M
  /-- The per-step additive term (`h`-dependent, quadratic). -/
  F : Nat → Q' → Q'
  /-- The additive term is dominated by `c_M·h²`. -/
  hFc : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') → F M h ≤ c M * (h * h)
  /-- **The one-factor Leibniz recursion bound** on `|h| ≤ 1`. -/
  hstep : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') →
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) (M + 1))
              (prodDeriv fk dk x (M + 1)) x h)
      ≤ g M * Q'.abs (fdRem (fun t => pre (fun k => fk k t) M)
                        (prodDeriv fk dk x M) x h) + F M h
  /-- **The global-cap finiteness residual** (geometric summability). -/
  hBrun_le : ∀ M : Nat, runningCap g c M ≤ B

/-! ## 3. The discrete-Grönwall induction against the running cap. -/

/-- **`prodSecondDiffOfRunning` — the running-cap constructor.**  From the
running-cap bundle, the finite-product quadratic second finite-difference residual
`ProdSecondDiffResidual fk dk x B` holds (single global `B`, as consumed by
`prodFlatModulus`).

Proof: fix `h` with `|h| ≤ 1`.  First `key : |R_N| ≤ B_N·h²` by induction on `N`
(`base_bound` at `N=0` since `B_0 = 0 ≥ 0`; at `N+1` chain `hstep`, monotonicity,
and `runningCap_capstep`).  Then `B_M·h² ≤ B·h²` by `hBrun_le` and `0 ≤ h²`. -/
def prodSecondDiffOfRunning {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (I : ProdSecondDiffRunningInputs fk dk x B) :
    ProdSecondDiffResidual fk dk x B where
  hBpos := I.hBpos
  quad := by
    intro M h hle
    have key : ∀ N : Nat,
        Q'.abs (fdRem (fun t => pre (fun k => fk k t) N)
                  (prodDeriv fk dk x N) x h)
          ≤ runningCap I.g I.c N * (h * h) := by
      intro N
      induction N with
      | zero => exact base_bound fk dk x (runningCap I.g I.c 0) (Q'.le_refl' 0) h
      | succ N ih =>
          have hmul :
              I.g N * Q'.abs (fdRem (fun t => pre (fun k => fk k t) N)
                                (prodDeriv fk dk x N) x h)
                ≤ I.g N * (runningCap I.g I.c N * (h * h)) :=
            Q'.mul_le_mul_of_nonneg_left _ _ (I.g N) ih (I.hgnn N)
          have hadd :
              I.g N * Q'.abs (fdRem (fun t => pre (fun k => fk k t) N)
                                (prodDeriv fk dk x N) x h) + I.F N h
                ≤ I.g N * (runningCap I.g I.c N * (h * h)) + I.F N h :=
            Q'.add_le_add hmul (Q'.le_refl' (I.F N h))
          have hcap :
              I.g N * (runningCap I.g I.c N * (h * h)) + I.F N h
                ≤ runningCap I.g I.c (N + 1) * (h * h) :=
            runningCap_capstep I.g I.c I.F I.hFc N h hle
          exact Q'.le_trans' _ _ _ (I.hstep N h hle)
            (Q'.le_trans' _ _ _ hadd hcap)
    refine Q'.le_trans' _ _ _ (key M) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ (h * h) (I.hBrun_le M) (sq_nonneg' h)

/-! ## 4. Discharging the `hstep` field from per-factor vanishing. -/

/-- **`hstep_of_vanishing` — the one-factor Leibniz recursion bound.**  When the
adjoined factor's own finite-difference remainder vanishes
(`fdRem (fk M) (dk M) x h ≈ 0` — for the Jacobi factors this is
`DkProducerClose.jacFdRem_vanishes`, the factor being affine in `x`), the cleared
product remainder at `M+1` obeys

    |R_{M+1}| ≤ (|fk M x| + |dk M|)·|R_M| + |prodDeriv_M · dk M|·h²,

i.e. exactly the `hstep` field with `g_M = |fk M x| + |dk M|` and
`F_M h = |prodDeriv_M · dk M|·h²` (so `c_M = |prodDeriv_M · dk M|`, `F_M h = c_M·h²`).

Proof: `mul_rem_expand` splits `R_{M+1}` into the six Leibniz atoms; the three atoms
carrying the vanishing factor remainder `rg = fdRem (fk M) (dk M) x h` collapse to
`0`; `abs_six_le` bounds the survivors `b0·rf`, `dg·(h·rf)`, `(df·dg)·h²`; folding
`|fk M x|·|R_M| + |dk M|·|R_M| = (|fk M x|+|dk M|)·|R_M|` gives the claim. -/
theorem hstep_of_vanishing (fk : Nat → Q' → Q') (dk : Nat → Q') (x : Q')
    (M : Nat) (h : Q') (hh1 : Q'.abs h ≤ (1 : Q'))
    (hrg : fdRem (fun t => fk M t) (dk M) x h ≈ (0 : Q')) :
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) (M + 1))
              (prodDeriv fk dk x (M + 1)) x h)
      ≤ (Q'.abs (fk M x) + Q'.abs (dk M))
          * Q'.abs (fdRem (fun t => pre (fun k => fk k t) M)
                      (prodDeriv fk dk x M) x h)
        + Q'.abs (prodDeriv fk dk x M * dk M) * (h * h) := by
  -- `Rf = R_M`, `Rg = fdRem (fk M) (dk M) x h` (definitionally the Leibniz atoms).
  let Rf : Q' := fdRem (fun t => pre (fun k => fk k t) M) (prodDeriv fk dk x M) x h
  let Rg : Q' := fdRem (fun t => fk M t) (dk M) x h
  have hRg0 : Rg ≈ (0 : Q') := hrg
  -- The six per-atom bounds.
  have b1 : Q'.abs ((fk M x) * Rf) ≤ Q'.abs (fk M x) * Q'.abs Rf :=
    TsumDeriv.Q'.abs_mul_le (fk M x) Rf
  have b2 : Q'.abs ((pre (fun k => fk k x) M) * Rg) ≤ (0 : Q') := by
    have hz : (pre (fun k => fk k x) M) * Rg ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (pre (fun k => fk k x) M) _ (0 : Q') hRg0)
        (Q'.mul_zero_eqv (pre (fun k => fk k x) M))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (TsumDeriv.Q'.abs_eqv_congr hz)
      (TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0)))
  have b3 : Q'.abs (Rf * Rg) ≤ (0 : Q') := by
    have hz : Rf * Rg ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left Rf _ (0 : Q') hRg0) (Q'.mul_zero_eqv Rf)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (TsumDeriv.Q'.abs_eqv_congr hz)
      (TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0)))
  have b4 : Q'.abs (prodDeriv fk dk x M * (h * Rg)) ≤ (0 : Q') := by
    have hzr : h * Rg ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left h _ (0 : Q') hRg0) (Q'.mul_zero_eqv h)
    have hz : prodDeriv fk dk x M * (h * Rg) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (prodDeriv fk dk x M) _ (0 : Q') hzr)
        (Q'.mul_zero_eqv (prodDeriv fk dk x M))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (TsumDeriv.Q'.abs_eqv_congr hz)
      (TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0)))
  have b5 : Q'.abs (dk M * (h * Rf)) ≤ Q'.abs (dk M) * Q'.abs Rf := by
    have hhrf : Q'.abs (h * Rf) ≤ Q'.abs Rf := by
      refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le h Rf) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs Rf) hh1 (Q'.abs_nonneg Rf)) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs Rf))
    refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le (dk M) (h * Rf)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs (dk M)) hhrf (Q'.abs_nonneg (dk M))
  have b6 : Q'.abs ((prodDeriv fk dk x M * dk M) * (h * h))
      ≤ Q'.abs (prodDeriv fk dk x M * dk M) * (h * h) := by
    refine Q'.le_trans' _ _ _
      (TsumDeriv.Q'.abs_mul_le (prodDeriv fk dk x M * dk M) (h * h)) ?_
    exact Q'.le_of_eqv (Q'.mul_eqv_congr_left
      (Q'.abs (prodDeriv fk dk x M * dk M)) _ _
      (TsumDeriv.Q'.abs_of_nonneg (sq_nonneg' h)))
  -- The six-atom Leibniz split, then the triangle bound.
  have hsplit := mul_rem_expand (pre (fun k => fk k (x + h)) M) (fk M (x + h))
    (pre (fun k => fk k x) M) (fk M x) (prodDeriv fk dk x M) (dk M) h
  have hsix := abs_six_le hsplit b1 b2 b3 b4 b5 b6
  -- Collapse the three zeros and fold the two `·|Rf|` atoms.
  have eAll :
      (((((Q'.abs (fk M x) * Q'.abs Rf + (0 : Q')) + 0) + 0)
          + Q'.abs (dk M) * Q'.abs Rf)
          + Q'.abs (prodDeriv fk dk x M * dk M) * (h * h))
        = (((Q'.abs (fk M x) * Q'.abs Rf) + Q'.abs (dk M) * Q'.abs Rf)
            + Q'.abs (prodDeriv fk dk x M * dk M) * (h * h)) := by
    rw [Q'.add_zero', Q'.add_zero', Q'.add_zero']
  have hfold :
      (((((Q'.abs (fk M x) * Q'.abs Rf + (0 : Q')) + 0) + 0)
          + Q'.abs (dk M) * Q'.abs Rf)
          + Q'.abs (prodDeriv fk dk x M * dk M) * (h * h))
        ≈ ((Q'.abs (fk M x) + Q'.abs (dk M)) * Q'.abs Rf
            + Q'.abs (prodDeriv fk dk x M * dk M) * (h * h)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq eAll)
      (Q'.add_eqv_congr_right _ _
        (Q'.abs (prodDeriv fk dk x M * dk M) * (h * h))
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.abs (fk M x)) (Q'.abs (dk M)) (Q'.abs Rf))))
  exact Q'.le_trans' _ _ _ hsix (Q'.le_of_eqv hfold)

end YMGap.Continuum.ProdSecondDiffInputsClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProdSecondDiffInputsClose.runningCap_capstep
#print axioms YMGap.Continuum.ProdSecondDiffInputsClose.prodSecondDiffOfRunning
#print axioms YMGap.Continuum.ProdSecondDiffInputsClose.hstep_of_vanishing
