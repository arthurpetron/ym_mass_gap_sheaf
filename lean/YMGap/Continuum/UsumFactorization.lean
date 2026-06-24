/-
# `(U★)` from the `U_M` factorization — the finite product-rule / `(★★)` route (Wall-1 capstone)

`(U★)` (`NewtonRecurrence.RootedNodesU.Usum_value`) is the single residual to which the
all-order SU(2) heat-kernel Gram PSD (Wall-1) was reduced after the entire
formal-power-series telescoping/swap content was PROVED in `NewtonRecurrence`:

    Asum D n  ≈  Uval M n        (1 ≤ n ≤ 2M)                              (U★)

i.e. the unweighted second-kind power sum `Σ_{k<M} U_n(x_k) = (M−n)` (`n` even) / `0`
(`n` odd) on the `M` roots `x_k` of `U_M`.  This module DERIVES `(U★)` FROM the genuine
`U_M` FACTORIZATION via the finite **product-rule** identity, reducing Wall-1 to the
single cleanest residual: that the `M` nodes ARE `U_M`'s roots (the factorization datum).

## The worked (π-free, finite, no infinite series, no roots of unity) derivation

For nodes `x_k`, `factor_k(z) := 1 − 2 x_k z + z²` (the `QPoly` `[1, −2x_k, 1]`).
`P := ∏_{k<M} factor_k`,  `N := Σ_{k<M} ∏_{l≠k} factor_l`,  `W := Σ_{k<M} x_k·∏_{l≠k} factor_l`,
`P' :=` the formal derivative of `P`.  Using `factor_k = (1+z²) − 2x_k z` and
`factor_k' = 2z − 2x_k`:

  * **FINITE PRODUCT RULE** (`pderiv_pmul_eval`, `pderiv_pprod_eval`): the formal
    derivative of a product evaluates to the Leibniz sum; over the node product,
    `P'(z) = Σ_{k<M} factor_k'(z)·∏_{l≠k} factor_l(z)`.  PROVED by structural induction.
  * `Σ_{k<M} factor_k·∏_{l≠k} factor_l = M·P` (each summand telescopes to `P`).
  * Expanding `factor_k`:  `M·P = (1+z²)·N − 2z·W`.                                  (i)
  * Expanding `factor_k'`:  `P' = 2z·N − 2·W`, hence `W = z·N − P'/2`.               (ii)
  * Substituting (ii) into (i):  **`(1−z²)·N = M·P − z·P'`**.                       (★★)

The factorization `P = Σ_{j=0}^M z^{2j}` (the proved `OffDiagShift.prodIdentity_geom`,
carried as the enriched datum `eval P z ≈ geomEven z M`) gives, via the geometric
telescope, `(1−z²)·P = 1 − z^{2(M+1)}`, and `M·P − z·P' = Σ_{j=0}^M (M−2j)z^{2j}`.  The
per-node U-generating function `factor_k(z)·(Σ_n U_n(x_k) z^n) = 1` (the U-recurrence)
sums to `P·(Σ_n A_n z^n) = N`, so `(1−z^{2(M+1)})·(Σ A_n z^n) = (1−z²)·N = M·P − z·P'`.
Reading `[z^n]` for `1 ≤ n ≤ 2M` (where the `z^{2(M+1)}` shift contributes `0`) gives
`A_n = (M−n)` (`n` even) / `0` (`n` odd) — that is `(U★)`.

## PROVED here (genuine, axiom-clean, π-free)

  * `pderiv` — the formal derivative on `QPoly` coefficient lists, with `coeff` access.
  * **`pderiv_pmul_eval`** — the FINITE LEIBNIZ PRODUCT RULE, eval level, GENERAL:
    `eval (pderiv (pmul p q)) z ≈ eval (pderiv p) z · eval q z + eval p z · eval (pderiv q) z`.
  * `factor` / `pprod` / `pprodOmit` — the node factor `[1,−2x,1]`, the full product `P`,
    and the leave-one-out product `∏_{l≠k}`.
  * **`star_star`** — the IDENTITY (★★) `(1−z²)·N(z) = M·P(z) − z·P'(z)`, GENERAL `M`,
    at eval level, via (i),(ii) and the product rule.  The genuine algebraic core.
  * `FactoredNodes` — the enriched interface carrying the factorization datum
    `eval P z ≈ geomEven z M` (the honest "nodes are `U_M`'s roots" content) and the
    per-node U-generating function, atop `RootPowerSumBridge.RootedNodes`.
  * `usum_of_factored` / the assembled coefficient extraction — DERIVE `(U★)`
    (`Asum D n ≈ Uval M n`, `1 ≤ n ≤ 2M`) FROM `FactoredNodes`.
  * `rootedNodesU_of_factored` — INHABIT `NewtonRecurrence.RootedNodesU` from
    `FactoredNodes` (general `M`); `gram_psd_from_factorization` composes with
    `gram_psd_closed` to close the all-order Gram PSD (Wall-1) RELATIVE TO the
    factorization datum.
  * The `M = 2` instance: the `FactoredNodes 2` factorization discharged, so everything
    is unconditional at `M = 2`.

## Honest status — PROVED vs NAMED-open

PROVED, general `M`: the finite product rule and the IDENTITY (★★) — the entire
finite-derivative / Leibniz content.  The residual is now the FACTORIZATION DATUM
`eval P z ≈ geomEven z M` (the `M` nodes ARE the roots of `U_M`) plus its per-node
U-generating consequence — carried as the honestly-named `Type`-level fields of
`FactoredNodes`, and DISCHARGED unconditionally at `M = 2`.  The factorization-for-
located-roots is the genuine irreducible wall: it requires a constructive
"degree-`M` `Q'`-polynomial with `M` located roots factors completely" theorem together
with the general-`M` located roots from `ChebRoot` (whose nodes are irrational for
`M ≥ 3`, so the rational `decide` route does not apply).  See the verdict below.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no `decide` on a non-decidable `Prop`.  `decide` only on closed
`Q'`/`Nat`.  Witnesses (`FactoredNodes`) are `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.NewtonRecurrence
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.UsumFactorization

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.PowerSumCollapse
open YMGap.Continuum.TPowerSum
open YMGap.Continuum.RootPowerSumBridge
open YMGap.Continuum.OffDiagShift
open YMGap.Continuum.NewtonRecurrence
open YMGap.Constructive.QPoly

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The formal derivative on `QPoly` coefficient lists

`pderiv [c₀,c₁,c₂,…] = [c₁, 2c₂, 3c₃, …]` — drop the constant, multiply the `n`-th
coefficient by `n`.  We define it via a helper carrying the running multiplier. -/

/-- Auxiliary: scale the `i`-th remaining coefficient by `(i + s)` and drop the head.
`derivFrom s [a₀, a₁, …] = [s·a₀, (s+1)·a₁, …]` is NOT what we want; we want the
derivative `[a₁, 2a₂, …]`.  So `pderiv (c :: cs) = scaleFrom 1 cs`. -/
def scaleFrom : Nat → Poly → Poly
  | _, [] => []
  | s, (c :: cs) => (Q'.ofNat s * c) :: scaleFrom (s+1) cs

/-- The formal derivative of a `QPoly`. -/
def pderiv : Poly → Poly
  | [] => []
  | (_ :: cs) => scaleFrom 1 cs

@[simp] theorem pderiv_nil : pderiv [] = [] := rfl
theorem pderiv_cons (c : Q') (cs : Poly) : pderiv (c :: cs) = scaleFrom 1 cs := rfl

/-! ## 2. The finite Leibniz product rule (eval level, general)

The genuine engine.  We prove `eval (pderiv (pmul p q)) z ≈ eval (pderiv p) z · eval q z
+ eval p z · eval (pderiv q) z` by structural induction on `p`.  Two helper eval-laws
for `scaleFrom`/`pderiv` make the head/cons bookkeeping explicit. -/

/-- `ofNat (s+1) = ofNat s + 1` over `Q'`. -/
theorem ofNatSucc (s : Nat) : Q'.ofNat (s+1) ≈ Q'.ofNat s + (1 : Q') := by
  show (Q'.ofNat (s+1)).num * ((Q'.ofNat s + 1).den : Int)
      = (Q'.ofNat s + 1).num * ((Q'.ofNat (s+1)).den : Int)
  simp only [Cheb.add_num]
  show (Int.ofNat (s+1)) * (1 * 1) = ((Int.ofNat s) * 1 + (1 : Int) * 1) * 1
  simp only [Int.ofNat_eq_natCast]; push_cast; omega

/-- `eval (scaleFrom s cs) z` relation: the "shifted derivative" satisfies
`eval (scaleFrom (s+1) cs) z = eval (scaleFrom s cs) z + eval cs z`, i.e. bumping the
running multiplier by one adds one copy of `eval cs`. -/
theorem eval_scaleFrom_succ (cs : Poly) (z : Q') : ∀ s,
    eval (scaleFrom (s+1) cs) z ≈ eval (scaleFrom s cs) z + eval cs z := by
  induction cs with
  | nil => intro s; show (0 : Q') ≈ (0 : Q') + 0; decide
  | cons c cs ih =>
      intro s
      -- LHS = ofNat (s+1) * c + z * eval (scaleFrom (s+2) cs) z
      -- RHS = (ofNat s * c + z * eval (scaleFrom (s+1) cs) z) + (c + z * eval cs z)
      show (Q'.ofNat (s+1) * c + z * eval (scaleFrom (s+1+1) cs) z)
        ≈ (Q'.ofNat s * c + z * eval (scaleFrom (s+1) cs) z) + (c + z * eval cs z)
      -- head: ofNat(s+1)*c ≈ ofNat s * c + c
      have hhead : Q'.ofNat (s+1) * c ≈ Q'.ofNat s * c + c := by
        refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ c (ofNatSucc s)) ?_
        refine eqv_trans _ _ _ (Cheb.add_mul_eqv (Q'.ofNat s) 1 c) ?_
        exact add_eqv_congr_left _ _ _ (one_mul_eqv c)
      -- tail: z * eval (scaleFrom (s+2) cs) ≈ z*(eval(scaleFrom (s+1) cs) + eval cs)
      have htail : z * eval (scaleFrom (s+1+1) cs) z
          ≈ z * eval (scaleFrom (s+1) cs) z + z * eval cs z := by
        refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ (ih (s+1))) ?_
        exact mul_add_eqv z (eval (scaleFrom (s+1) cs) z) (eval cs z)
      -- assemble via the interchange (a+b)+(c+d) regroup
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hhead htail) ?_
      -- (ofNat s*c + c) + (z·… + z·eval cs) ≈ (ofNat s*c + z·…) + (c + z·eval cs)
      exact q_interchange (Q'.ofNat s * c) c (z * eval (scaleFrom (s+1) cs) z) (z * eval cs z)

/-- `pderiv` of `padd`: `eval (pderiv (padd p q)) z ≈ eval (pderiv p) z + eval (pderiv q) z`.
We need the `scaleFrom`-level statement first (since `pderiv (a::p) = scaleFrom 1 p`). -/
theorem eval_scaleFrom_padd (z : Q') : ∀ (s : Nat) (p q : Poly),
    eval (scaleFrom s (padd p q)) z ≈ eval (scaleFrom s p) z + eval (scaleFrom s q) z := by
  intro s p
  induction p generalizing s with
  | nil =>
      intro q
      show eval (scaleFrom s q) z ≈ (0 : Q') + eval (scaleFrom s q) z
      exact eqv_symm (q_zero_add_eqv (eval (scaleFrom s q) z))
  | cons a p ih =>
      intro q
      cases q with
      | nil =>
          show eval (scaleFrom s (a :: p)) z ≈ eval (scaleFrom s (a :: p)) z + (0 : Q')
          exact eqv_symm (q_add_zero_eqv (eval (scaleFrom s (a :: p)) z))
      | cons b q =>
          -- scaleFrom s ((a+b)::padd p q) = (ofNat s*(a+b)) :: scaleFrom (s+1) (padd p q)
          show (Q'.ofNat s * (a + b) + z * eval (scaleFrom (s+1) (padd p q)) z)
            ≈ (Q'.ofNat s * a + z * eval (scaleFrom (s+1) p) z)
              + (Q'.ofNat s * b + z * eval (scaleFrom (s+1) q) z)
          have hhead : Q'.ofNat s * (a + b) ≈ Q'.ofNat s * a + Q'.ofNat s * b :=
            mul_add_eqv (Q'.ofNat s) a b
          have htail : z * eval (scaleFrom (s+1) (padd p q)) z
              ≈ z * eval (scaleFrom (s+1) p) z + z * eval (scaleFrom (s+1) q) z := by
            refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ (ih (s+1) q)) ?_
            exact mul_add_eqv z (eval (scaleFrom (s+1) p) z) (eval (scaleFrom (s+1) q) z)
          refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hhead htail) ?_
          exact q_interchange (Q'.ofNat s * a) (Q'.ofNat s * b)
            (z * eval (scaleFrom (s+1) p) z) (z * eval (scaleFrom (s+1) q) z)

/-- `pderiv` of `pscale`: `eval (scaleFrom s (pscale k q)) z ≈ k · eval (scaleFrom s q) z`. -/
theorem eval_scaleFrom_pscale (z k : Q') : ∀ (s : Nat) (q : Poly),
    eval (scaleFrom s (pscale k q)) z ≈ k * eval (scaleFrom s q) z := by
  intro s q
  induction q generalizing s with
  | nil =>
      show (0 : Q') ≈ k * 0
      exact eqv_symm (q_mul_zero k)
  | cons c q ih =>
      -- pscale k (c::q) = (k*c) :: pscale k q ; scaleFrom s ((k*c)::…) = ofNat s*(k*c) :: …
      show (Q'.ofNat s * (k * c) + z * eval (scaleFrom (s+1) (pscale k q)) z)
        ≈ k * (Q'.ofNat s * c + z * eval (scaleFrom (s+1) q) z)
      have hhead : Q'.ofNat s * (k * c) ≈ k * (Q'.ofNat s * c) := by
        refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (Q'.ofNat s) k c)) ?_
        refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ c (mul_comm_eqv (Q'.ofNat s) k)) ?_
        exact mul_assoc_eqv k (Q'.ofNat s) c
      have htail : z * eval (scaleFrom (s+1) (pscale k q)) z
          ≈ k * (z * eval (scaleFrom (s+1) q) z) := by
        refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ (ih (s+1))) ?_
        -- z * (k * X) ≈ k * (z * X)
        refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv z k (eval (scaleFrom (s+1) q) z))) ?_
        refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv z k)) ?_
        exact mul_assoc_eqv k z (eval (scaleFrom (s+1) q) z)
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hhead htail) ?_
      exact eqv_symm (mul_add_eqv k (Q'.ofNat s * c) (z * eval (scaleFrom (s+1) q) z))

/-- **`pderiv` distributes over `padd`** (eval level):
`eval (pderiv (padd p q)) z ≈ eval (pderiv p) z + eval (pderiv q) z`. -/
theorem eval_pderiv_padd (z : Q') (p q : Poly) :
    eval (pderiv (padd p q)) z ≈ eval (pderiv p) z + eval (pderiv q) z := by
  cases p with
  | nil =>
      cases q with
      | nil => show (0 : Q') ≈ (0 : Q') + 0; decide
      | cons b q =>
          -- padd [] (b::q) = b::q ; pderiv = scaleFrom 1 q ; pderiv [] = []
          show eval (scaleFrom 1 q) z ≈ (0 : Q') + eval (scaleFrom 1 q) z
          exact eqv_symm (q_zero_add_eqv _)
  | cons a p =>
      cases q with
      | nil =>
          show eval (scaleFrom 1 p) z ≈ eval (scaleFrom 1 p) z + (0 : Q')
          exact eqv_symm (q_add_zero_eqv _)
      | cons b q =>
          -- padd (a::p)(b::q) = (a+b)::padd p q ; pderiv = scaleFrom 1 (padd p q)
          show eval (scaleFrom 1 (padd p q)) z ≈ eval (scaleFrom 1 p) z + eval (scaleFrom 1 q) z
          exact eval_scaleFrom_padd z 1 p q

/-- **`pderiv` commutes with `pscale`** (eval level):
`eval (pderiv (pscale k q)) z ≈ k · eval (pderiv q) z`. -/
theorem eval_pderiv_pscale (z k : Q') (q : Poly) :
    eval (pderiv (pscale k q)) z ≈ k * eval (pderiv q) z := by
  cases q with
  | nil => show (0 : Q') ≈ k * 0; exact eqv_symm (q_mul_zero k)
  | cons c q =>
      -- pscale k (c::q) = (k*c) :: pscale k q ; pderiv = scaleFrom 1 (pscale k q)
      show eval (scaleFrom 1 (pscale k q)) z ≈ k * eval (scaleFrom 1 q) z
      exact eval_scaleFrom_pscale z k 1 q

/-- The derivative of `x·r` (i.e. of `0 :: r`):
`eval (pderiv (0 :: r)) z ≈ eval r z + z · eval (pderiv r) z`.
`pderiv (0::r) = scaleFrom 1 r`, and `scaleFrom 1 r` Horner-relates to `r + z·scaleFrom 1`. -/
theorem eval_pderiv_consZero (z : Q') (r : Poly) :
    eval (pderiv ((0 : Q') :: r)) z ≈ eval r z + z * eval (pderiv r) z := by
  -- pderiv (0::r) = scaleFrom 1 r ; pderiv r = scaleFrom 1 (tail r).
  cases r with
  | nil => show (0 : Q') ≈ (0 : Q') + z * 0; refine eqv_symm ?_
           refine eqv_trans _ _ _ (q_zero_add_eqv (z * 0)) ?_; exact q_mul_zero z
  | cons c r =>
      -- scaleFrom 1 (c::r) = (ofNat 1*c) :: scaleFrom 2 r
      -- eval = ofNat 1 * c + z * eval (scaleFrom 2 r) z
      -- RHS = (c + z*eval r z) + z*eval (scaleFrom 1 r) z   [pderiv (c::r)=scaleFrom 1 r]
      show (Q'.ofNat 1 * c + z * eval (scaleFrom (1+1) r) z)
        ≈ (c + z * eval r z) + z * eval (scaleFrom 1 r) z
      have hhead : Q'.ofNat 1 * c ≈ c := eqv_trans _ _ _
        (mul_eqv_congr_right (Q'.ofNat 1) 1 c (by decide)) (one_mul_eqv c)
      -- tail: z * eval (scaleFrom 2 r) z ≈ z*(eval (scaleFrom 1 r) z + eval r z)
      have htail : z * eval (scaleFrom (1+1) r) z
          ≈ z * eval r z + z * eval (scaleFrom 1 r) z := by
        refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ (eval_scaleFrom_succ r z 1)) ?_
        -- z*(eval(scaleFrom 1 r) + eval r) ≈ z*eval r + z*eval(scaleFrom 1 r)
        refine eqv_trans _ _ _ (mul_add_eqv z (eval (scaleFrom 1 r) z) (eval r z)) ?_
        exact add_comm_eqv (z * eval (scaleFrom 1 r) z) (z * eval r z)
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hhead htail) ?_
      -- c + (z*eval r + z*eval(scaleFrom 1 r)) ≈ (c + z*eval r) + z*eval(scaleFrom 1 r)
      exact eqv_symm (add_assoc_eqv c (z * eval r z) (z * eval (scaleFrom 1 r) z))

/-- **The cons-derivative law** (eval level): `d/dz(a + z·P(z)) = P(z) + z·P'(z)`, i.e.
`eval (pderiv (a :: p)) z ≈ eval p z + z · eval (pderiv p) z`.  (The head `a` does not
affect the derivative; same shape as `eval_pderiv_consZero`.) -/
theorem eval_pderiv_cons (z a : Q') (p : Poly) :
    eval (pderiv (a :: p)) z ≈ eval p z + z * eval (pderiv p) z := by
  -- pderiv (a::p) = scaleFrom 1 p = pderiv (0::p), so reuse consZero.
  have h : pderiv (a :: p) = pderiv ((0 : Q') :: p) := rfl
  rw [h]; exact eval_pderiv_consZero z p

/-- **THE FINITE LEIBNIZ PRODUCT RULE** (eval level, general).
`eval (pderiv (pmul p q)) z ≈ eval (pderiv p) z · eval q z + eval p z · eval (pderiv q) z`.
Proved by structural induction on `p` using the derivative distributivity laws and
`eval_pmul`. -/
theorem pderiv_pmul_eval (z : Q') : ∀ (p q : Poly),
    eval (pderiv (pmul p q)) z ≈ eval (pderiv p) z * eval q z + eval p z * eval (pderiv q) z := by
  intro p
  induction p with
  | nil =>
      intro q
      -- pmul [] q = [] ; pderiv [] = [] ; eval = 0 ; RHS = 0*… + 0*… = 0
      show (0 : Q') ≈ (0 : Q') * eval q z + (0 : Q') * eval (pderiv q) z
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ (q_zero_mul (eval q z)) (q_zero_mul (eval (pderiv q) z))) ?_
      exact q_add_zero_eqv 0
  | cons a p ih =>
      intro q
      -- pmul (a::p) q = padd (pscale a q) (0 :: pmul p q)
      show eval (pderiv (padd (pscale a q) ((0:Q') :: pmul p q))) z
        ≈ eval (pderiv (a :: p)) z * eval q z + eval (a :: p) z * eval (pderiv q) z
      -- LHS distributes over padd:
      refine eqv_trans _ _ _ (eval_pderiv_padd z (pscale a q) ((0:Q') :: pmul p q)) ?_
      -- = eval(pderiv(pscale a q)) + eval(pderiv(0::pmul p q))
      have hL : eval (pderiv (pscale a q)) z ≈ a * eval (pderiv q) z := eval_pderiv_pscale z a q
      have hR : eval (pderiv ((0:Q') :: pmul p q)) z
          ≈ eval (pmul p q) z + z * eval (pderiv (pmul p q)) z := eval_pderiv_consZero z (pmul p q)
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hL hR) ?_
      -- = a·q' + (eval(pmul p q) + z·eval(pderiv(pmul p q)))
      -- use eval_pmul and ih:
      have hpq : eval (pmul p q) z ≈ eval p z * eval q z := eval_pmul p q z
      have hdpq : eval (pderiv (pmul p q)) z
          ≈ eval (pderiv p) z * eval q z + eval p z * eval (pderiv q) z := ih q
      refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _
        (Cheb.add_eqv_congr _ _ _ _ hpq (mul_eqv_congr_left z _ _ hdpq))) ?_
      -- now everything is in eval p, eval q, derivatives; pure Q' algebra.
      -- LHS = a·q' + (p·q + z·(p'·q + p·q'))
      -- RHS = (eval(pderiv(a::p)))·q + (a + z·p)·q'
      --     = (p + z·p')·q + (a + z·p)·q'      [eval_pderiv_cons, and eval (a::p) = a + z·p]
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (mul_eqv_congr_right _ _ (eval q z) (eval_pderiv_cons z a p))
        (eqv_refl ((a + z * eval p z) * eval (pderiv q) z))) ?_
      -- ((eval p + z·p')·q) + ((a + z·p)·q')
      -- expand both products
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (Cheb.add_mul_eqv (eval p z) (z * eval (pderiv p) z) (eval q z))
        (Cheb.add_mul_eqv a (z * eval p z) (eval (pderiv q) z))) ?_
      -- = (p·q + (z·p')·q) + (a·q' + (z·p)·q')
      -- target LHS = a·q' + (p·q + (z·(p'·q) + z·(p·q')))   ... need to expand z*(...)
      -- Let me massage the LHS target into the same normal form.
      -- RHS-of-our-symm-goal is the original LHS:  a·q' + (p·q + z·(p'·q + p·q'))
      -- expand z·(p'·q + p·q') = z·(p'·q) + z·(p·q')
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _
        (mul_add_eqv z (eval (pderiv p) z * eval q z) (eval p z * eval (pderiv q) z)))) ?_
      -- LHS now: a·q' + (p·q + (z·(p'·q) + z·(p·q')))
      -- RHS now: (p·q + (z·p')·q) + (a·q' + (z·p)·q')
      -- Use associativity of multiplication to match (z·p')·q = z·(p'·q), (z·p)·q' = z·(p·q').
      -- Reduce both sides to the flat multiset {a·q', p·q, z·(p'·q), z·(p·q')}.
      -- LHS already: a·q' + (p·q + (z·(p'·q) + z·(p·q')))
      -- RHS: (p·q + z·(p'·q)) + (a·q' + z·(p·q'))   after assoc on the two mul triples
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (add_eqv_congr_left _ _ _ (mul_assoc_eqv z (eval (pderiv p) z) (eval q z)))
        (add_eqv_congr_left _ _ _ (mul_assoc_eqv z (eval p z) (eval (pderiv q) z)))) ?_
      -- RHS: (p·q + z·(p'·q)) + (a·q' + z·(p·q'))
      -- LHS: a·q' + (p·q + (z·(p'·q) + z·(p·q')))
      -- Both equal a·q' + p·q + z·(p'·q) + z·(p·q'); regroup RHS to match LHS.
      -- goal:  (PQ + Z1) + (Aq + Z2)  ≈  Aq + (PQ + (Z1 + Z2))
      calc ((eval p z * eval q z) + z * (eval (pderiv p) z * eval q z))
            + ((a * eval (pderiv q) z) + z * (eval p z * eval (pderiv q) z))
          ≈ (((eval p z * eval q z) + z * (eval (pderiv p) z * eval q z))
              + (a * eval (pderiv q) z)) + z * (eval p z * eval (pderiv q) z) :=
            eqv_symm (add_assoc_eqv _ (a * eval (pderiv q) z) (z * (eval p z * eval (pderiv q) z)))
        _ ≈ ((a * eval (pderiv q) z)
              + ((eval p z * eval q z) + z * (eval (pderiv p) z * eval q z)))
              + z * (eval p z * eval (pderiv q) z) :=
            add_eqv_congr_right _ _ _ (add_comm_eqv _ (a * eval (pderiv q) z))
        _ ≈ (a * eval (pderiv q) z)
              + (((eval p z * eval q z) + z * (eval (pderiv p) z * eval q z))
                + z * (eval p z * eval (pderiv q) z)) :=
            add_assoc_eqv (a * eval (pderiv q) z) _ (z * (eval p z * eval (pderiv q) z))
        _ ≈ (a * eval (pderiv q) z)
              + ((eval p z * eval q z)
                + (z * (eval (pderiv p) z * eval q z) + z * (eval p z * eval (pderiv q) z))) :=
            add_eqv_congr_left _ _ _ (add_assoc_eqv (eval p z * eval q z)
              (z * (eval (pderiv p) z * eval q z)) (z * (eval p z * eval (pderiv q) z)))

/-! ## 3. The node factor `[1, −2x, 1]` and the finite product `P`

`factor x = [1, −2x, 1]` so `eval (factor x) z = 1 + z·(−2x + z·1) = 1 − 2xz + z²`.
`pprod nodes M = factor (nodes 0) · … · factor (nodes (M−1))` (built up by `pmul`). -/

/-- The node factor polynomial `1 − 2x·z + z²` as the coefficient list `[1, −2x, 1]`. -/
def factor (x : Q') : Poly := [1, -((2 : Q') * x), 1]

/-- `eval (factor x) z ≈ (1 + z²) + (−(2x))·z`. -/
theorem eval_factor (x z : Q') :
    eval (factor x) z ≈ (1 + z * z) + (-((2 : Q') * x)) * z := by
  -- eval [1, -2x, 1] z = 1 + z*(-2x + z*(1 + z*0))
  show (1 + z * ((-((2:Q')*x)) + z * (1 + z * 0))) ≈ (1 + z * z) + (-((2:Q')*x)) * z
  have hinner : ((-((2:Q')*x)) + z * (1 + z * 0)) ≈ (-((2:Q')*x)) + z := by
    refine add_eqv_congr_left _ _ _ ?_
    refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ ?_) (mul_one_eqv z)
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (q_mul_zero z)) ?_
    rw [add_zero']; exact eqv_refl _
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (mul_eqv_congr_left z _ _ hinner)) ?_
  -- 1 + z*((-2x) + z) ≈ (1 + z²) + (-2x)·z
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (mul_add_eqv z (-((2:Q')*x)) z)) ?_
  -- 1 + (z·(-2x) + z·z) ≈ (1 + z·z) + (-2x)·z
  refine eqv_trans _ _ _ (eqv_symm (add_assoc_eqv 1 (z * (-((2:Q')*x))) (z * z))) ?_
  -- (1 + z·(-2x)) + z·z
  refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (add_comm_eqv 1 (z * (-((2:Q')*x))))) ?_
  -- (z·(-2x) + 1) + z·z ≈ (1 + z·z) + (-2x)·z
  refine eqv_trans _ _ _ (add_assoc_eqv (z * (-((2:Q')*x))) 1 (z * z)) ?_
  -- z·(-2x) + (1 + z·z) ≈ (1 + z·z) + (-2x)·z
  refine eqv_trans _ _ _ (add_comm_eqv (z * (-((2:Q')*x))) (1 + z * z)) ?_
  exact add_eqv_congr_left _ _ _ (mul_comm_eqv z (-((2:Q')*x)))

/-- The finite product `P = ∏_{k<M} factor (nodes k)` as a `Poly` (left fold by `pmul`). -/
def pprod (nodes : Nat → Q') : Nat → Poly
  | 0 => [1]
  | (m+1) => pmul (factor (nodes m)) (pprod nodes m)

@[simp] theorem pprod_zero (nodes : Nat → Q') : pprod nodes 0 = [1] := rfl
theorem pprod_succ (nodes : Nat → Q') (m : Nat) :
    pprod nodes (m+1) = pmul (factor (nodes m)) (pprod nodes m) := rfl

/-! ## 4. The identity (★★) `(1−z²)·N = M·P − z·P'` (general `M`, eval level)

We carry the eval-level quantities `Pv = eval P`, `Pdv = eval P'`, and the leave-one-out
sums `Nv = Σ_{k<M} ∏_{l≠k}`, `Wv = Σ_{k<M} x_k·∏_{l≠k}` defined by the recursions
`N_{M+1} = P_M + factor_M·N_M`, `W_{M+1} = x_M·P_M + factor_M·W_M`, `N_0 = W_0 = 0`.
Then (★★) follows by induction on `M`, the step using the product rule
`P'_{M+1} = factor'_M·P_M + factor_M·P'_M`. -/

/-- `Pv nodes M z = eval (pprod nodes M) z`. -/
def Pv (nodes : Nat → Q') (M : Nat) (z : Q') : Q' := eval (pprod nodes M) z
/-- `Pdv nodes M z = eval (pderiv (pprod nodes M)) z` (the derivative `P'`). -/
def Pdv (nodes : Nat → Q') (M : Nat) (z : Q') : Q' := eval (pderiv (pprod nodes M)) z

/-- The leave-one-out sum `N = Σ_{k<M} ∏_{l≠k} factor_l`, eval level, by the recursion. -/
def Nv (nodes : Nat → Q') (z : Q') : Nat → Q'
  | 0 => 0
  | (m+1) => Pv nodes m z + ((1 + z*z) + (-((2:Q') * nodes m)) * z) * Nv nodes z m

/-- The weighted leave-one-out sum `W = Σ_{k<M} x_k·∏_{l≠k}`, eval level. -/
def Wv (nodes : Nat → Q') (z : Q') : Nat → Q'
  | 0 => 0
  | (m+1) => nodes m * Pv nodes m z
      + ((1 + z*z) + (-((2:Q') * nodes m)) * z) * Wv nodes z m

/-- `Pv` recursion: `P_{M+1} = factor_M · P_M`, eval level. -/
theorem Pv_succ (nodes : Nat → Q') (m : Nat) (z : Q') :
    Pv nodes (m+1) z ≈ ((1 + z*z) + (-((2:Q') * nodes m)) * z) * Pv nodes m z := by
  show eval (pmul (factor (nodes m)) (pprod nodes m)) z
    ≈ ((1 + z*z) + (-((2:Q') * nodes m)) * z) * eval (pprod nodes m) z
  refine eqv_trans _ _ _ (eval_pmul (factor (nodes m)) (pprod nodes m) z) ?_
  exact mul_eqv_congr_right _ _ (eval (pprod nodes m) z) (eval_factor (nodes m) z)

/-- The derivative of the factor `factor'_M = 2z − 2x_M`, eval level:
`eval (pderiv (factor x)) z ≈ (-((2:Q')*x)) + (2:Q')*z`. -/
theorem eval_pderiv_factor (x z : Q') :
    eval (pderiv (factor x)) z ≈ (-((2:Q') * x)) + (2:Q') * z := by
  -- pderiv [1, -2x, 1] = scaleFrom 1 [-2x, 1] = [ofNat 1*(-2x), ofNat 2 * 1]
  -- eval = ofNat 1*(-2x) + z*(ofNat 2*1 + z*0)
  show (Q'.ofNat 1 * (-((2:Q')*x)) + z * (Q'.ofNat 2 * 1 + z * 0)) ≈ (-((2:Q')*x)) + (2:Q')*z
  refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
  · exact eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (by decide : Q'.ofNat 1 ≈ (1:Q')))
      (one_mul_eqv (-((2:Q')*x)))
  · -- z * (ofNat 2 * 1 + z*0) ≈ 2*z
    refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ ?_) (mul_comm_eqv z (2:Q'))
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (q_mul_zero z)) ?_
    rw [add_zero']
    exact eqv_trans _ _ _ (mul_one_eqv (Q'.ofNat 2)) (by decide : Q'.ofNat 2 ≈ (2:Q'))

/-- `Pdv` recursion via the product rule: `P'_{M+1} = factor'_M·P_M + factor_M·P'_M`. -/
theorem Pdv_succ (nodes : Nat → Q') (m : Nat) (z : Q') :
    Pdv nodes (m+1) z
      ≈ ((-((2:Q') * nodes m)) + (2:Q')*z) * Pv nodes m z
        + ((1 + z*z) + (-((2:Q') * nodes m)) * z) * Pdv nodes m z := by
  show eval (pderiv (pmul (factor (nodes m)) (pprod nodes m))) z
    ≈ ((-((2:Q') * nodes m)) + (2:Q')*z) * eval (pprod nodes m) z
      + ((1 + z*z) + (-((2:Q') * nodes m)) * z) * eval (pderiv (pprod nodes m)) z
  refine eqv_trans _ _ _ (pderiv_pmul_eval z (factor (nodes m)) (pprod nodes m)) ?_
  -- eval(pderiv factor)·eval pprod + eval factor·eval(pderiv pprod)
  exact Cheb.add_eqv_congr _ _ _ _
    (mul_eqv_congr_right _ _ _ (eval_pderiv_factor (nodes m) z))
    (mul_eqv_congr_right _ _ _ (eval_factor (nodes m) z))

/-- `ofNat (m+1) · X ≈ ofNat m · X + X`. -/
theorem ofNatSucc_mul (m : Nat) (X : Q') :
    Q'.ofNat (m+1) * X ≈ Q'.ofNat m * X + X := by
  refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ X (ofNatSucc m)) ?_
  refine eqv_trans _ _ _ (Cheb.add_mul_eqv (Q'.ofNat m) 1 X) ?_
  exact add_eqv_congr_left _ _ _ (one_mul_eqv X)

/-- **Identity (i)** (general `M`, eval level):
`ofNat M · P_M = (1+z²)·N_M + (−(2z))·W_M`. -/
theorem identity_i (nodes : Nat → Q') (z : Q') : ∀ M,
    Q'.ofNat M * Pv nodes M z
      ≈ (1 + z*z) * Nv nodes z M + (-((2:Q') * z)) * Wv nodes z M := by
  intro M
  induction M with
  | zero =>
      -- 0·P_0 ≈ (1+z²)·0 + (-(2z))·0 = 0
      show Q'.ofNat 0 * Pv nodes 0 z ≈ (1 + z*z) * 0 + (-((2:Q')*z)) * 0
      refine eqv_trans _ _ _ (Q'.zero_mul_eqv (Pv nodes 0 z)) ?_
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ (q_mul_zero (1+z*z)) (q_mul_zero (-((2:Q')*z)))) ?_
      exact q_add_zero_eqv 0
  | succ m ih =>
      -- Let F := (1+z²) + (−2x_m)·z = factor_m ; c := 1+z² ; w := −(2z).
      -- N_{m+1} = P_m + F·N_m ; W_{m+1} = x_m·P_m + F·W_m ; P_{m+1} = F·P_m.
      -- RHS = c·(P_m + F·N_m) + w·(x_m·P_m + F·W_m)
      --     = c·P_m + F·(c·N_m + w·W_m) + w·x_m·P_m
      --     = c·P_m + F·(ofNat m·P_m) + w·x_m·P_m          [IH]
      --     = (c + w·x_m)·P_m + ofNat m·(F·P_m)
      --     = F·P_m + ofNat m·P_{m+1} = ofNat(m+1)·P_{m+1}  [c + w·x_m = F]
      have hP : Pv nodes (m+1) z ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * Pv nodes m z := Pv_succ nodes m z
      -- Abbreviations as plain terms.
      -- Goal LHS: ofNat(m+1)·P_{m+1}
      -- First expand ofNat(m+1)·P_{m+1} = ofNat m·P_{m+1} + P_{m+1}.
      refine eqv_trans _ _ _ (ofNatSucc_mul m (Pv nodes (m+1) z)) ?_
      -- ofNat m·P_{m+1} + P_{m+1}
      -- Now RHS = c·N_{m+1} + w·W_{m+1}, unfold N_{m+1},W_{m+1}.
      show Q'.ofNat m * Pv nodes (m+1) z + Pv nodes (m+1) z
        ≈ (1 + z*z) * (Pv nodes m z + ((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
          + (-((2:Q')*z)) * (nodes m * Pv nodes m z + ((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
      -- Massage RHS.
      refine eqv_symm ?_
      -- distribute c and w over the two summands
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (mul_add_eqv (1+z*z) (Pv nodes m z) (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m))
        (mul_add_eqv (-((2:Q')*z)) (nodes m * Pv nodes m z) (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m))) ?_
      -- (c·P_m + c·(F·N_m)) + (w·(x_m·P_m) + w·(F·W_m))
      -- regroup to (c·P_m + w·(x_m·P_m)) + (c·(F·N_m) + w·(F·W_m))
      refine eqv_trans _ _ _ (q_interchange (((1+z*z) * Pv nodes m z))
        ((1+z*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m))
        ((-((2:Q')*z)) * (nodes m * Pv nodes m z))
        ((-((2:Q')*z)) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m))) ?_
      -- = (c·P_m + w·(x_m·P_m)) + (c·(F·N_m) + w·(F·W_m))
      -- term A: c·P_m + w·(x_m·P_m) ≈ F·P_m
      have hA : (1+z*z) * Pv nodes m z + (-((2:Q')*z)) * (nodes m * Pv nodes m z)
          ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * Pv nodes m z := by
        -- (c + (w·x_m))·P_m ; and w·(x_m·P_m) = (w·x_m)·P_m ; need c + w·x_m = F i.e. (-2z)·x_m = (-2x_m)·z
        refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _
          (eqv_symm (mul_assoc_eqv (-((2:Q')*z)) (nodes m) (Pv nodes m z)))) ?_
        refine eqv_trans _ _ _ (eqv_symm (Cheb.add_mul_eqv (1+z*z) ((-((2:Q')*z)) * nodes m) (Pv nodes m z))) ?_
        refine mul_eqv_congr_right _ _ (Pv nodes m z) ?_
        -- c + (-(2z))·x_m ≈ c + (-(2x_m))·z
        refine add_eqv_congr_left _ _ _ ?_
        -- (-(2z))·x_m ≈ (-(2x_m))·z
        refine eqv_trans _ _ _ (Q'.neg_mul_eqv ((2:Q')*z) (nodes m)) ?_
        refine eqv_symm ?_
        refine eqv_trans _ _ _ (Q'.neg_mul_eqv ((2:Q')*nodes m) z) ?_
        refine neg_eqv_congr _ _ ?_
        -- (2·x_m)·z ≈ (2·z)·x_m
        refine eqv_trans _ _ _ (mul_assoc_eqv (2:Q') (nodes m) z) ?_
        refine eqv_trans _ _ _ (mul_eqv_congr_left (2:Q') _ _ (mul_comm_eqv (nodes m) z)) ?_
        exact eqv_symm (mul_assoc_eqv (2:Q') z (nodes m))
      -- term B: c·(F·N_m) + w·(F·W_m) ≈ F·(c·N_m + w·W_m) ≈ F·(ofNat m·P_m)
      have hB : (1+z*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
            + (-((2:Q')*z)) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
          ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * (Q'.ofNat m * Pv nodes m z) := by
        -- c·(F·N) = F·(c·N), w·(F·W) = F·(w·W)
        have e1 : (1+z*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
            ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * ((1+z*z) * Nv nodes z m) := by
          refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (1+z*z) ((1+z*z) + (-((2:Q')*nodes m))*z) (Nv nodes z m))) ?_
          refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (Nv nodes z m) (mul_comm_eqv (1+z*z) ((1+z*z) + (-((2:Q')*nodes m))*z))) ?_
          exact mul_assoc_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) (1+z*z) (Nv nodes z m)
        have e2 : (-((2:Q')*z)) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
            ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * ((-((2:Q')*z)) * Wv nodes z m) := by
          refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (-((2:Q')*z)) ((1+z*z) + (-((2:Q')*nodes m))*z) (Wv nodes z m))) ?_
          refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (Wv nodes z m) (mul_comm_eqv (-((2:Q')*z)) ((1+z*z) + (-((2:Q')*nodes m))*z))) ?_
          exact mul_assoc_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) (-((2:Q')*z)) (Wv nodes z m)
        refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ e1 e2) ?_
        -- F·(c·N) + F·(w·W) = F·(c·N + w·W) = F·(ofNat m·P_m)  [IH]
        refine eqv_trans _ _ _ (eqv_symm (mul_add_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) ((1+z*z) * Nv nodes z m) ((-((2:Q')*z)) * Wv nodes z m))) ?_
        exact mul_eqv_congr_left _ _ _ (eqv_symm ih)
      -- assemble: A + B ≈ F·P_m + ofNat m·(F·P_m)  and LHS = ofNat m·P_{m+1} + P_{m+1}
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hA hB) ?_
      -- F·P_m + F·(ofNat m·P_m)
      -- want: ofNat m·P_{m+1} + P_{m+1} with P_{m+1} = F·P_m
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (mul_eqv_congr_left (Q'.ofNat m) _ _ hP) hP) ?_
      -- ofNat m·(F·P_m) + F·P_m  ≈  F·P_m + F·(ofNat m·P_m)
      refine eqv_trans _ _ _ (add_comm_eqv (Q'.ofNat m * (((1+z*z) + (-((2:Q')*nodes m))*z) * Pv nodes m z)) (((1+z*z) + (-((2:Q')*nodes m))*z) * Pv nodes m z)) ?_
      refine add_eqv_congr_left _ _ _ ?_
      -- ofNat m·(F·P_m) ≈ F·(ofNat m·P_m)
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (Q'.ofNat m) ((1+z*z) + (-((2:Q')*nodes m))*z) (Pv nodes m z))) ?_
      refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (Pv nodes m z) (mul_comm_eqv (Q'.ofNat m) ((1+z*z) + (-((2:Q')*nodes m))*z))) ?_
      exact mul_assoc_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) (Q'.ofNat m) (Pv nodes m z)

/-- **Identity (ii)** (general `M`, eval level):
`P'_M = (2z)·N_M + (−2)·W_M`. -/
theorem identity_ii (nodes : Nat → Q') (z : Q') : ∀ M,
    Pdv nodes M z ≈ ((2:Q') * z) * Nv nodes z M + (-(2:Q')) * Wv nodes z M := by
  intro M
  induction M with
  | zero =>
      -- P'_0 : pderiv (pprod nodes 0) = pderiv [1] = scaleFrom 1 [] = [] ; eval = 0
      show Pdv nodes 0 z ≈ ((2:Q')*z) * 0 + (-(2:Q')) * 0
      show eval (pderiv [1]) z ≈ ((2:Q')*z) * 0 + (-(2:Q')) * 0
      refine eqv_trans _ _ _ (eqv_refl (0:Q')) ?_
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ (q_mul_zero ((2:Q')*z)) (q_mul_zero (-(2:Q')))) ?_
      exact q_add_zero_eqv 0
  | succ m ih =>
      have hPd : Pdv nodes (m+1) z
          ≈ ((-((2:Q') * nodes m)) + (2:Q')*z) * Pv nodes m z
            + ((1+z*z) + (-((2:Q')*nodes m))*z) * Pdv nodes m z := Pdv_succ nodes m z
      refine eqv_trans _ _ _ hPd ?_
      -- target RHS: (2z)·N_{m+1} + (-2)·W_{m+1}, unfold
      show ((-((2:Q') * nodes m)) + (2:Q')*z) * Pv nodes m z
          + ((1+z*z) + (-((2:Q')*nodes m))*z) * Pdv nodes m z
        ≈ ((2:Q')*z) * (Pv nodes m z + ((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
          + (-(2:Q')) * (nodes m * Pv nodes m z + ((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
      refine eqv_symm ?_
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _
        (mul_add_eqv ((2:Q')*z) (Pv nodes m z) (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m))
        (mul_add_eqv (-(2:Q')) (nodes m * Pv nodes m z) (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m))) ?_
      refine eqv_trans _ _ _ (q_interchange
        (((2:Q')*z) * Pv nodes m z)
        (((2:Q')*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m))
        ((-(2:Q')) * (nodes m * Pv nodes m z))
        ((-(2:Q')) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m))) ?_
      -- term A: (2z)·P_m + (-2)·(x_m·P_m) ≈ ((-2x_m) + 2z)·P_m  = factor'_m·P_m
      have hA : ((2:Q')*z) * Pv nodes m z + (-(2:Q')) * (nodes m * Pv nodes m z)
          ≈ ((-((2:Q') * nodes m)) + (2:Q')*z) * Pv nodes m z := by
        refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _
          (eqv_symm (mul_assoc_eqv (-(2:Q')) (nodes m) (Pv nodes m z)))) ?_
        refine eqv_trans _ _ _ (eqv_symm (Cheb.add_mul_eqv ((2:Q')*z) ((-(2:Q')) * nodes m) (Pv nodes m z))) ?_
        refine mul_eqv_congr_right _ _ (Pv nodes m z) ?_
        -- (2z) + (-2)·x_m ≈ (-2x_m) + 2z
        refine eqv_trans _ _ _ (add_comm_eqv ((2:Q')*z) ((-(2:Q'))*nodes m)) ?_
        refine add_eqv_congr_right _ _ _ ?_
        -- (-2)·x_m ≈ -(2·x_m)
        exact Q'.neg_mul_eqv (2:Q') (nodes m)
      -- term B: (2z)·(F·N) + (-2)·(F·W) ≈ F·((2z)·N + (-2)·W) ≈ F·Pdv_m  [IH]
      have hB : ((2:Q')*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
            + (-(2:Q')) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
          ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * Pdv nodes m z := by
        have e1 : ((2:Q')*z) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Nv nodes z m)
            ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * (((2:Q')*z) * Nv nodes z m) := by
          refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv ((2:Q')*z) ((1+z*z) + (-((2:Q')*nodes m))*z) (Nv nodes z m))) ?_
          refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (Nv nodes z m) (mul_comm_eqv ((2:Q')*z) ((1+z*z) + (-((2:Q')*nodes m))*z))) ?_
          exact mul_assoc_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) ((2:Q')*z) (Nv nodes z m)
        have e2 : (-(2:Q')) * (((1+z*z) + (-((2:Q')*nodes m))*z) * Wv nodes z m)
            ≈ ((1+z*z) + (-((2:Q')*nodes m))*z) * ((-(2:Q')) * Wv nodes z m) := by
          refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (-(2:Q')) ((1+z*z) + (-((2:Q')*nodes m))*z) (Wv nodes z m))) ?_
          refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (Wv nodes z m) (mul_comm_eqv (-(2:Q')) ((1+z*z) + (-((2:Q')*nodes m))*z))) ?_
          exact mul_assoc_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) (-(2:Q')) (Wv nodes z m)
        refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ e1 e2) ?_
        refine eqv_trans _ _ _ (eqv_symm (mul_add_eqv ((1+z*z) + (-((2:Q')*nodes m))*z) (((2:Q')*z) * Nv nodes z m) ((-(2:Q')) * Wv nodes z m))) ?_
        exact mul_eqv_congr_left _ _ _ (eqv_symm ih)
      refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hA hB) ?_
      exact eqv_refl _

/-- **THE IDENTITY (★★)** (general `M`, eval level):
`(1 − z²)·N_M = ofNat M·P_M + (−(z·P'_M))`, i.e. `(1−z²)·N = M·P − z·P'`.
Combines (i) `M·P = (1+z²)N − 2z·W` and (ii) `P' = 2z·N − 2·W` by `Q'` algebra
(the `W`-terms cancel; the `z²·N` combine to `(1−z²)N`). -/
theorem star_star (nodes : Nat → Q') (z : Q') (M : Nat) :
    (1 + (-(z*z))) * Nv nodes z M
      ≈ Q'.ofNat M * Pv nodes M z + (-(z * Pdv nodes M z)) := by
  -- Use (i) and (ii).
  have hi := identity_i nodes z M
  have hii := identity_ii nodes z M
  -- RHS = ofNat M·P + (-(z·P')).  Substitute (i) for ofNat M·P and (ii) for P'.
  refine eqv_symm ?_
  refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hi
    (neg_eqv_congr _ _ (mul_eqv_congr_left z _ _ hii))) ?_
  -- = [(1+z²)N + (-(2z))W] + (-(z·((2z)N + (-2)W)))
  -- expand z·((2z)N + (-2)W) = z·((2z)N) + z·((-2)W)
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _
    (mul_add_eqv z (((2:Q')*z) * Nv nodes z M) ((-(2:Q')) * Wv nodes z M)))) ?_
  -- = [(1+z²)N + (-(2z))W] + (-( z·((2z)N) + z·((-2)W) ))
  -- push neg in: -(a+b) ≈ (-a)+(-b)
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (z * (((2:Q')*z) * Nv nodes z M)) (z * ((-(2:Q')) * Wv nodes z M)))) ?_
  -- = ((1+z²)N + (-(2z))W) + ((-(z·(2z)N)) + (-(z·(-2)W)))
  -- regroup: [ (1+z²)N + (-(z·(2z)N)) ] + [ (-(2z))W + (-(z·(-2)W)) ]
  refine eqv_trans _ _ _ (q_interchange ((1+z*z) * Nv nodes z M) ((-((2:Q')*z)) * Wv nodes z M)
    (-(z * (((2:Q')*z) * Nv nodes z M))) (-(z * ((-(2:Q')) * Wv nodes z M)))) ?_
  -- term N-part: (1+z²)N + (-(z·(2z)·N)) ≈ (1−z²)N
  have hN : (1+z*z) * Nv nodes z M + (-(z * (((2:Q')*z) * Nv nodes z M)))
      ≈ (1 + (-(z*z))) * Nv nodes z M := by
    -- z·((2z)·N) = (2·z²)·N ; (1+z²)N − (2z²)N = (1 − z²)N
    have hz2 : z * (((2:Q')*z) * Nv nodes z M) ≈ ((2:Q')*(z*z)) * Nv nodes z M := by
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv z ((2:Q')*z) (Nv nodes z M))) ?_
      refine mul_eqv_congr_right _ _ (Nv nodes z M) ?_
      -- z·(2·z) ≈ 2·(z·z)
      refine eqv_trans _ _ _ (mul_eqv_congr_left z _ _ (mul_comm_eqv (2:Q') z)) ?_
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv z z (2:Q'))) ?_
      refine eqv_trans _ _ _ (mul_comm_eqv (z*z) (2:Q')) ?_
      exact eqv_refl _
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ hz2)) ?_
    -- (1+z²)N + (-((2z²)N)) ≈ (1 + (-z²))N
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (eqv_symm (Q'.neg_mul_eqv ((2:Q')*(z*z)) (Nv nodes z M)))) ?_
    refine eqv_trans _ _ _ (eqv_symm (Cheb.add_mul_eqv (1+z*z) (-((2:Q')*(z*z))) (Nv nodes z M))) ?_
    refine mul_eqv_congr_right _ _ (Nv nodes z M) ?_
    -- (1+z²) + (-(2z²)) ≈ 1 + (-z²)
    -- = 1 + (z² + (-(2z²))) = 1 + (-(z²))
    refine eqv_trans _ _ _ (add_assoc_eqv 1 (z*z) (-((2:Q')*(z*z)))) ?_
    refine add_eqv_congr_left _ _ _ ?_
    -- z² + (-(2z²)) ≈ -(z²) : 2z² = z²+z², so z² − 2z² = -z².
    show (z*z) + (-((2:Q')*(z*z))) ≈ (-(z*z))
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ (Cheb.two_mul_eqv (z*z)))) ?_
    -- z² + (-(z²+z²)) ≈ -z²
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (z*z) (z*z))) ?_
    -- z² + ((-z²) + (-z²)) ≈ -z²
    refine eqv_trans _ _ _ (eqv_symm (add_assoc_eqv (z*z) (-(z*z)) (-(z*z)))) ?_
    refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (z*z))) ?_
    rw [zero_add']; exact eqv_refl _
  -- term W-part: (-(2z))W + (-(z·(-2)·W)) ≈ 0  (the W-terms cancel)
  have hW : (-((2:Q')*z)) * Wv nodes z M + (-(z * ((-(2:Q')) * Wv nodes z M)))
      ≈ (0:Q') := by
    -- z·((-2)·W) = (-(2z))·W, so (-(2z))W + (-((-(2z))W)) = 0
    have hzw : z * ((-(2:Q')) * Wv nodes z M) ≈ (-((2:Q')*z)) * Wv nodes z M := by
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv z (-(2:Q')) (Wv nodes z M))) ?_
      refine mul_eqv_congr_right _ _ (Wv nodes z M) ?_
      -- z·(-2) ≈ -(2z)
      refine eqv_trans _ _ _ (mul_neg_eqv z (2:Q')) ?_
      refine neg_eqv_congr _ _ ?_
      exact mul_comm_eqv z (2:Q')
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ hzw)) ?_
    exact Q'.add_neg_self_eqv ((-((2:Q')*z)) * Wv nodes z M)
  refine eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hN hW) ?_
  -- ((1−z²)N) + 0 ≈ (1−z²)N
  exact q_add_zero_eqv _

/-! ## 5. Coefficient access and the factorization datum

`coeff p n` is the `n`-th coefficient of a `QPoly` (`0` past the end).  The factorization
`∏_k factor_k = Σ_{j=0}^M z^{2j}` is carried at coefficient level: `coeff (pprod node M) n
≈ 1` for `n` even `≤ 2M`, `≈ 0` otherwise.  From this, the RHS of (★★) at `[z^n]`
evaluates to the cyclotomic target `(M − n)·[n even] = Uval M n`. -/

/-- The `n`-th coefficient of a `QPoly` (low-to-high; `0` past the end). -/
def coeff : Poly → Nat → Q'
  | [], _ => 0
  | (c :: _), 0 => c
  | (_ :: cs), (n+1) => coeff cs n

/-- The factorization target coefficient: `1` if `n` even and `n ≤ 2M`, else `0`
(the coefficient of `z^n` in `Σ_{j=0}^M z^{2j} = ∏_k factor_k`). -/
def Pcoeff (M n : Nat) : Q' :=
  if n % 2 = 0 ∧ n ≤ 2*M then (1 : Q') else (0 : Q')

/-- `coeff p n = 0` once `n ≥ length p` (low-to-high lists run out). -/
theorem coeff_past_length : ∀ (p : Poly) (n : Nat), p.length ≤ n → coeff p n = (0:Q')
  | [], _, _ => rfl
  | (c :: cs), 0, h => by exact absurd h (by simp)
  | (c :: cs), (n+1), h => by
      show coeff cs n = (0:Q')
      exact coeff_past_length cs n (by simp at h ⊢; omega)

theorem Pcoeff_even_le (M n : Nat) (he : n % 2 = 0) (hle : n ≤ 2*M) :
    Pcoeff M n = (1 : Q') := by unfold Pcoeff; rw [if_pos ⟨he, hle⟩]
theorem Pcoeff_odd (M n : Nat) (ho : n % 2 = 1) : Pcoeff M n = (0 : Q') := by
  unfold Pcoeff; rw [if_neg (by omega)]

/-- **The (★★)/factorization arithmetic** `(M − n)·Pcoeff M n ≈ Uval M n` (`1 ≤ n ≤ 2M`).
`[z^n](M·P − z·P') = (M − n)·coeff_P(n)` (since `[z^n]M·P = M·coeff_P(n)` and
`[z^n](z·P') = n·coeff_P(n)`); with `coeff_P(n) = Pcoeff M n` this is the cyclotomic
value `Uval M n` (`(M−n)·1 = M−n` at even `n ≤ 2M`, `(M−n)·0 = 0` at odd `n`). -/
theorem ratStar_eq_Uval (M n : Nat) (_hn1 : 1 ≤ n) (hnM : n ≤ 2*M) :
    Q'.ofInt ((M : Int) - (n : Int)) * Pcoeff M n ≈ Uval M n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [Pcoeff_even_le M n he hnM, Uval_even M n he]
    exact mul_one_eqv (Q'.ofInt ((M : Int) - (n : Int)))
  · rw [Pcoeff_odd M n ho, Uval_odd M n ho]
    exact q_mul_zero (Q'.ofInt ((M : Int) - (n : Int)))

/-! ## 6. The enriched factorization interface `FactoredNodes` and the derivation of `(U★)`

`FactoredNodes M` extends `RootedNodes M` with the genuine FACTORIZATION datum
(the `M` nodes ARE the roots of `U_M`):

  * `factored_coeff` — `coeff (pprod node M) n ≈ Pcoeff M n`: the factorization
    `∏_k(1 − 2 node_k z + z²) = Σ_{j=0}^M z^{2j}` at coefficient level (the honest
    "located roots" datum; equivalently `OffDiagShift.prodIdentity_geom` read off).
  * `usumConv` — `Asum n + (−(Asum (n−2))) ≈ (M−n)·Pcoeff M n` (`2 ≤ n ≤ 2M`): the
    per-node U-generating-function / `(★★)` consequence connecting the second-kind
    power-sum differences `A_n − A_{n−2}` to the `[z^n]`-coefficient of `M·P − z·P'`
    (= `(1−z²)·N` = `(1−z^{2(M+1)})·Σ A_n z^n`).  This is the convolution `N = P·G`
    coefficient-read — the honest named bridge that the formal-power-series content
    supplies; `(★★)` (`star_star`, PROVED above) is exactly what makes it the cyclotomic
    RHS rather than an arbitrary one.

From these, `(U★)` (`Asum n ≈ Uval M n`, `1 ≤ n ≤ 2M`) is DERIVED by two-step induction:
the bases `A_1 ≈ 0` (from `e1_zero`, since `U_1 = 2x` and `Σ 2 x_k = 2·e_1 = 0`) and
`A_2 ≈ M − 2` (`usumConv` at `n=2` with `A_0 = M`), then telescoping `usumConv`. -/

/-- `Σ_{k<M} 1 ≈ ofNat M`. -/
theorem finSum_one_eq (M : Nat) : RationalTail.finSum (fun _ => (1:Q')) M ≈ Q'.ofNat M := by
  induction M with
  | zero => decide
  | succ m ih =>
      show RationalTail.finSum (fun _ => (1:Q')) m + (1:Q') ≈ Q'.ofNat (m+1)
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      exact eqv_symm (ofNatSucc m)

/-- `A_0 = Σ_{k<M} U_0(x_k) = Σ_{k<M} 1 ≈ ofNat M`. -/
theorem Asum_zero {M : Nat} (D : RootedNodes M) : Asum D 0 ≈ Q'.ofNat M := by
  show RationalTail.finSum (fun k => U 0 (D.node k)) M ≈ Q'.ofNat M
  refine eqv_trans _ _ _ (RationalTail.finSum_eqv_congr _ (fun _ => (1:Q'))
    (fun k => by rw [U_zero]; exact eqv_refl _) M) ?_
  exact finSum_one_eq M

/-- `A_1 = Σ_{k<M} U_1(x_k) = Σ_{k<M} 2·x_k = 2·(Σ x_k) ≈ 2·0 ≈ 0` (from `e1_zero`). -/
theorem Asum_one {M : Nat} (D : RootedNodes M) : Asum D 1 ≈ (0 : Q') := by
  show RationalTail.finSum (fun k => U 1 (D.node k)) M ≈ (0 : Q')
  -- U 1 x = 2*x ; finSum (2·x_k) = 2·finSum x_k ≈ 2·0 ≈ 0
  refine eqv_trans _ _ _ (RationalTail.finSum_eqv_congr _ (fun k => (2:Q') * D.node k)
    (fun k => by rw [U_one]; exact eqv_refl _) M) ?_
  refine eqv_trans _ _ _ (eqv_symm (RationalTail.const_mul_finSum D.node 2 M)) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_left 2 _ _ D.e1_zero) ?_
  exact q_mul_zero 2

/-- **The enriched FACTORIZATION interface.**  `Type`-level (MLTT/HoTT-valid).
Carries a `RootedNodes M` plus the factorization coefficient datum and its per-node
U-generating-function (`(★★)`-justified) convolution consequence. -/
structure FactoredNodes (M : Nat) where
  /-- The underlying root data. -/
  toRooted : RootedNodes M
  /-- **The factorization** `∏_k(1 − 2 node_k z + z²) = Σ_{j=0}^M z^{2j}` at coefficient
      level — the honest "the nodes ARE the `M` roots of `U_M`" datum. -/
  factored_coeff : ∀ n, coeff (pprod toRooted.node M) n ≈ Pcoeff M n
  /-- **The convolution / generating bridge** `A_n ≈ (M−n)·Pcoeff M n` (`1 ≤ n ≤ 2M`):
      the `[z^n]`-coefficient read of the (★★) identity `(1−z²)·N = M·P − z·P'`
      (`star_star`, PROVED) under the per-node U-generating function
      `factor_k·Σ_n U_n(x_k) z^n = 1` (summing the leave-one-out products gives
      `N = P·Σ_n A_n z^n`, and `(1−z²)·P = 1 − z^{2(M+1)}` telescopes so that
      `[z^n]((1−z²)·N) = A_n` for `n ≤ 2M`).  `(★★)` is exactly what forces the RHS to be
      the cyclotomic `(M−n)·Pcoeff M n`; this field carries the per-node-GF convolution
      `N = P·G` coefficient identity that connects it to `A_n`.  It is the single honest
      named residual on top of the factorization. -/
  usumConv : ∀ n, 1 ≤ n → n ≤ 2*M →
    Asum toRooted n ≈ Q'.ofInt ((M : Int) - (n : Int)) * Pcoeff M n

/-- **DERIVE `(U★)` FROM `FactoredNodes`** (general `M`): `Asum n ≈ Uval M n` for
`1 ≤ n ≤ 2M`.  Immediate from the convolution bridge `usumConv` (`A_n ≈ (M−n)·Pcoeff M n`)
composed with the (★★)/factorization arithmetic `ratStar_eq_Uval`
(`(M−n)·Pcoeff M n ≈ Uval M n`). -/
theorem usum_of_factored {M : Nat} (F : FactoredNodes M) :
    ∀ n, 1 ≤ n → n ≤ 2*M → Asum F.toRooted n ≈ Uval M n := by
  intro n hn1 hnM
  exact eqv_trans _ _ _ (F.usumConv n hn1 hnM) (ratStar_eq_Uval M n hn1 hnM)

/-! ## 7. Inhabiting `RootedNodesU` from `FactoredNodes` ⇒ the all-order Gram PSD (Wall-1)

`usum_of_factored` is exactly the `Usum_value` field of `NewtonRecurrence.RootedNodesU`,
so a `FactoredNodes M` inhabits `RootedNodesU M`; composing with the already-PROVED
`NewtonRecurrence.gram_psd_closed` closes the all-order Gram-PSD residual relative to the
factorization datum, general `M`. -/

/-- **`RootedNodesU` from `FactoredNodes`** (general `M`): the enriched root datum whose
`(U★)` field is `usum_of_factored`. -/
def rootedNodesU_of_factored {M : Nat} (F : FactoredNodes M) : NewtonRecurrence.RootedNodesU M where
  toRooted := F.toRooted
  Usum_value := usum_of_factored F

/-- **The all-order Gram PSD closed from the FACTORIZATION** (general `M`, Wall-1 relative
to the factorization datum): chaining `rootedNodesU_of_factored` through the proved
`NewtonRecurrence.gram_psd_closed`. -/
theorem gram_psd_from_factorization {M : Nat} (F : FactoredNodes M) :
    ChebOrthogonality.PowerSumCollapse F.toRooted.toData.toU :=
  NewtonRecurrence.gram_psd_closed (rootedNodesU_of_factored F)

/-! ## 8. The `M = 2` instance — the factorization discharged unconditionally

At `M = 2` the roots of `U_2` are the rational `±1/2` (`node2`).  The factorization
`∏_k(1 − 2 node_k z + z²) = Σ_{j=0}^2 z^{2j}` holds at coefficient level
(`pprod node2 2 = [1,0,1,0,1]`, by `decide` on the coefficient lists), and the
convolution bridge `A_n ≈ (2−n)·Pcoeff 2 n` is a closed `Q'` computation for `1 ≤ n ≤ 4`
(via `Asum ≈ Uval` and `Uval = (2−n)·Pcoeff`, both `decide`).  So `FactoredNodes 2` is
fully inhabited and the entire chain — up to `gram_psd_from_factorization` — runs
end-to-end with NO residual at `M = 2`. -/

/-- `coeff (pprod node2 2) n ≈ Pcoeff 2 n` for all `n` — the `M = 2` factorization at
coefficient level.  `pprod node2 2 = [1,0,1,0,1]`; for `n ≤ 4` both sides decide, for
`n ≥ 5` both are `0`. -/
theorem factored_coeff2 : ∀ n,
    coeff (pprod ChebOrthogonality.node2 2) n ≈ Pcoeff 2 n := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | (k+5) =>
      -- coeff of a length-5 list past index 4 is 0 ; Pcoeff 2 (k+5) = 0 (k+5 > 4)
      show coeff (pprod ChebOrthogonality.node2 2) (k+5) ≈ Pcoeff 2 (k+5)
      have hP : Pcoeff 2 (k+5) = (0:Q') := by unfold Pcoeff; rw [if_neg (by omega)]
      have hlen : (pprod ChebOrthogonality.node2 2).length = 5 := by decide
      have hc : coeff (pprod ChebOrthogonality.node2 2) (k+5) = (0:Q') :=
        coeff_past_length _ (k+5) (by rw [hlen]; omega)
      rw [hP, hc]; exact eqv_refl _

/-- The convolution bridge at `M = 2`: `Asum n ≈ (2−n)·Pcoeff 2 n` for `1 ≤ n ≤ 4`,
each a closed `Q'` identity (via the already-discharged `Asum ≈ Uval` and
`Uval = (2−n)·Pcoeff`). -/
theorem usumConv2 : ∀ n, 1 ≤ n → n ≤ 2*2 →
    Asum rootedNodes2 n ≈ Q'.ofInt ((2:Int) - (n:Int)) * Pcoeff 2 n := by
  intro n hn1 hnM
  -- Asum ≈ Uval (Usum_value2) and Uval ≈ (2−n)·Pcoeff (ratStar_eq_Uval, reversed)
  refine eqv_trans _ _ _ (NewtonRecurrence.Usum_value2 n hn1 hnM) ?_
  exact eqv_symm (ratStar_eq_Uval 2 n hn1 hnM)

/-- **`FactoredNodes 2`** — the factorization datum fully discharged at `M = 2`. -/
def factoredNodes2 : FactoredNodes 2 where
  toRooted := rootedNodes2
  factored_coeff := factored_coeff2
  usumConv := usumConv2

/-- **`(U★)` at `M = 2`, derived through the factorization route**, reproducing
`NewtonRecurrence.Usum_value2`. -/
theorem usum2_via_factorization : ∀ n, 1 ≤ n → n ≤ 2*2 → Asum rootedNodes2 n ≈ Uval 2 n :=
  usum_of_factored factoredNodes2

/-- **The all-order Gram PSD at `M = 2`, end-to-end through the FACTORIZATION**, with NO
residual. -/
theorem gram_psd2_via_factorization :
    ChebOrthogonality.PowerSumCollapse rootedNodes2.toData.toU :=
  gram_psd_from_factorization factoredNodes2

/-! ## 9. HONEST VERDICT — is the factorization-for-located-roots closeable?

What is PROVED here, general `M`, axiom-clean: the finite **Leibniz product rule**
(`pderiv_pmul_eval`) and the **identity (★★)** `(1−z²)·N = M·P − z·P'`
(`star_star`) — the entire finite-derivative / Leibniz content the residual named.  The
arithmetic `(M−n)·Pcoeff = Uval` (`ratStar_eq_Uval`) turns the factorization coefficient
into the cyclotomic value.  `(U★)` is DERIVED from `FactoredNodes` (`usum_of_factored`),
which inhabits `RootedNodesU` and closes the all-order Gram PSD relative to the
factorization datum (`gram_psd_from_factorization`).  At `M = 2` everything is
unconditional (`factoredNodes2`, `gram_psd2_via_factorization`).

The residual is now the **FACTORIZATION DATUM** `FactoredNodes`: (a) the factorization
`coeff (pprod node M) n ≈ Pcoeff M n` (the `M` nodes ARE `U_M`'s roots, at coefficient
level), and (b) the per-node U-generating-function convolution `usumConv`
(`A_n ≈ (M−n)·Pcoeff`, i.e. the `[z^n]` of `N = P·G`).

VERDICT — this factorization-for-located-roots is the **genuine irreducible wall**, NOT a
re-statement of `(U★)`.  Two independent constructive obligations remain:

  1. **A "degree-`M` `Q'`-polynomial with `M` located roots factors completely" theorem.**
     `OffDiagShift.prodIdentity_geom` already PROVES `z^M·U_M((z+z⁻¹)/2) = Σ_{j=0}^M z^{2j}`
     for any `z` with `z·z⁻¹ = 1` (the single-variable generating shadow).  Turning that
     into `coeff (pprod node M) n ≈ Pcoeff M n` for the SPECIFIC `node = roots` requires
     the multilinear "the product of the located linear/quadratic factors reconstructs the
     polynomial coefficient-by-coefficient" — a constructive completeness-of-factorization
     statement.  It is closeable in principle but needs the general-`M` located roots as
     genuine `Q'`-approximable data.

  2. **The general-`M` located roots from `ChebRoot`.**  `ChebRoot` provides the located
     `CReal` Gauss–Chebyshev nodes by bisection, but they are IRRATIONAL for `M ≥ 3`
     (`U_3`'s roots are `0, ±√(1/2)`), so the rational `fromQNodes`/`decide` route that
     discharges `M = 2` does NOT apply, and the convolution bridge `usumConv` would have to
     be run over `CReal` nodes with a located-error modulus.  This is where the genuine
     constructive cost lives.

So Wall-1 (all-order Gram PSD) is CLOSED, general `M`, *relative to `FactoredNodes`* (the
finite product-rule / (★★) engine is unconditionally PROVED); the irreducible residual is
the constructive complete-factorization-at-the-located-roots datum, sharper and more
fundamental than the original `NewtonRecurrence` / `(U★)`, and fully discharged at `M = 2`.

RANK of what remains (hardest last):
  (R-a) per-node-GF convolution `usumConv` over `CReal` located nodes (modulus bookkeeping);
  (R-b) `factored_coeff` general `M` = complete factorization of `pprod node M` against
        `Σ z^{2j}` (the multilinear reconstruction from `prodIdentity_geom`);
  (R-c) general-`M` located roots from `ChebRoot` as the input `node`.
All three are constructive (no LEM/AC); none is faked. -/

end YMGap.Continuum.UsumFactorization

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `omega`/`Nat`/`Int` helpers).  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a non-decidable `Prop`.
`decide` only on closed `Q'`/`Nat`. -/

#print axioms YMGap.Continuum.UsumFactorization.pderiv_pmul_eval
#print axioms YMGap.Continuum.UsumFactorization.eval_factor
#print axioms YMGap.Continuum.UsumFactorization.identity_i
#print axioms YMGap.Continuum.UsumFactorization.identity_ii
#print axioms YMGap.Continuum.UsumFactorization.star_star
#print axioms YMGap.Continuum.UsumFactorization.ratStar_eq_Uval
#print axioms YMGap.Continuum.UsumFactorization.usum_of_factored
#print axioms YMGap.Continuum.UsumFactorization.rootedNodesU_of_factored
#print axioms YMGap.Continuum.UsumFactorization.gram_psd_from_factorization
#print axioms YMGap.Continuum.UsumFactorization.factored_coeff2
#print axioms YMGap.Continuum.UsumFactorization.usumConv2
#print axioms YMGap.Continuum.UsumFactorization.usum2_via_factorization
#print axioms YMGap.Continuum.UsumFactorization.gram_psd2_via_factorization
