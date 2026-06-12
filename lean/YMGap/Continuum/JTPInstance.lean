/-
# Instantiating the Bishop C¹-uniform-limit engine for the Jacobi theta product
  (Wall-2 differentiation: the per-factor moduli)

This module supplies the CONCRETE per-factor analytic data that the generic
constructive C¹-limit engine `TsumDeriv.fdDeriv_of_unif` consumes when specialised
to the Jacobi theta product — the genuine "M_k / N(ε) / equicontinuity" moduli
named by the constructive-analysis route (Bishop & Bridges *Constructive Analysis*
1985 Ch.2; Bridger *Real Analysis: A Constructive Approach* 2019 Ch.6; CoRN's
normal⇒uniform⇒differentiate architecture).

## The route (logarithm-free product-rule + geometric majorant)

The `k`-th Jacobi factor, in the `θ`-variable with `q = a ∈ (0,1)` fixed, is

    f_k(θ) = 1 + 2·q^{2k+1}·c + q^{4k+2},     c = cos 2θ ∈ [−1,1],

with `θ`-derivative contribution `f_k'(θ) = −4·q^{2k+1}·s`, `s = sin 2θ ∈ [−1,1]`.
The whole differentiation content is captured by THREE algebraic per-factor facts,
all proved here WITHOUT any attained sup/max over `θ` (the scout-flagged pitfall):

* **`jFac` / `jDeriv`** — the factor and its formal `θ`-derivative as `Q'` values
  of the abstract bounded data `c, s` (we carry `|c| ≤ 1`, `|s| ≤ 1` as hypotheses,
  exactly the algebraic `|cos2θ| ≤ 1`, `|sin2θ| ≤ 1` the route mandates).
* **`jDeriv_abs_le` (the `M_k`)** — the per-factor derivative magnitude bound
  `|f_k'(θ)| ≤ 4·q^{2k+1}`, denominator-free, by `|s| ≤ 1` algebraically.
* **`jFac_lb` (denominator positivity)** — `f_k(θ) ≥ (1 − q^{2k+1})² > 0` directly
  from `c ≥ −1` (NOT a classical minimum), the bound the route names for keeping
  the per-factor log-derivative bounded.
* **`jTail_lt` / `jModulus` (the `N(ε)`)** — the closed-form uniform geometric
  cutoff: the per-factor majorant `4·q^{2k+1}` has geometric tail summable at base
  `q² < 1`, with cutoff delivered by the existing `HKConvGen.pow_base_le` engine.

These are precisely the inputs `TsumDeriv.C1Inputs` requires for the theta family
(pointwise + uniform derivative convergence moduli + equicontinuity), reduced to
the per-factor level.

## The honest residual (AGENTS.md Rule 6)

What this module does NOT do: assemble these per-factor moduli into a full
`C1Inputs f f' F g θ` for the *specific* `dSeriesCReal` / `Rhalf` truncation
families and thereby discharge `DiffProduct.C1ToEquiv`.  The obstruction is
structural and is pinned down sharply in `docs/jtp-closure-progress.md`: the
series side `dSeriesCReal` (super-geometric `~a^{(M+1)²}`) and the product side
`Rhalf` (geometric `~(a·a)^M`) are DIFFERENT finite truncation families that
coincide only in the limit; the `C1ToEquiv.bridge` field is therefore the genuine
`CReal.Equiv` of those two limits — the differentiation–limit interchange — and is
NOT produced by the per-factor moduli alone.  The per-factor `M_k`/`N(ε)` engine
inputs built here are the analytic content the route names; the residual is their
assembly into the family-level `C1Inputs` plus the Gauss derivative-value
identification, exposed downstream as `DiffProduct.C1ToEquiv`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.JTPIdentity
import YMGap.Constructive.AbsQ
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.JTPInstance

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConvGen

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The geometric per-factor amplitude `q^{2k+1}` and base-`q²` decay

The per-factor amplitude `amp q k = q^{2k+1}` controls every per-factor estimate
below.  Its decay is geometric at base `q·q`: `amp q (k+1) = (q·q)·amp q k`, so the
existing general-base modulus engine `HKConvGen.pow_base_le` (at base `q²`) gives a
closed-form cutoff for `amp q k ≤ δ`. -/

/-- The per-factor amplitude `amp q k = q^{2k+1}`. -/
def amp (q : Q') (k : Nat) : Q' := q ^ (2 * k + 1)

theorem amp_nonneg {q : Q'} (hq0 : (0 : Q') ≤ q) (k : Nat) : (0 : Q') ≤ amp q k :=
  Q'.pow_nonneg q hq0 _

/-- `amp q k ≤ q^{2k}` (drop the trailing factor `q ≤ 1`). -/
theorem amp_le_even {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (k : Nat) :
    amp q k ≤ q ^ (2 * k) := by
  show q ^ (2 * k + 1) ≤ q ^ (2 * k)
  -- q^{2k+1} = q·q^{2k} ≤ 1·q^{2k} = q^{2k}
  show q * q ^ (2 * k) ≤ q ^ (2 * k)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right q 1 (q ^ (2 * k)) hq1 (Q'.pow_nonneg q hq0 (2 * k))) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (q ^ (2 * k)))

/-- `q^{2k} ≈ (q·q)^k` — the even power as a power of `q²` (reuse of the
`JTPIdentity.aa_pow_eqv` Gaussian-vs-geometric helper). -/
theorem even_pow_eqv (q : Q') (k : Nat) : q ^ (2 * k) ≈ (q * q) ^ k := by
  have h2k : 2 * k = k + k := by omega
  rw [h2k]
  exact JTPIdentity.aa_pow_eqv q k

/-! ## 1. The Jacobi factor and its formal `θ`-derivative

`jFac q k c = 1 + 2·q^{2k+1}·c + q^{4k+2}` with `c = cos 2θ`, and the formal
`θ`-derivative `jDeriv q k s = −4·q^{2k+1}·s` with `s = sin 2θ`.  We work with the
bounded data `c, s` abstractly (carrying `|c| ≤ 1`, `|s| ≤ 1`), so every estimate
is purely algebraic — never an attained sup/max over `θ`. -/

/-- The `k`-th Jacobi factor `f_k(θ) = 1 + 2·q^{2k+1}·c + q^{4k+2}` (`c = cos 2θ`). -/
def jFac (q : Q') (k : Nat) (c : Q') : Q' :=
  1 + ((amp q k + amp q k) * c + amp q k * amp q k)

/-- The `k`-th factor's formal `θ`-derivative `f_k'(θ) = −(4·q^{2k+1})·s`
(`s = sin 2θ`).  (`d/dθ [2 q^{2k+1} cos 2θ] = −4 q^{2k+1} sin 2θ`.) -/
def jDeriv (q : Q') (k : Nat) (s : Q') : Q' :=
  -(((amp q k + amp q k) + (amp q k + amp q k)) * s)

/-! ### `amp q k · amp q k = q^{4k+2}` consistency (the constant term) -/

/-- `amp q k · amp q k ≈ q^{4k+2}` — the squared amplitude is the constant term. -/
theorem amp_sq_eqv (q : Q') (k : Nat) : amp q k * amp q k ≈ q ^ (4 * k + 2) := by
  show q ^ (2 * k + 1) * q ^ (2 * k + 1) ≈ q ^ (4 * k + 2)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv q (2 * k + 1) (2 * k + 1))) ?_
  have he : (2 * k + 1) + (2 * k + 1) = 4 * k + 2 := by omega
  rw [he]
  exact Q'.eqv_refl _

/-! ## 2. The per-factor derivative magnitude bound (the `M_k`)

`|f_k'(θ)| = |4·q^{2k+1}·s| ≤ 4·q^{2k+1}` using `|s| ≤ 1` algebraically.  This is
the denominator-free `M_k ≤ 4·amp q k` the route names; it needs NO attained max. -/

/-- `0 ≤ a` and `0 ≤ b` give `0 ≤ a + b` (local helper). -/
theorem add_nonneg' {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b :=
  Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg a b hb)

/-- `4·amp q k = (amp+amp)+(amp+amp)`, packaged as a nonneg `Q'`. -/
def fourAmp (q : Q') (k : Nat) : Q' := (amp q k + amp q k) + (amp q k + amp q k)

theorem fourAmp_nonneg {q : Q'} (hq0 : (0 : Q') ≤ q) (k : Nat) :
    (0 : Q') ≤ fourAmp q k := by
  have h := amp_nonneg hq0 k
  exact add_nonneg' (add_nonneg' h h) (add_nonneg' h h)

/-- **The per-factor derivative magnitude bound (the `M_k`).**  For `|s| ≤ 1`
(i.e. `−1 ≤ s ≤ 1`, the algebraic `|sin 2θ| ≤ 1`), the `k`-th factor's formal
`θ`-derivative satisfies `|f_k'(θ)| ≤ 4·q^{2k+1} = fourAmp q k`.  Proved purely
algebraically (`Q'.abs_le` + the sign-cased `Q'.mul_le_of_bounds`), with NO
attained sup/max over `θ`. -/
theorem jDeriv_abs_le {q : Q'} (hq0 : (0 : Q') ≤ q) (k : Nat) {s : Q'}
    (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q')) :
    Q'.abs (jDeriv q k s) ≤ fourAmp q k := by
  have hFA : (0 : Q') ≤ fourAmp q k := fourAmp_nonneg hq0 k
  -- |jDeriv| = |-(fourAmp·s)| = |fourAmp·s| ≤ fourAmp·1 = fourAmp
  -- fourAmp·s ∈ [−fourAmp, fourAmp] from |s| ≤ 1 and fourAmp ≥ 0.
  have hbd : (fourAmp q k) * s ≤ fourAmp q k * 1 :=
    Q'.mul_le_mul_of_nonneg_left s 1 (fourAmp q k) hs2 hFA
  have hbd2 : fourAmp q k * 1 ≈ fourAmp q k := Q'.mul_one_eqv _
  have hub : (fourAmp q k) * s ≤ fourAmp q k :=
    Q'.le_trans' _ _ _ hbd (Q'.le_of_eqv hbd2)
  -- lower: −fourAmp ≤ fourAmp·s.  fourAmp·(−1) ≤ fourAmp·s, and fourAmp·(−1) ≈ −fourAmp.
  have hbdl : fourAmp q k * (-1) ≤ fourAmp q k * s :=
    Q'.mul_le_mul_of_nonneg_left (-1) s (fourAmp q k) hs1 hFA
  have hbdl2 : (fourAmp q k * (-1)) ≈ (-(fourAmp q k)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (fourAmp q k) 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (fourAmp q k))
  have hlb : -(fourAmp q k) ≤ fourAmp q k * s :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hbdl2) hbdl
  -- |fourAmp·s| ≤ fourAmp
  have habs : Q'.abs (fourAmp q k * s) ≤ fourAmp q k := Q'.abs_le hlb hub
  -- |jDeriv| = |-(fourAmp·s)|; jDeriv q k s = -((amp+amp)+(amp+amp))·s = -(fourAmp·s)
  show Q'.abs (-(((amp q k + amp q k) + (amp q k + amp q k)) * s)) ≤ fourAmp q k
  -- abs(-y) = abs(y); use TsumDeriv.Q'.abs_neg
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (YMGap.Continuum.TsumDeriv.Q'.abs_neg
    (((amp q k + amp q k) + (amp q k + amp q k)) * s))) ?_
  exact habs

/-! ## 3. Denominator positivity (the route's `(1−q^{2k+1})²` lower bound)

`f_k(θ) ≥ (1 − q^{2k+1})²` directly from `c ≥ −1` and `amp ≥ 0` — NOT a classical
minimum.  Concretely `f_k − (1−amp)² = 2·amp·(c+1) ≥ 0`.  This is the route's
denominator-free positivity, keeping the per-factor log-derivative bounded. -/

open YMGap.Continuum.TsumDeriv.Q' (add_eqv_congr eqv_of_eq) in
/-- The algebraic identity in opaque variables `A, c`:
`1 + ((A+A)·c + A·A) ≈ (1 + (-A))·(1 + (-A)) + (A+A)·(c+1)`.  Pure `Q'` ring
rearrangement over `eqv` (no `set`; `A` is a free variable so the goal is literal). -/
theorem jFac_split_abs (A c : Q') :
    (1 + ((A + A) * c + A * A)) ≈
      ((1 + (-A)) * (1 + (-A)) + (A + A) * (c + 1)) := by
  -- (1 + (-A))·(1 + (-A)) ≈ (1 + (-A)) + ((-A) + (-A)·(-A))
  have hsq : ((1 + (-A)) * (1 + (-A)))
      ≈ ((1 + (-A)) + ((-A) + (-A) * (-A))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-A) (1 + (-A))) ?_
    refine add_eqv_congr (Q'.one_mul_eqv (1 + (-A))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-A) 1 (-A)) ?_
    exact Q'.add_eqv_congr_right _ _ ((-A) * (-A)) (Q'.mul_one_eqv (-A))
  have hAA : ((-A) * (-A)) ≈ (A * A) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv A (-A)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv A A)) ?_
    exact Q'.neg_neg_eqv (A * A)
  have hcross : ((A + A) * (c + 1)) ≈ ((A + A) * c + (A + A)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (A + A) c 1) ?_
    exact Q'.add_eqv_congr_left ((A + A) * c) _ _ (Q'.mul_one_eqv (A + A))
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (add_eqv_congr hsq hcross) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ ((A + A) * c + (A + A))
      (Q'.add_eqv_congr_left (1 + (-A)) _ _
        (Q'.add_eqv_congr_left (-A) _ _ hAA))) ?_
  show ((((1 : Q') + (-A)) + ((-A) + A * A)) + ((A + A) * c + (A + A)))
      ≈ (1 + ((A + A) * c + A * A))
  -- First reassociate the leading block `(1+(-A)) + ((-A)+A·A) ≈ 1 + ((-A)+((-A)+A·A))`.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ ((A + A) * c + (A + A))
      (Q'.add_assoc_eqv 1 (-A) ((-A) + A * A))) ?_
  -- Then pull the leading `1` across the whole sum.
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv 1 ((-A) + ((-A) + A * A)) ((A + A) * c + (A + A))) ?_
  refine Q'.add_eqv_congr_left 1 _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ ((A + A) * c + (A + A))
      (Q'.eqv_symm (Q'.add_assoc_eqv (-A) (-A) (A * A)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (((-A) + (-A)) + A * A) ((A + A) * c + (A + A))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv ((A + A) * c) (A + A) (((-A) + (-A)) + A * A)) ?_
  refine Q'.add_eqv_congr_left ((A + A) * c) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (A + A) ((-A) + (-A)) (A * A))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 (A * A) ?_) ?_
  · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (A + A) (-A) (-A))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-A) (Q'.add_assoc_eqv A A (-A))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-A)
        (Q'.add_eqv_congr_left A _ _ (Q'.add_neg_self_eqv A))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-A) (eqv_of_eq (Q'.add_zero' A))) ?_
    exact Q'.add_neg_self_eqv A
  · exact eqv_of_eq (Q'.zero_add' (A * A))

/-- The algebraic identity `jFac q k c ≈ (1−amp)² + (amp+amp)·(c+1)`, the
specialisation of `jFac_split_abs` at `A = amp q k`. -/
theorem jFac_split (q : Q') (k : Nat) (c : Q') :
    jFac q k c ≈
      ((1 + (-(amp q k))) * (1 + (-(amp q k)))
        + (amp q k + amp q k) * (c + 1)) :=
  jFac_split_abs (amp q k) c

/-- **Denominator positivity (route's `(1−q^{2k+1})²` lower bound).**  For
`c ≥ −1` (the algebraic `cos 2θ ≥ −1`) and `0 ≤ q`, the `k`-th factor satisfies
`(1 − q^{2k+1})² ≤ f_k(θ)`.  Directly from `c + 1 ≥ 0`, NOT a classical minimum. -/
theorem jFac_lb {q : Q'} (hq0 : (0 : Q') ≤ q) (k : Nat) {c : Q'}
    (hc : (-1 : Q') ≤ c) :
    (1 + (-(amp q k))) * (1 + (-(amp q k))) ≤ jFac q k c := by
  have hA : (0 : Q') ≤ amp q k := amp_nonneg hq0 k
  -- c + 1 ≥ 0 from c ≥ −1
  have hc1 : (0 : Q') ≤ c + 1 := by
    have h := Q'.add_le_add_right _ _ 1 hc  -- (-1) + 1 ≤ c + 1
    refine Q'.le_trans' _ _ _ ?_ h
    have hz : ((-1 : Q') + 1) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-1) 1) (Q'.add_neg_self_eqv 1)
    exact Q'.ge_of_eqv hz
  have hcross_nn : (0 : Q') ≤ (amp q k + amp q k) * (c + 1) :=
    Q'.mul_nonneg _ _ (add_nonneg' hA hA) hc1
  -- (1−amp)² ≤ (1−amp)² + (amp+amp)(c+1) ≈ jFac
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg ((1 + (-(amp q k))) * (1 + (-(amp q k)))) _ hcross_nn) ?_
  exact Q'.ge_of_eqv (jFac_split q k c)

/-! ## 4. The uniform geometric cutoff `N(ε)` (the route's tail bound)

`fourAmp q k = 4·q^{2k+1} ≤ 4·(q²)^k`, geometric at base `q² < 1`.  The existing
general-base modulus `HKConvGen.pow_base_le` gives a closed-form cutoff so that
`(q²)^k ≤ δ` for `k ≥ N`; chaining with `fourAmp ≤ 4·(q²)^k` yields the per-factor
uniform modulus `N(ε)` with `fourAmp q k ≤ ε`. -/

/-- The geometric-majorant constant `Cfour = (1+1)+(1+1) = 4`. -/
def Cfour : Q' := (1 + 1) + (1 + 1)

theorem Cfour_nonneg : (0 : Q') ≤ Cfour := by
  have h1 : (0 : Q') ≤ (1 : Q') := Q'.zero_le_one
  exact add_nonneg' (add_nonneg' h1 h1) (add_nonneg' h1 h1)

open YMGap.Continuum.TsumDeriv.Q' (add_eqv_congr) in
/-- `Cfour · qe ≈ (qe+qe)+(qe+qe)` (distribute `((1+1)+(1+1))·qe`). -/
theorem Cfour_mul_eqv (qe : Q') : Cfour * qe ≈ ((qe + qe) + (qe + qe)) := by
  show ((1 + 1) + (1 + 1)) * qe ≈ ((qe + qe) + (qe + qe))
  -- ((1+1)+(1+1))·qe ≈ (1+1)·qe + (1+1)·qe ≈ (1·qe+1·qe) + (1·qe+1·qe) ≈ (qe+qe)+(qe+qe)
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 + 1) (1 + 1) qe) ?_
  have hone : ((1 + 1) * qe) ≈ (qe + qe) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 qe) ?_
    exact add_eqv_congr (Q'.one_mul_eqv qe) (Q'.one_mul_eqv qe)
  exact add_eqv_congr hone hone

/-- **`fourAmp q k ≤ Cfour · (q·q)^k`** — the geometric majorant at base `q²`.
`fourAmp = 4·amp ≤ 4·q^{2k} ≈ 4·(q·q)^k`. -/
theorem fourAmp_le_geo {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (k : Nat) :
    fourAmp q k ≤ Cfour * (q * q) ^ k := by
  have hae : amp q k ≤ q ^ (2 * k) := amp_le_even hq0 hq1 k
  have hstep : fourAmp q k ≤ (q ^ (2 * k) + q ^ (2 * k)) + (q ^ (2 * k) + q ^ (2 * k)) :=
    Q'.add_le_add (Q'.add_le_add hae hae) (Q'.add_le_add hae hae)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- Cfour · (q·q)^k ≈ Cfour · q^{2k} ≈ (q^{2k}+q^{2k})+(q^{2k}+q^{2k})
  have hqe_eqv : q ^ (2 * k) ≈ (q * q) ^ k := even_pow_eqv q k
  have h4 : (Cfour * (q * q) ^ k)
      ≈ ((q ^ (2 * k) + q ^ (2 * k)) + (q ^ (2 * k) + q ^ (2 * k))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left Cfour _ _ (Q'.eqv_symm hqe_eqv)) ?_
    exact Cfour_mul_eqv (q ^ (2 * k))
  exact Q'.ge_of_eqv h4

/-! ### The closed-form uniform modulus `N(ε)`

For `0 < q < 1`, the per-factor majorant `fourAmp q k ≤ Cfour·(q²)^k` has a
closed-form cutoff: `pow_base_le` at base `q² < 1` gives `N` with `(q²)^k ≤ δ`,
`δ = ε/Cfour`, for `k ≥ N`, and `Cfour·δ ≈ ε`. -/

/-- `q·q < 1` for `0 < q < 1`. -/
theorem qq_lt_one {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    q * q < (1 : Q') := by
  have hqq_le : q * q ≤ q := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0)) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv q)
  exact HKPos.q_lt_of_le_of_lt hqq_le hq1

/-- `Cfour > 0`. -/
theorem Cfour_pos : (0 : Q') < Cfour := by
  have h : (0 : Int) < Cfour.num := by decide
  exact CReal.pos_of_num_pos h

/-- **The explicit closed-form cutoff `N(ε)`** (Rule 8.3 `Type`-level data): the
`powBaseCutoff` of the existing geometric engine at base `q²` and tolerance
`δ = ε/Cfour`.  Fully recoverable as a `Nat`-valued function of `ε`. -/
def fourAmpCutoff (q ε : Q') : Nat :=
  HKConvGen.powBaseCutoff (q * q) (HKConv.divPos ε Cfour)

/-- **THE UNIFORM PER-FACTOR MODULUS `N(ε)`, with the explicit cutoff.**  For
`0 < q < 1` and `ε > 0`, the per-factor derivative majorant satisfies
`fourAmp q k ≤ ε` for ALL `k ≥ fourAmpCutoff q ε`.  The route's geometric tail
cutoff, built on `HKConvGen.pow_base_le_cutoff` at base `q²` — no `Exists.choose`,
the cutoff is data. -/
theorem fourAmp_le_of_cutoff {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (k : Nat) (hk : fourAmpCutoff q ε ≤ k) :
    fourAmp q k ≤ ε := by
  have hCnum : 0 < Cfour.num := CReal.num_pos_of_pos Cfour_pos
  have hqq0 : (0 : Q') < q * q := HKPos.q_mul_pos hq0 hq0
  have hqq1 : q * q < (1 : Q') := qq_lt_one hq0 hq1
  have hCpos : (0 : Q') ≤ Cfour := Cfour_nonneg
  have hδpos : (0 : Q') < HKConv.divPos ε Cfour := HKConv.divPos_pos (CReal.num_pos_of_pos hε)
  have hCδ : (Cfour * HKConv.divPos ε Cfour) ≈ ε := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv Cfour (HKConv.divPos ε Cfour)) ?_
    exact HKConv.divPos_mul_eqv hCnum
  -- (q·q)^k ≤ δ for k ≥ cutoff (pow_base_antitone + pow_base_le_cutoff)
  have hpow : (q * q) ^ k ≤ HKConv.divPos ε Cfour := by
    refine Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hqq0) (Q'.le_of_lt hqq1) hk) ?_
    exact HKConvGen.pow_base_le_cutoff hqq0 hqq1 hδpos
  -- fourAmp q k ≤ Cfour·(q·q)^k ≤ Cfour·δ ≈ ε
  refine Q'.le_trans' _ _ _ (fourAmp_le_geo (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) k) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left ((q * q) ^ k) (HKConv.divPos ε Cfour) Cfour hpow hCpos) ?_
  exact Q'.le_of_eqv hCδ

/-! ## 5. The per-factor moduli as a bundle, and the sharp residual

The four per-factor facts proved above — `jDeriv_abs_le` (the `M_k`), `jFac_lb`
(denominator positivity), and `fourAmp_modulus` (the closed-form `N(ε)`) — are
exactly the per-factor analytic content the constructive route names.  We bundle
them as `PerFactorModuli` (the genuine, fully-proven data), and isolate the
remaining gap to `C1ToEquiv` as ONE sharply-named obligation. -/

/-- **The fully-proven per-factor analytic data** for the Jacobi theta family at a
fixed `q = a ∈ (0,1)`.  All three fields are discharged by the theorems above
(`fourAmp_modulus`, `jDeriv_abs_le`, `jFac_lb`); this records that the route's
per-factor moduli are GENUINELY built (not hypotheses). -/
structure PerFactorModuli (q : Q') : Type where
  /-- The uniform geometric cutoff `N(ε)` for the derivative majorant `fourAmp`. -/
  modulus : Q' → Nat
  /-- Past `modulus ε`, the per-factor derivative majorant is `≤ ε`. -/
  modulus_spec : ∀ ε : Q', (0 : Q') < ε → ∀ k : Nat, modulus ε ≤ k → fourAmp q k ≤ ε
  /-- The per-factor derivative magnitude bound `|f_k'(θ)| ≤ fourAmp q k` (`|s| ≤ 1`). -/
  deriv_bound : ∀ k : Nat, ∀ s : Q', (-1 : Q') ≤ s → s ≤ (1 : Q') →
    Q'.abs (jDeriv q k s) ≤ fourAmp q k
  /-- The denominator positivity `(1−q^{2k+1})² ≤ f_k(θ)` (`c ≥ −1`). -/
  denom_lb : ∀ k : Nat, ∀ c : Q', (-1 : Q') ≤ c →
    (1 + (-(amp q k))) * (1 + (-(amp q k))) ≤ jFac q k c

/-- **The per-factor moduli are genuinely constructed** for every `q ∈ (0,1)** —
the route's `M_k` / `N(ε)` / denominator-positivity data, all discharged. -/
def perFactorModuli {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    PerFactorModuli q where
  modulus ε := fourAmpCutoff q ε
  modulus_spec ε hε k hk := fourAmp_le_of_cutoff hq0 hq1 hε k hk
  deriv_bound k s hs1 hs2 := jDeriv_abs_le (Q'.le_of_lt hq0) k hs1 hs2
  denom_lb k c hc := jFac_lb (Q'.le_of_lt hq0) k hc

/-! ### The sharp residual to `DiffProduct.C1ToEquiv`

The per-factor moduli `perFactorModuli` are the genuine analytic content the route
names.  What is NOT done here is the FAMILY-LEVEL assembly: turning the per-factor
`PerFactorModuli` into a `DiffProduct.C1Inputs` for the SPECIFIC `dSeriesCReal` /
`Rhalf` truncation families (the equicontinuity `delStar`, the pointwise and
uniform `Mg`/`Nθ` moduli at the family level), together with the Gauss
derivative-value identification needed for the `bridge`.  We name that residual
sharply — it is exactly the data required to BUILD a `DiffProduct.C1ToEquiv`. -/

/-- **The sharp family-level residual (named, NOT discharged).**  Given the
genuine per-factor moduli (which `perFactorModuli` supplies), a
`ThetaFamilyAssembly` is precisely the remaining datum that produces a
`DiffProduct.C1ToEquiv (dSeriesCReal …) (Rhalf …)`: the assembly of the per-factor
`M_k`/`N(ε)`/denominator data into the family-level `C1Inputs` for the
theta-product truncations, plus the derivative-value `bridge`.  Stated as the
`C1ToEquiv` itself so that supplying it closes `DiffJTP` (hence `K_t ≥ 0`) via the
already-proven `JTPIdentity.Kt_geRat_zero_of_c1`.  It is the SOLE outstanding input;
the per-factor analytic content it rests on is fully proved above. -/
def ThetaFamilyAssembly {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type :=
  DiffProduct.C1ToEquiv
    (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
    (JTPIdentity.Rhalf ha0 ha1 hx hx1)

/-- **`ThetaFamilyAssembly → K_t ≥ 0`.**  Given the family-level assembly datum
(built ON the per-factor moduli proved here), the heat-kernel series
`K_t = dSeriesCReal ≥ 0`, unconditionally in the assembly.  This is the engine-routed
closure `JTPIdentity.Kt_geRat_zero_of_c1`, re-exposed through the per-factor module
to make explicit that the per-factor `M_k`/`N(ε)` content is the analytic substrate
the assembly consumes. -/
theorem Kt_geRat_zero_of_assembly {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : ThetaFamilyAssembly ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  JTPIdentity.Kt_geRat_zero_of_c1 ha0 ha1 hx hx1 H

end YMGap.Continuum.JTPInstance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega`/`pow`/`divPos` helpers).  No
`Classical.*`, no `native_decide`, no `sorry`.  `ThetaFamilyAssembly` is a named
`Type`-obligation (the sole outstanding input), NOT a `sorry`. -/

#print axioms YMGap.Continuum.JTPInstance.amp_le_even
#print axioms YMGap.Continuum.JTPInstance.even_pow_eqv
#print axioms YMGap.Continuum.JTPInstance.amp_sq_eqv
#print axioms YMGap.Continuum.JTPInstance.fourAmp_nonneg
#print axioms YMGap.Continuum.JTPInstance.jDeriv_abs_le
#print axioms YMGap.Continuum.JTPInstance.jFac_split_abs
#print axioms YMGap.Continuum.JTPInstance.jFac_split
#print axioms YMGap.Continuum.JTPInstance.jFac_lb
#print axioms YMGap.Continuum.JTPInstance.Cfour_mul_eqv
#print axioms YMGap.Continuum.JTPInstance.fourAmp_le_geo
#print axioms YMGap.Continuum.JTPInstance.qq_lt_one
#print axioms YMGap.Continuum.JTPInstance.fourAmp_le_of_cutoff
#print axioms YMGap.Continuum.JTPInstance.perFactorModuli
#print axioms YMGap.Continuum.JTPInstance.Kt_geRat_zero_of_assembly
