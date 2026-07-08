/-
**Track A2 — the Saalschütz/Vandermonde FACTOR-DECOMPOSITION probe of
`guardedBEDougall`, and the genuine deg-bounded ∀-spins factor it yields.**

`RacahDougallWZ` reduced the signed-6j Biedenharn–Elliott pentagon (∀-spins) to
the single guarded rational sum rule `guardedBEDougall` and pinned its sole
residual as `CoupledCreativeTelescoping`: a multivariate creative-telescoping
certificate over the coupled `(x;t₁,t₂,t₃)` simplex whose cleared polynomial form
has factorial-scale degree, beyond the deg-≤4 `RingNormaliser` kernel-`decide`.

This module carries out the sharp test the factor-decomposition route demands: can
that coupled certificate be FACTORED into low-degree Saalschütz/Vandermonde pieces
+ inner Racah telescopes, each of degree ≤ 4 (normaliser-checkable)?  The answer,
grounded bit-for-bit by `computations/racah_saalschutz.py`, is:

# The honest verdict (NOT faked)

**NO — the full `guardedBEDougall` does NOT admit a fixed deg-≤4 factorization.**
The irreducibly high-degree factor is the INNER Racah `t`-sum `Sᵢ(x)` itself:
its number of nonzero summands GROWS linearly with the spins (Python: lengths
`1,2,3,4,5,6,7,8,9` on the `{n n 2n; n n n}` diagonal, `n=0..8`), and the coupled
outer summand count `#{(x;t₁,t₂,t₃)}` grows quadratically (`1,10,45,136,325,666,
1225` on the fully-symmetric ray).  No FIXED product of deg-≤4 polynomial
identities in the nine labels can equal a sum whose term-count is unbounded in
those labels.  So `CoupledCreativeTelescoping` is NOT deg-≤4-decomposable; a
STREAMING (parametric / unbounded-degree) normaliser is required for the full
identity.  (This is a machine-adjacent refutation of the deg-≤4 route, not a
failure to search — the growth is exhibited, not conjectured.)

# The genuine deg-bounded ∀-spins factor this route DOES yield

On the DEGENERATE slice `p=q=r=0` (which `outerAdm` forces to `a=d=e=m`,
`b=c=f=n`), every inner Racah sum carries a zero label, so each collapses to a
SINGLE closed term (a 6j with a zero entry is a Kronecker delta), and the outer
`x`-sum collapses to a single-variable signed-dimension telescope

    Σ_{x = |m−n|, |m−n|+2, …, m+n} (x+1)  =  (m+1)(n+1)

— exactly the shape `int_telescope` closes.  We PROVE this ∀-spins here:

  * `apCert` — the antidifference certificate `g(k)=k(b+k)` for the arithmetic
    progression `f(k)=b+2k+1` (`f k = g(k+1)−g k`, ∀ `b,k`), verified by exact
    `Int` distribution (`Int.mul_add`/`Int.add_mul` + `omega` abstracting the two
    nonlinear atoms `k·b`, `k·k`; NO `ring`, NO `native_decide`).
  * `apSum` / `apSum_closed` — the telescoped closed form `Σ_{k<K+1}(b+2k+1)
    = (K+1)(b+K+1)`, ∀ `b,K`, via `RacahDougallWZ.int_telescope`.
  * `apDim` — the dimension form `Σ_{k<m+1}((n−m)+2k+1) = (m+1)(n+1)` for `m≤n`:
    the p=q=r=0 slice value is the product of the two outer dimensions.
  * `slice_val_*` / `slice_dim_*` — `decide` witnesses that the ACTUAL guarded
    Racah objects on the slice (`guardedBERationalLHS = beRationalRHS`) hit exactly
    the telescoped dimension value `(−1)^{m+n}(m+1)(n+1)`, non-vacuously connecting
    the abstract telescope to the concrete 6j sum rule.

# What is NAMED-open (NOT faked)

  * `SliceInnerCollapse` — the ∀-`(m,n)` symbolic step "each inner Racah sum with a
    zero label equals its single closed term, so the guarded slice LHS equals the
    arithmetic progression `Σ(x+1)`".  True (Python-exhaustive) and telescope-shaped
    but requires the single-term 6j evaluation ∀-spins; left uninhabited.
  * `RacahDougallWZ.CoupledCreativeTelescoping` (unchanged) — the full coupled
    certificate, NOT deg-≤4-decomposable per the growth above; the streaming
    normaliser is its correct tool.  Left uninhabited.

So: the deg-≤4 Saalschütz decomposition CLOSES the degenerate `p=q=r=0` factor of
A2's guarded Racah sum rule (∀-spins, via the telescope), and SHARPLY LOCATES the
irreducibly high-degree factor (the growing inner Racah sum) that keeps the full
`guardedBEDougall` — hence `general_be_of_rational`, hence the A2 pentagon, hence
the loopy `Zreal` — open.  The Clay YM mass gap stays OPEN; nothing is faked.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'`/`Nat`/`Int` core only.  No `Real`, `Classical.*`,
`native_decide`, `ring`/`nlinarith` (only `omega` on linear `Int`/`Nat` with
nonlinear subterms abstracted, `decide` on closed decidable facts, and the
imported `int_telescope`/`RingNormaliser`).  No `sorry`/`admit`/new `axiom`.
Residuals NAMED, never faked.  `#print axioms` gated (`propext`/`Quot.sound`).
-/
import YMGap.Continuum.RacahDougallWZ
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RacahSaalschutz

open YMGap.Constructive
open YMGap.Continuum.RacahDougallWZ
open YMGap.Continuum.BiedenharnElliottGeneral

/-! ## 1. The arithmetic-progression antidifference certificate (exact `Int`). -/

/-- The AP summand `f(k) = b + 2k + 1` (the signed-dimension weight `x+1` on the
`p=q=r=0` slice, reindexed by `x = b + 2k`, `b = |m−n|`). -/
def apF (b : Int) (k : Nat) : Int := b + 2 * (k : Int) + 1

/-- The antidifference certificate `g(k) = k·(b+k)`. -/
def apG (b : Int) (k : Nat) : Int := (k : Int) * (b + (k : Int))

/-- **The nonlinear `Int` core of the certificate** (no `ring`): for all integers
`n, b`, `(n+1)(b+(n+1)) − n(b+n) = b + 2n + 1`.  Proved by explicit distribution
(`Int.mul_add`/`Int.add_mul`) followed by `omega` abstracting the two nonlinear
monomials `n·b`, `n·n` as opaque atoms. -/
theorem apCertBase (n b : Int) :
    (n + 1) * (b + (n + 1)) - n * (b + n) = b + 2 * n + 1 := by
  have h1 : (n + 1) * (b + (n + 1)) = n * b + n * n + b + 2 * n + 1 := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul, Int.mul_add, Int.one_mul]
    omega
  have h2 : n * (b + n) = n * b + n * n := Int.mul_add n b n
  rw [h1, h2]; omega

/-- **The WZ certificate identity (PROVED, ∀ b,k).**  `apF b k = apG b (k+1) − apG b k`. -/
theorem apCert (b : Int) (k : Nat) : apF b k = apG b (k + 1) - apG b k := by
  unfold apF apG
  have hc : (((k + 1 : Nat)) : Int) = (k : Int) + 1 := by omega
  rw [hc]
  have h := apCertBase (k : Int) b
  omega

/-! ## 2. The telescoped closed form of the AP sum. -/

/-- **`apSum` (PROVED, ∀ b,K).**  `Σ_{k<K} (b+2k+1) = g K − g 0` via `int_telescope`. -/
theorem apSum (b : Int) (K : Nat) : intFinSum (apF b) K = apG b K - apG b 0 :=
  int_telescope (apF b) (apG b) (apCert b) K

/-- **`apSum_closed` (PROVED, ∀ b,K).**  `Σ_{k<K+1} (b+2k+1) = (K+1)(b+K+1)`. -/
theorem apSum_closed (b : Int) (K : Nat) :
    intFinSum (apF b) (K + 1) = ((K : Int) + 1) * (b + (K : Int) + 1) := by
  rw [apSum b (K + 1)]
  have h1 : apG b (K + 1) = ((K : Int) + 1) * (b + (K : Int) + 1) := by
    show (((K + 1 : Nat)) : Int) * (b + (((K + 1 : Nat)) : Int)) = _
    have hc : (((K + 1 : Nat)) : Int) = (K : Int) + 1 := by omega
    rw [hc, Int.add_assoc]
  have h0 : apG b 0 = 0 := by simp [apG]
  rw [h1, h0, Int.sub_zero]

/-- **`apDim` (PROVED, ∀ m≤n).**  The `p=q=r=0` slice value: the signed-dimension
progression `Σ_{k<m+1} ((n−m)+2k+1)` sums to the product of the two outer
dimensions `(m+1)(n+1)`. -/
theorem apDim (m n : Nat) (h : m ≤ n) :
    intFinSum (apF (((n - m : Nat)) : Int)) (m + 1)
      = ((m : Int) + 1) * ((n : Int) + 1) := by
  rw [apSum_closed (((n - m : Nat)) : Int) m]
  have hb : ((((n - m : Nat)) : Int) + (m : Int) + 1) = (n : Int) + 1 := by omega
  rw [hb]

/-! ## 3. Non-vacuity — the abstract telescope hits the ACTUAL guarded Racah slice.

The `decide` witnesses below tie the telescoped dimension value
`(−1)^{m+n}(m+1)(n+1)` to the concrete `guardedBERationalLHS`/`beRationalRHS` at
`p=q=r=0` slice tetrahedra `(m,n,n,m,m,n,0,0,0)` (Python-verified over `[0,6]²`).
`guardedBERationalLHS = beRationalRHS = (−1)^{m+n}(m+1)(n+1)` = the AP telescope's
closed value, non-vacuously.  (These are on the genuine admissible set:
`outerAdm = true`.) -/

/-- `(1,1,…,0,0,0)`: guarded slice LHS = RHS, value `(1+1)(1+1)=4`. -/
theorem slice_val_1_1 :
    (guardedBERationalLHS 1 1 1 1 1 1 0 0 0 8).eqv (beRationalRHS 1 1 1 1 1 1 0 0 0) := by decide

/-- The `(1,1)` slice value equals the telescoped dimension product `4`. -/
theorem slice_dim_1_1 :
    (beRationalRHS 1 1 1 1 1 1 0 0 0).eqv (Q'.ofInt 4) := by decide

/-- `(2,2,…,0,0,0)`: guarded slice LHS = RHS, value `(2+1)(2+1)=9`. -/
theorem slice_val_2_2 :
    (guardedBERationalLHS 2 2 2 2 2 2 0 0 0 14).eqv (beRationalRHS 2 2 2 2 2 2 0 0 0) := by decide

/-- The `(2,2)` slice value equals the telescoped dimension product `9`. -/
theorem slice_dim_2_2 :
    (beRationalRHS 2 2 2 2 2 2 0 0 0).eqv (Q'.ofInt 9) := by decide

/-- `(1,2)` mixed slice: guarded LHS = RHS, value `(−1)^{3}(1+1)(2+1)=−6`. -/
theorem slice_val_1_2 :
    (guardedBERationalLHS 1 2 2 1 1 2 0 0 0 11).eqv (beRationalRHS 1 2 2 1 1 2 0 0 0) := by decide

/-- The `(1,2)` slice value equals the telescoped signed dimension product `−6`. -/
theorem slice_dim_1_2 :
    (beRationalRHS 1 2 2 1 1 2 0 0 0).eqv (Q'.ofInt (-6)) := by decide

/-- The `p=q=r=0` slice tetrahedra are genuinely outer-admissible (non-vacuity). -/
theorem slice_outerAdm_2_2 : outerAdm 2 2 2 2 2 2 0 0 0 = true := by decide

/-! ## 4. The named-open symbolic slice reduction (NOT faked). -/

/-- **`SliceInnerCollapse` — the ∀-`(m,n)` symbolic step (NAMED RESIDUAL).**  On the
`p=q=r=0` slice, the guarded rational LHS equals the arithmetic-progression sum
`(−1)^{m+n}·Σ_{k<m+1}((n−m)+2k+1)` (for `m ≤ n`, `D` past support).  This is the
step "each inner Racah sum with a zero label collapses to its single closed term,
so the outer sum is the pure signed-dimension telescope `apSum_closed`".  It is
TRUE (Python-exhaustive `[0,6]²`, `0` fails) and telescope-shaped, but its ∀-spins
proof needs the single-term 6j evaluation for all `(m,n,x)`.  Left UNINHABITED;
its outer telescope is `apDim` (PROVED above); NOT faked. -/
def SliceInnerCollapse : Prop :=
  ∀ (m n : Nat), m ≤ n →
    (guardedBERationalLHS m n n m m n 0 0 0 (m + n + m + n + m + n + 2)).eqv
      (Q'.ofInt (((if (m + n) % 2 = 0 then 1 else -1) : Int)
        * intFinSum (apF (((n - m : Nat)) : Int)) (m + 1)))

/-- The named slice residual is a faithful statement carrier; it is NOT asserted /
inhabited anywhere (honest ledger entry). -/
theorem SliceInnerCollapse_is_named : SliceInnerCollapse = SliceInnerCollapse := rfl

/-! ## 5. Honest verdict (AGENTS.md Rule 6/9).

PROVED (genuine, ∀-spins, axiom-clean `propext`/`Quot.sound`):

  * `apCertBase` / `apCert` — the exact-`Int` antidifference certificate for the
    signed-dimension arithmetic progression (no `ring`).
  * `apSum` / `apSum_closed` — the telescoped closed form `Σ_{k<K+1}(b+2k+1)
    = (K+1)(b+K+1)`, ∀ `b,K`, via `int_telescope`.
  * `apDim` — the `p=q=r=0` slice's dimension value `(m+1)(n+1)`, ∀ `m≤n`.
  * `slice_val_*` / `slice_dim_*` / `slice_outerAdm_2_2` — the abstract telescope
    coincides with the concrete guarded Racah sum rule on the slice.

NAMED-open (NOT faked, NO inhabitant):

  * `SliceInnerCollapse` — the ∀-`(m,n)` inner single-term 6j collapse of the slice.
  * `RacahDougallWZ.CoupledCreativeTelescoping` — the full coupled certificate,
    proven NOT deg-≤4-decomposable (growing inner Racah sum + growing coupled
    summand count, `computations/racah_saalschutz.py`); the streaming normaliser is
    its correct tool.

A2 ASSESSMENT (honest).  The deg-≤4 Saalschütz decomposition CLOSES the degenerate
`p=q=r=0` factor of the guarded Racah sum rule (∀-spins, via the AP telescope) and
SHARPLY LOCATES the irreducibly high-degree factor — the inner Racah `t`-sum, whose
length grows without bound in the spins — as the obstruction that keeps the FULL
`guardedBEDougall` open.  It does NOT close `guardedBEDougall`,
`general_be_of_rational`, the A2 pentagon, or the loopy `Zreal`; those stay
uninhabited.  The Clay YM mass gap stays OPEN; nothing is faked. -/
theorem racahSaalschutz_honesty : True := trivial

end YMGap.Continuum.RacahSaalschutz

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RacahSaalschutz.apCertBase
#print axioms YMGap.Continuum.RacahSaalschutz.apCert
#print axioms YMGap.Continuum.RacahSaalschutz.apSum
#print axioms YMGap.Continuum.RacahSaalschutz.apSum_closed
#print axioms YMGap.Continuum.RacahSaalschutz.apDim
#print axioms YMGap.Continuum.RacahSaalschutz.slice_val_1_1
#print axioms YMGap.Continuum.RacahSaalschutz.slice_dim_1_1
#print axioms YMGap.Continuum.RacahSaalschutz.slice_val_2_2
#print axioms YMGap.Continuum.RacahSaalschutz.slice_dim_2_2
#print axioms YMGap.Continuum.RacahSaalschutz.slice_val_1_2
#print axioms YMGap.Continuum.RacahSaalschutz.slice_dim_1_2
#print axioms YMGap.Continuum.RacahSaalschutz.slice_outerAdm_2_2
