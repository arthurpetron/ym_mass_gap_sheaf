/-
Track B / R2 — LAYER 1 of the `(r,d)` theta-asymptotics build: two-sided DISCRETE
bounds for the TAIL Gaussian-theta sums

    Rsum_m(K)  :=  ∑_{r ≥ K}  r^m · σ^{r²}        (m ∈ {0, 2},   σ ∈ (0,1)).

# Why this module exists — the `R_m` tail side of the self-fusion factorization

The `p = 2` SU(2) self-fusion coefficient factorizes (the `(r,d)` diagonalization)
into one-dimensional incomplete-theta sums `R_m(k) = ∑_r r^m σ^{r²}` and `D_m(k)`,
with `σ = √w` (`σ^{r²} = w^{r²/2}`).  The genuine open frontier (the sharp discrete
local CLT, DOM/DER) consumes two-sided control of these sums.  This module builds
the REUSABLE Gaussian-theta-tail infrastructure for the `R_m` side: the tail sum
`∑_{r ≥ K} r^m σ^{r²}`, its positivity, a clean GEOMETRIC/dyadic UPPER bound, a
first-block LOWER bound, and the single-term head increment.

# The `Q'`-level model (clean, half-integer-free)

`σ^{r²} = w^{r²/2}` carries a half-integer exponent when `r` is odd.  We avoid the
`/2` entirely by carrying `σ` itself as the rational base `σ : Q'`, `0 < σ ≤ 1`
(the caller instantiates `σ = √w` and lifts to the `CReal` `cpow σ` when the
CReal form is needed).  Then `σ^{r²} = qpow σ (r·r)` is a clean `Nat`-exponent
`Q'` power.  The term is `r^m · σ^{r²} = ofNat(r^m)·qpow σ (r·r)`, summed over a
window `M` starting at the cutoff `K`.

# THE LEADING τ-SCALING (documented, the bound shapes match it)

With `σ = w^{1/2} = e^{−τ/2}` (`τ = −log w`), `σ^{r²} = e^{−τ r²/2}` is a Gaussian
of width `r ≍ τ^{−1/2}`.  The full (untruncated, `K = 0`) sum scales as

    ∑_{r ≥ 0} r^m σ^{r²}  ≍  τ^{−(m+1)/2}·(Gamma factor),

and the TAIL past `K` carries the cutoff Gaussian factor `σ^{K²} = e^{−τ K²/2}`:

    Rsum_m(K)  ≍  C_m · σ^{K²} · τ^{−(m+1)/2}      (for `K ≲ τ^{−1/2}`, the active
                                                    scale; smaller for `K ≫ τ^{−1/2}`).

The bounds proved here have exactly this shape: the UPPER bound is
`2·K^m·σ^{K²}` (leading factor `σ^{K²}`, constant `2` once the cutoff
`2^m·σ^{2K+1} ≤ 1/2` fires — the discrete analogue of "past the Gaussian width"),
and the LOWER bound keeps the leading head term `K^m·σ^{K²}`.

# What is PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

  * `thetaTailTerm` / `thetaTailSum` — the tail term `r^m σ^{r²}` and its windowed
    `Q'` finite sum, with nonnegativity (`thetaTailSum_nonneg`).
  * `thetaTail_succ` — the window extends by one term:
    `thetaTailSum σ m K (M+1) = thetaTailSum σ m K M + (K+M)^m σ^{(K+M)²}`.
  * `thetaTail_head_drop` — THE SINGLE-TERM HEAD INCREMENT (the Layer-2 lever):
    `thetaTailSum σ m K (M+1) = K^m σ^{K²} + thetaTailSum σ m (K+1) M`, i.e.
    dropping the `r = K` term shifts the cutoff to `K+1`.  A clean exact equality.
  * `thetaTailTerm_ratio` — the successive-term ratio bound
    `term(K, j+1) ≤ (2^m·σ^{2K+1})·term(K, j)` (polynomial `((r+1)/r)^m ≤ 2^m`
    beaten by the Gaussian gain `σ^{2r+1} ≤ σ^{2K+1}`).
  * `thetaTail_le` — THE GEOMETRIC UPPER BOUND.  Under the cutoff
    `2^m·σ^{2K+1} ≤ 1/2`, for every window `M`:
        Rsum_m(K) ≤ 2 · ofNat(K^m) · qpow σ (K·K)   =   2·K^m·σ^{K²}.
    Explicit constant `C_m = 2`; leading factor `σ^{K²}`.
  * `thetaTail_ge` — THE FIRST-BLOCK LOWER BOUND.  For any nonempty window
    (`M ≥ 1`):  Rsum_m(K) ≥ ofNat(K^m)·qpow σ (K·K) = K^m·σ^{K²}.  The leading
    head term is kept; the τ-scaling order `τ^{−(m+1)/2}` is obtained by the caller
    summing such head blocks across the active scale `K ≲ τ^{−1/2}`.

# Honest verdict and scope (AGENTS.md Rule 6)

This is LAYER-1 reusable Gaussian-theta-tail infrastructure (the `R_m` tail side):
the windowed tail sum, its positivity, the single-term head increment, a geometric
UPPER bound `≤ 2·K^m·σ^{K²}` (under an explicit `Q'` cutoff), and a first-block
LOWER bound `≥ K^m·σ^{K²}`.  The leading τ-scaling `Rsum_m(K) ≍ C_m·σ^{K²}·
τ^{−(m+1)/2}` is documented and the bound shapes match it.  This is NOT the
DOM/DER discrete local CLT (Layer 2 — the consecutive-mode ratio and the parity
interleaving — and Layer 3 — the DOM/DER assembly — are downstream), and it is NOT
a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, `omega` on `Nat` identities, reused `Q'` order and
`qpow`/`finSum`/geometric-closure lemmas.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.PartitionUpperBound

namespace YMGap.Continuum.RDThetaTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.PartitionUpperBound

/-! ## 0. A local `finSum` nonnegativity helper -/

/-- `0 ≤ finSum f n` when every term is nonnegative (local copy; structural
induction on `n`). -/
theorem finSum_nonneg {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ RationalTail.finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ RationalTail.finSum f n + f n
      have h1 := finSum_nonneg hf n
      exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ h1 (hf n)) (Q'.le_refl' _)

/-! ## 1. The tail theta term and its windowed sum -/

/-- **The tail theta term** `r^m · σ^{r²}` at `r = K + j`, as a `Q'`:
`ofNat((K+j)^m) · qpow σ ((K+j)·(K+j))`.  (`σ^{r²} = qpow σ (r·r)`, the clean
`Nat`-exponent `Q'` power of the rational base `σ ∈ (0,1)`.) -/
def thetaTailTerm (σ : Q') (m K j : Nat) : Q' :=
  Q'.ofNat ((K + j) ^ m) * qpow σ ((K + j) * (K + j))

/-- The tail theta term is nonnegative on `0 ≤ σ`. -/
theorem thetaTailTerm_nonneg {σ : Q'} (hσ : (0 : Q') ≤ σ) (m K j : Nat) :
    (0 : Q') ≤ thetaTailTerm σ m K j :=
  Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg σ hσ _)

/-- **The windowed tail theta sum** `Rsum_m(K)` (truncated to a window of `M`
terms starting at the cutoff `K`):

    thetaTailSum σ m K M  =  ∑_{j < M} (K+j)^m · σ^{(K+j)²}  =  ∑_{r = K}^{K+M−1} r^m σ^{r²}.

The full tail `∑_{r ≥ K}` is its `M → ∞` limit, accessed through `thetaTail_le`
(which is uniform in `M`). -/
def thetaTailSum (σ : Q') (m K : Nat) : Nat → Q' :=
  fun M => RationalTail.finSum (fun j => thetaTailTerm σ m K j) M

/-- The tail theta sum is nonnegative on `0 ≤ σ`. -/
theorem thetaTailSum_nonneg {σ : Q'} (hσ : (0 : Q') ≤ σ) (m K M : Nat) :
    (0 : Q') ≤ thetaTailSum σ m K M :=
  finSum_nonneg (fun j => thetaTailTerm_nonneg hσ m K j) M

/-! ## 2. The window-extension and single-term head-drop increments

`thetaTail_succ` is the bare `finSum` recurrence (append the next term).  The
genuinely useful Layer-2 lever is `thetaTail_head_drop`: dropping the leading
`r = K` term turns the window into the window at cutoff `K+1` — i.e. the single
extra term separating `Rsum_m(K)` from `Rsum_m(K+1)` is `K^m σ^{K²}`. -/

/-- **Window extension (the `finSum` recurrence).**
`thetaTailSum σ m K (M+1) = thetaTailSum σ m K M + (K+M)^m σ^{(K+M)²}`. -/
theorem thetaTail_succ (σ : Q') (m K M : Nat) :
    thetaTailSum σ m K (M + 1)
      = thetaTailSum σ m K M + thetaTailTerm σ m K M := rfl

/-- **The leading term shifts the cutoff** (the Nat-index reindex):
`thetaTailTerm σ m K (j+1) = thetaTailTerm σ m (K+1) j`, since both name the term
at absolute index `r = K + 1 + j`. -/
theorem thetaTailTerm_shift (σ : Q') (m K j : Nat) :
    thetaTailTerm σ m K (j + 1) = thetaTailTerm σ m (K + 1) j := by
  show Q'.ofNat ((K + (j + 1)) ^ m) * qpow σ ((K + (j + 1)) * (K + (j + 1)))
      = Q'.ofNat (((K + 1) + j) ^ m) * qpow σ (((K + 1) + j) * ((K + 1) + j))
  have h : K + (j + 1) = (K + 1) + j := by omega
  rw [h]

/-- **THE SINGLE-TERM HEAD-DROP INCREMENT (the Layer-2 lever).**  Dropping the
leading `r = K` term shifts the cutoff to `K + 1`:

    thetaTailSum σ m K (M+1)  =  K^m·σ^{K²}  +  thetaTailSum σ m (K+1) M.

Equivalently `Rsum_m(K) − Rsum_m(K+1) = K^m σ^{K²}` (the single clean term
separating consecutive cutoffs).  PROOF: peel the first summand of the `finSum`
(`finSum_peel_first`-style induction), then reindex the tail by
`thetaTailTerm_shift`. -/
theorem thetaTail_head_drop (σ : Q') (m K : Nat) :
    ∀ M, (thetaTailSum σ m K (M + 1)).eqv
      (thetaTailTerm σ m K 0 + thetaTailSum σ m (K + 1) M)
  | 0 => by
      -- LHS = finSum _ 1 = 0 + term(K,0) ; RHS = term(K,0) + finSum _ 0 = term(K,0) + 0
      show (RationalTail.finSum (fun j => thetaTailTerm σ m K j) 1).eqv
        (thetaTailTerm σ m K 0
          + RationalTail.finSum (fun j => thetaTailTerm σ m (K + 1) j) 0)
      show ((0 : Q') + thetaTailTerm σ m K 0).eqv
        (thetaTailTerm σ m K 0 + (0 : Q'))
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _).symm
  | M + 1 => by
      -- thetaTailSum σ m K (M+2) = thetaTailSum σ m K (M+1) + term(K, M+1)
      show (RationalTail.finSum (fun j => thetaTailTerm σ m K j) (M + 1)
            + thetaTailTerm σ m K (M + 1)).eqv
        (thetaTailTerm σ m K 0
          + (RationalTail.finSum (fun j => thetaTailTerm σ m (K + 1) j) M
              + thetaTailTerm σ m (K + 1) M))
      -- IH on the left prefix
      have ih := thetaTail_head_drop σ m K M
      -- term(K, M+1) = term(K+1, M)
      have hshift : thetaTailTerm σ m K (M + 1) = thetaTailTerm σ m (K + 1) M :=
        thetaTailTerm_shift σ m K M
      rw [hshift]
      -- (P + t) where P ≃ term(K,0) + Q :  ≃ (term(K,0)+Q) + t ≃ term(K,0) + (Q + t)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (thetaTailTerm σ m (K + 1) M) ih) ?_
      exact Q'.add_assoc_eqv (thetaTailTerm σ m K 0)
        (RationalTail.finSum (fun j => thetaTailTerm σ m (K + 1) j) M)
        (thetaTailTerm σ m (K + 1) M)

/-! ## 3. The successive-term ratio bound (the engine of the UPPER bound)

The Gaussian exponent jumps `r² → (r+1)² = r² + (2r+1)`, so the per-term gain is
`σ^{2r+1} ≤ σ^{2K+1}` (past the cutoff `r ≥ K`, `σ ≤ 1`).  The polynomial ratio is
`(r+1)^m ≤ 2^m·r^m` (from `r+1 ≤ 2r` for `r ≥ 1`).  Hence the ratio is
`≤ 2^m·σ^{2K+1}`.  We work in window coordinates `r = K + j`, so the cutoff `K ≥ 1`
is needed only for `m ≥ 1` (the `r+1 ≤ 2r` step); we require `1 ≤ K` to keep the
statement uniform in `m`. -/

/-- The Gaussian exponent increment `(r+1)² = r² + (2r+1)` (Nat). -/
theorem sq_succ (r : Nat) : (r + 1) * (r + 1) = r * r + (2 * r + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega

/-- The polynomial-ratio Nat bound `(r+1)^m ≤ 2^m·r^m` for `r ≥ 1` (from
`r + 1 ≤ 2·r`). -/
theorem polyRatio_succ_nat (m : Nat) {r : Nat} (hr : 1 ≤ r) :
    (r + 1) ^ m ≤ 2 ^ m * r ^ m := by
  calc (r + 1) ^ m
      ≤ (2 * r) ^ m := Nat.pow_le_pow_left (by omega) m
    _ = 2 ^ m * r ^ m := by rw [Nat.mul_pow]

/-- **THE SUCCESSIVE-TERM RATIO BOUND (the engine).**  On `0 ≤ σ ≤ 1` with `1 ≤ K`,
for every window offset `j`:

    thetaTailTerm σ m K (j+1)  ≤  (2^m · σ^{2K+1}) · thetaTailTerm σ m K j.

PROOF.  With `r = K + j ≥ K ≥ 1`: the term at `j+1` is `(r+1)^m·σ^{r²+(2r+1)}`
(`sq_succ`, `qpow_add`); bound the polynomial part by `2^m·r^m` (`polyRatio_succ_nat`)
and the Gaussian gain `σ^{2r+1} ≤ σ^{2K+1}` (`qpow_antitone`, `2K+1 ≤ 2r+1`);
regroup into `(2^m·σ^{2K+1})·(r^m·σ^{r²})`. -/
theorem thetaTailTerm_ratio {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (m K : Nat) (hK : 1 ≤ K) (j : Nat) :
    thetaTailTerm σ m K (j + 1)
      ≤ (Q'.ofNat (2 ^ m) * qpow σ (2 * K + 1)) * thetaTailTerm σ m K j := by
  -- write r = K + j (kept explicit; no `set`)
  have hr1 : 1 ≤ K + j := by omega
  have hKj : K ≤ K + j := by omega
  -- target index K + (j+1) = (K+j) + 1
  have hidx : K + (j + 1) = (K + j) + 1 := by omega
  show Q'.ofNat ((K + (j + 1)) ^ m) * qpow σ ((K + (j + 1)) * (K + (j + 1)))
      ≤ (Q'.ofNat (2 ^ m) * qpow σ (2 * K + 1))
        * (Q'.ofNat ((K + j) ^ m) * qpow σ ((K + j) * (K + j)))
  rw [hidx]
  -- (r+1)² = r² + (2r+1)
  rw [sq_succ (K + j)]
  -- introduce the local name r := K + j for the rest of the proof
  generalize hr : K + j = r at hr1 hKj ⊢
  have hKr : K ≤ r := hKj
  -- σ^{r²+(2r+1)} ≃ σ^{r²}·σ^{2r+1}
  have hsplit : (qpow σ (r * r + (2 * r + 1))).eqv (qpow σ (r * r) * qpow σ (2 * r + 1)) :=
    qpow_add σ (r * r) (2 * r + 1)
  -- polynomial ratio (r+1)^m ≤ 2^m·r^m  (as Q')
  have hpoly : Q'.ofNat ((r + 1) ^ m) ≤ Q'.ofNat (2 ^ m) * Q'.ofNat (r ^ m) := by
    have hnat : (r + 1) ^ m ≤ 2 ^ m * r ^ m := polyRatio_succ_nat m hr1
    refine Q'.le_trans' _ _ _ (BondMovingMoment.ofNat_le_ofNat hnat) (Q'.le_of_eqv ?_)
    exact ofNat_mul_eqv (2 ^ m) (r ^ m)
  -- Gaussian gain σ^{2r+1} ≤ σ^{2K+1}  (2K+1 ≤ 2r+1 since K ≤ r)
  have hgain : qpow σ (2 * r + 1) ≤ qpow σ (2 * K + 1) :=
    qpow_antitone hσ0 hσ1 (2 * K + 1) (2 * r + 1) (by omega)
  -- LHS ≃ (r+1)^m · (σ^{r²}·σ^{2r+1})
  have hLeq : (Q'.ofNat ((r + 1) ^ m) * qpow σ (r * r + (2 * r + 1))).eqv
      (Q'.ofNat ((r + 1) ^ m) * (qpow σ (r * r) * qpow σ (2 * r + 1))) :=
    Q'.mul_eqv_congr_left _ _ _ hsplit
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq) ?_
  -- bound polynomial factor: ≤ (2^m·r^m)·(σ^{r²}·σ^{2r+1})
  have hgnn : (0 : Q') ≤ qpow σ (r * r) * qpow σ (2 * r + 1) :=
    Q'.mul_nonneg _ _ (qpow_nonneg σ hσ0 _) (qpow_nonneg σ hσ0 _)
  have hB1 : Q'.ofNat ((r + 1) ^ m) * (qpow σ (r * r) * qpow σ (2 * r + 1))
      ≤ (Q'.ofNat (2 ^ m) * Q'.ofNat (r ^ m)) * (qpow σ (r * r) * qpow σ (2 * r + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hgnn
  refine Q'.le_trans' _ _ _ hB1 ?_
  -- bound the gain σ^{2r+1} ≤ σ^{2K+1} inside the right factor
  have hcoefnn : (0 : Q') ≤ Q'.ofNat (2 ^ m) * Q'.ofNat (r ^ m) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
  have hrrnn : (0 : Q') ≤ qpow σ (r * r) := qpow_nonneg σ hσ0 _
  have hB2 : (Q'.ofNat (2 ^ m) * Q'.ofNat (r ^ m)) * (qpow σ (r * r) * qpow σ (2 * r + 1))
      ≤ (Q'.ofNat (2 ^ m) * Q'.ofNat (r ^ m)) * (qpow σ (r * r) * qpow σ (2 * K + 1)) := by
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hcoefnn
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hgain hrrnn
  refine Q'.le_trans' _ _ _ hB2 ?_
  -- regroup: (2^m·r^m)·(σ^{r²}·σ^{2K+1}) ≃ (2^m·σ^{2K+1})·(r^m·σ^{r²})
  -- A=2^m, B=r^m, C=σ^{r²}, D=σ^{2K+1}: (A·B)·(C·D) ≃ (A·D)·(B·C).
  exact Q'.le_of_eqv (mul_four_swap (Q'.ofNat (2 ^ m)) (Q'.ofNat (r ^ m))
    (qpow σ (r * r)) (qpow σ (2 * K + 1)))

/-! ## 4. THE GEOMETRIC UPPER BOUND `Rsum_m(K) ≤ 2·K^m·σ^{K²}`

Under the explicit cutoff `2^m·σ^{2K+1} ≤ 1/2` (the discrete "past the Gaussian
width" condition `K ≳ √(1/τ)`), the successive-term ratio is `≤ 1/2`, so the
windowed tail sums under `H = 2·(head)`, uniformly in `M`. -/

/-- **THE GEOMETRIC UPPER BOUND.**  Fix `0 ≤ σ ≤ 1`, `1 ≤ K`, and suppose the
explicit cutoff inequality

    cutoff:   2^m · σ^{2K+1}  ≤  1/2

holds.  Then for every window length `M`:

    Rsum_m(K)  =  thetaTailSum σ m K M  ≤  2 · ofNat(K^m) · qpow σ (K·K)
                                        =  2 · K^m · σ^{K²}.

Explicit constant `C_m = 2`; leading factor `σ^{K²} = e^{−τ K²/2}` (the cutoff
Gaussian factor of the τ-scaling `Rsum_m(K) ≍ C_m·σ^{K²}·τ^{−(m+1)/2}`).

PROOF.  The window sequence `f j = thetaTailTerm σ m K j` has head
`f 0 = K^m·σ^{K²}`, successive-term ratio `≤ 2^m·σ^{2K+1} ≤ 1/2`
(`thetaTailTerm_ratio` + cutoff), and `H = 2·f0` satisfies the geometric
recurrence `f0 + (1/2)·H = f0 + f0 = H`; `CharacterTail.geom_series_le` then sums
every window under `H`. -/
theorem thetaTail_le {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (m K : Nat) (hK : 1 ≤ K)
    (hcut : Q'.ofNat (2 ^ m) * qpow σ (2 * K + 1) ≤ HalfPow.half) :
    ∀ M, thetaTailSum σ m K M
      ≤ Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K)) := by
  intro M
  -- the window sequence  f j = thetaTailTerm σ m K j  (kept explicit, no `set`),
  -- head value  f0 = K^m·σ^{K²},  closure target  H = 2·f0.
  -- head f0 = K^m·σ^{K²}  (K + 0 = K)
  have hf0term : thetaTailTerm σ m K 0 = Q'.ofNat (K ^ m) * qpow σ (K * K) := by
    show Q'.ofNat ((K + 0) ^ m) * qpow σ ((K + 0) * (K + 0))
        = Q'.ofNat (K ^ m) * qpow σ (K * K)
    rw [Nat.add_zero]
  have hf0nn : (0 : Q') ≤ Q'.ofNat (K ^ m) * qpow σ (K * K) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg σ hσ0 _)
  -- ratio domination: f(j+1) ≤ (1/2)·f(j)
  have hdom : ∀ j, thetaTailTerm σ m K (j + 1)
      ≤ HalfPow.half * thetaTailTerm σ m K j := by
    intro j
    have hr := thetaTailTerm_ratio hσ0 hσ1 m K hK j
    have hfjnn : (0 : Q') ≤ thetaTailTerm σ m K j := thetaTailTerm_nonneg hσ0 m K j
    have hstep : (Q'.ofNat (2 ^ m) * qpow σ (2 * K + 1)) * thetaTailTerm σ m K j
        ≤ HalfPow.half * thetaTailTerm σ m K j :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcut hfjnn
    exact Q'.le_trans' _ _ _ hr hstep
  -- head bound f 0 ≤ f0
  have hf0le : thetaTailTerm σ m K 0 ≤ Q'.ofNat (K ^ m) * qpow σ (K * K) :=
    Q'.le_of_eqv (Q'.eqv_of_eq hf0term)
  -- H = 2·f0 ; recurrence f0 + (1/2)·H ≤ H
  have hHnn : (0 : Q') ≤ Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K)) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 2) hf0nn
  have hrec : Q'.ofNat (K ^ m) * qpow σ (K * K)
      + HalfPow.half * (Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K)))
      ≤ Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K)) := by
    -- write F0 := K^m·σ^{K²} below.  (1/2)·(2·F0) ≃ F0 ; F0 + F0 ≃ 2·F0.
    refine Q'.le_of_eqv ?_
    -- F0 + (1/2)·(2·F0) ≃ F0 + F0 ≃ 2·F0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat (K ^ m) * qpow σ (K * K)) _
        (Q'.ofNat (K ^ m) * qpow σ (K * K)) ?_) ?_
    · -- (1/2)·(2·F0) ≃ F0
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half (Q'.ofNat 2)
          (Q'.ofNat (K ^ m) * qpow σ (K * K)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (HalfPow.half * Q'.ofNat 2) (1 : Q')
          (Q'.ofNat (K ^ m) * qpow σ (K * K)) ?_)
        (Q'.one_mul_eqv (Q'.ofNat (K ^ m) * qpow σ (K * K)))
      show (HalfPow.half * Q'.ofNat 2).eqv (1 : Q'); decide
    · -- F0 + F0 ≃ 2·F0
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + (1 : Q'))
          (Q'.ofNat (K ^ m) * qpow σ (K * K)) ?_) ?_
      · show (Q'.ofNat 2).eqv ((1 : Q') + (1 : Q')); decide
      · refine Q'.eqv_trans _ _ _
          (Q'.add_mul_eqv (1 : Q') (1 : Q') (Q'.ofNat (K ^ m) * qpow σ (K * K))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ ((1 : Q') * (Q'.ofNat (K ^ m) * qpow σ (K * K)))
            (Q'.one_mul_eqv (Q'.ofNat (K ^ m) * qpow σ (K * K)))) ?_
        exact Q'.add_eqv_congr_left (Q'.ofNat (K ^ m) * qpow σ (K * K)) _ _
          (Q'.one_mul_eqv (Q'.ofNat (K ^ m) * qpow σ (K * K)))
  -- geometric closure
  have hclose := CharacterTail.geom_series_le (fun j => thetaTailTerm σ m K j)
    (Q'.ofNat (K ^ m) * qpow σ (K * K)) HalfPow.half
    (Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K)))
    HalfPow.half_nonneg hHnn hf0le hdom hrec M
  -- thetaTailSum σ m K M = finSum (fun j => thetaTailTerm σ m K j) M
  show RationalTail.finSum (fun j => thetaTailTerm σ m K j) M
      ≤ Q'.ofNat 2 * (Q'.ofNat (K ^ m) * qpow σ (K * K))
  exact hclose

/-! ## 5. THE FIRST-BLOCK LOWER BOUND `Rsum_m(K) ≥ K^m·σ^{K²}`

The cleanest constructive lower bound keeps the leading head term: every nonempty
window dominates its `j = 0` term, all later terms being nonnegative.  Summing such
head blocks across the active scale `K ≲ τ^{−1/2}` gives the leading τ-scaling
order `τ^{−(m+1)/2}` (the caller's instantiation; cf. the `Zsum_ge_head` cube
lower bound for the analogous block-summation device on the partition side). -/

/-- **THE FIRST-BLOCK LOWER BOUND.**  On `0 ≤ σ`, for any nonempty window
(`M = M' + 1`):

    Rsum_m(K)  =  thetaTailSum σ m K (M'+1)  ≥  ofNat(K^m)·qpow σ (K·K)
                                            =  K^m · σ^{K²}.

PROOF.  `thetaTailSum σ m K (M'+1) = thetaTailTerm σ m K 0 + thetaTailSum σ m (K+1) M'`
(`thetaTail_head_drop`); the head term is `K^m·σ^{K²}` and the shifted tail is
nonnegative. -/
theorem thetaTail_ge {σ : Q'} (hσ : (0 : Q') ≤ σ) (m K M' : Nat) :
    Q'.ofNat (K ^ m) * qpow σ (K * K)
      ≤ thetaTailSum σ m K (M' + 1) := by
  -- thetaTailSum σ m K (M'+1) ≃ term(K,0) + thetaTailSum σ m (K+1) M'
  have hdrop := thetaTail_head_drop σ m K M'
  -- term(K,0) = K^m·σ^{K²}
  have hhead : thetaTailTerm σ m K 0 = Q'.ofNat (K ^ m) * qpow σ (K * K) := by
    show Q'.ofNat ((K + 0) ^ m) * qpow σ ((K + 0) * (K + 0))
        = Q'.ofNat (K ^ m) * qpow σ (K * K)
    rw [Nat.add_zero]
  -- term(K,0) ≤ term(K,0) + (nonneg tail)
  have htailnn : (0 : Q') ≤ thetaTailSum σ m (K + 1) M' :=
    thetaTailSum_nonneg hσ m (K + 1) M'
  have hge : thetaTailTerm σ m K 0
      ≤ thetaTailTerm σ m K 0 + thetaTailSum σ m (K + 1) M' :=
    Q'.add_le_self_of_nonneg _ _ htailnn
  -- assemble
  rw [hhead] at hge
  exact Q'.le_trans' _ _ _ hge (Q'.ge_of_eqv hdrop)

/-! ## 6. Demo: the two-sided bound fires at a concrete weight

A self-contained instance at `σ = 1/2`, degree `m = 2`, cutoff `K = 2`.  The cutoff
inequality is a decidable `Q'` fact:

  * cutoff:  `2²·(1/2)^{2·2+1} = 4·(1/2)^5 = 4/32 = 1/8 ≤ 1/2`.

So the upper bound gives `thetaTailSum (1/2) 2 2 M ≤ 2·(2²·(1/2)^4) = 2·(4·1/16) =
1/2` for every window `M`, and the lower bound gives `≥ 2²·(1/2)^4 = 1/4` on any
nonempty window. -/

/-- The concrete demo base `σ = 1/2`. -/
def demoSigma : Q' := Q'.mkPos 1 2 (by decide)

theorem demoSigma_nonneg : (0 : Q') ≤ demoSigma := by decide
theorem demoSigma_le_one : demoSigma ≤ (1 : Q') := by decide

/-- The demo cutoff `2²·(1/2)^5 ≤ 1/2` (decidable). -/
theorem demo_cut : Q'.ofNat (2 ^ 2) * qpow demoSigma (2 * 2 + 1) ≤ HalfPow.half := by decide

/-- **The UPPER bound fires at `σ = 1/2`, `m = 2`, `K = 2`.**  For every window `M`,
`thetaTailSum (1/2) 2 2 M ≤ 2·(2²·(1/2)⁴)`. -/
theorem demo_upper :
    ∀ M, thetaTailSum demoSigma 2 2 M
      ≤ Q'.ofNat 2 * (Q'.ofNat (2 ^ 2) * qpow demoSigma (2 * 2)) :=
  thetaTail_le demoSigma_nonneg demoSigma_le_one 2 2 (by omega) demo_cut

/-- **The LOWER bound fires at `σ = 1/2`, `m = 2`, `K = 2`.**  For every nonempty
window, `thetaTailSum (1/2) 2 2 (M'+1) ≥ 2²·(1/2)⁴`. -/
theorem demo_lower :
    ∀ M', Q'.ofNat (2 ^ 2) * qpow demoSigma (2 * 2)
      ≤ thetaTailSum demoSigma 2 2 (M' + 1) :=
  fun M' => thetaTail_ge demoSigma_nonneg 2 2 M'

end YMGap.Continuum.RDThetaTail

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RDThetaTail.thetaTailTerm_nonneg
#print axioms YMGap.Continuum.RDThetaTail.thetaTailSum_nonneg
#print axioms YMGap.Continuum.RDThetaTail.thetaTail_succ
#print axioms YMGap.Continuum.RDThetaTail.thetaTailTerm_shift
#print axioms YMGap.Continuum.RDThetaTail.thetaTail_head_drop
#print axioms YMGap.Continuum.RDThetaTail.sq_succ
#print axioms YMGap.Continuum.RDThetaTail.polyRatio_succ_nat
#print axioms YMGap.Continuum.RDThetaTail.thetaTailTerm_ratio
#print axioms YMGap.Continuum.RDThetaTail.thetaTail_le
#print axioms YMGap.Continuum.RDThetaTail.thetaTail_ge
#print axioms YMGap.Continuum.RDThetaTail.demo_upper
#print axioms YMGap.Continuum.RDThetaTail.demo_lower
