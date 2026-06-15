# SU(N) uniform tail cap — factorization and status (2026-06-15)

A serious run at the genuinely-open analytic frontier: the uniform-in-N SU(N)
character-tail cap that closes `eta_dominated` (hence `mass_gap_simple_group`)
for the whole A_{N−1} family, not just SU(2)/SU(3).  This note records (i) the
clean closed-form structure, (ii) what is now PROVED in Lean, and (iii) the
sharply-factored remaining analytic atoms.

## 1. The cap and its rank-collapse reduction (already in Lean)

The all-groups budget needs (rank-collapse, `RG/RankCollapse.lean`):

    Z_t(SU(N)) ≤ 2·Σ_{i=1}^{N−1} s_i ≤ Z_t(su2),     2·Σ_i s_i ≤ 1,

where `s_i = S_i − 1`, `S_i(t) = Σ_{x≥0} (x+1)^{2 n_i} e^{−t h_i(x)}` is the
per-axis polynomial-geometric character tail (`notes/uniform-character-tail-bound.md`
§2).  `rank_collapse_of_sum` already turns `2·Σ s_i ≤ Z_t(su2)` (+ window) into
`Z_t ≤ Z_t(su2)`; `RG/CharacterTail.geom_series_le` already bounds each `S_i`
from a term-ratio input.  So the open content is (a) the per-axis ratio data and
(b) the final scalar sum inequality.

## 2. The SU(N) closed form (clean)

For A_{N−1} = SU(N), with `q_i := i(N−i)` (number of positive roots containing
simple root `α_i`):

  * `n_i = q_i`,
  * `‖ω_i‖² = G_ii = q_i / N`,
  * `C₂(ω_i) = q_i·(N+1)/(2N)`,
  * the Casimir split rate **`h_i(x) = (q_i/2)·x·(1 + x/N)`**, so `h_i(1) = C₂(ω_i)`.

Leading per-axis term (`x = 1`):
`(2)^{2q_i} e^{−t·C₂(ω_i)} = [4·e^{−t(N+1)/(2N)}]^{q_i} = b^{q_i}`, `b := 4 e^{−t(N+1)/(2N)}`.

## 3. PROVED in Lean (`lean/YMGap/RG/SUNWeylData.lean`, axiom-clean)

The rep-theory foundation (notes §2a) for the WHOLE family — previously only the
`i = 1` weight (`RepTheory.suN_gap_lb`):

  * **`suN_qWeight_ge`** : `q_i ≥ N−1` for `1 ≤ i ≤ N−1`.  The rigorous
    combinatorial worst-case fact — `q_i` is minimized at `i = 1, N−1` because
    `i(N−i) − (N−1) = (i−1)(N−1−i) ≥ 0`.  This is the SU(N) analogue of
    "SU(2)/the `i=1` axis is the worst case."
  * **`suN_C2_fundweight_gap_lb`** : `Casimir.gapFloor (= 3/4) ≤ C₂(ω_i)` for
    **every** `1 ≤ i ≤ N−1`.  All SU(N) fundamental weights clear the gap floor;
    reduces via `q_i ≥ N−1` to the `N² ≥ 2N` step of `suN_gap_lb`.

So: the per-axis gaps `Δ_i = C₂(ω_i)` are all `≥ 3/4`, minimized at `i=1`
(`= (N²−1)/(2N)`, `= 3/4` only at `N=2`).  This is the "SU(2) is the global
worst case" mechanism, now Lean for arbitrary N.

## 4. The remaining analytic atoms (sharply factored)

With `b = 4 e^{−t(N+1)/(2N)} < 1`, the cap factors into three exponential
inequalities (each a CReal fact about `e^{−t·}` — NOT Q'-expressible, per the
§6 divergence result: a rational surrogate cannot carry the tail):

  **(B1) per-axis tail ≤ 2× leading.**  `s_i ≤ 2·b^{q_i}` — the term ratio
  `((x+2)/(x+1))^{2q_i} e^{−t h_i'(x)} ≤ 1/2` past `x=1` (geometric tail; the
  `CharacterTail.geom_series_le` engine consumes exactly this ratio input).

  **(B2) sum over axes (PROVED-adjacent).**  `Σ_{i=1}^{N−1} b^{q_i} ≤ (N−1)·b^{N−1}`
  — since `0 ≤ b < 1` and `q_i ≥ N−1` (THIS is `suN_qWeight_ge`, proved), every
  `b^{q_i} ≤ b^{N−1}`.  Needs only `b<1` + a `pow` antitone-in-exponent lemma.

  **(B3) the worst-case scalar inequality.**  `4(N−1)·b^{N−1} ≤ Z_t(su2)`, i.e.
  `(N−1)·4^{N−1} e^{−t(N²−1)/(2N)} ≤ e^{−3t/4}` (using `Z_t(su2) ≥ 4 e^{−3t/4}`).
  Equivalently `(N−1)·4^{N−1} ≤ e^{t[(N²−1)/(2N) − 3/4]}` — exponential beats
  polynomial.  Holds for all `N ≥ 2` once `t ≥ t₀ ≈ 6.25` (the canonical
  operating point `t ≈ 11.1` and the whole RG trajectory satisfy `t ≥ t₀`); the
  sup over N of the per-N threshold is finite (`≈ 2.77` as `N→∞`, max near small
  N).  This needs a uniform CReal lower bound `e^{x} ≥ (N−1)4^{N−1}` for the
  N-dependent exponent — the one genuinely new exponential estimate.

`suN_qWeight_ge` discharges the combinatorial heart of (B2).  (B1) and (B3) are
the irreducible exponential atoms; both are standard `e^{−t·}` estimates uniform
in N, but the constructive-`CReal` machinery for N-indexed exponential
lower/upper bounds is not yet in the stack (the `E_antitone` seed handles the
box, not the N-uniform tail constant).

## 5. Honest status

- **Closed**: the SU(N) rep-theory foundation — all fundamental weights clear
  `3/4`, worst case at `i=1` — for ALL N (this run).
- **Reduced**: the cap to the three exponential atoms (B1)–(B3), with (B2)'s
  combinatorial core proved.
- **Open**: (B1), (B3), and the `pow` step of (B2) — uniform-in-N CReal
  exponential estimates.  SU(2) and SU(3) close unconditionally (concrete
  `decide`/`charSum_le`); general N awaits the N-indexed exponential bounds.

This is a structural advance, not a closure: the rep-theory layer the cap rests
on is now Lean for the whole family, and the open problem is three sharp,
named exponential inequalities rather than "the whole cap."
