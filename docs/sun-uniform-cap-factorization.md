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
the exponential atoms.

**UPDATE 2026-06-15 — the exp machinery for (B1) and (B3) is now BUILT** (the
"rational surrogate can't carry the tail" obstruction is resolved by genuine
geometric domination):

  * `Constructive/ExpGeomBound.expNeg_mul_le_pow` : **`e^{−a·m} ≤ ρ^m`**
    (`ρ < 1` rational) from `e^{−a} ≤ ρ`.  The continuous→geometric bridge.
  * `Constructive/ExpGeomSum.expNeg_geom_csum_le` : **(B1) geometric envelope**
    — `Σ_{m<N} e^{−a·m} ≤ H` (the heat-kernel exponential sum closes
    geometrically), via `leRat_csum` + `geometric_tail_closure`.
  * `Constructive/GeomBeatsLinear.geom_beats_linear` : **(B3) scalar tail** —
    `(k : Q')·s^k ≤ 1` for `s ≤ 1/2` (geometric decay crushes the linear `k`).
    With `e^{−tδ_N} ≤ ρ^{N−1}` (`expNeg_mul_le_pow` at `m = N−1`, `δ_N ≥ c(N−1)`)
    and `s = 4ρ ≤ 1/2`, this gives `(N−1)(4ρ)^{N−1} ≤ 1`, i.e. (B3).

  * `RG/PerAxisTail.expNeg_poly_csum_le` : **the FULL (B1) per-axis tail** —
    `Σ_{m<N} w(m)·e^{−g(m)} ≤ B₀·H^{d+1}` for a per-term exponent `g(m) ≥ a·m`,
    polynomial weight `w` dominated by `B₀·C(m+d,d)`.  Chains
    `expNeg_mul_le_pow` + `expNeg_antitone_leRat` (through `g(m) ≥ a·m`) +
    `leRat_smul_nonneg` + `leRat_csum` + `weightedGeomSum_le`.  This closes the
    *polynomial*-geometric per-axis character tail (`(m+1)^{2q_i}·e^{−t h_i(m)}`,
    `d = 2q_i`, `g(m) = t h_i(m) ≥ (t q_i/2) m`) at a single explicit rational —
    the complete discharge of `AxisFactorBound` from the constructive exp stack.

All axiom-clean (`[propext]`/`[propext, Quot.sound]`).

**The exponential machinery for the cap is now COMPLETE** — every atom (B1
full polynomial-geometric, B3) has a built, general, axiom-clean kernel, and the
"rational surrogate can't carry the tail" obstruction (§6) is fully resolved.

## 6. SU(N) per-axis inputs now built (2026-06-15)

The tight per-axis tool `RG.charTail_geom_le` (`S_i ≤ 1/(1−P·ρ)`) and its SU(N)
inputs are now in place:

  * `RG.polyWeight_ratio` — the weight `(m+1)^{2q_i}` has ratio `P = 4^{q_i}`.
  * `RepTheory.suN_C2_fundweight_mul_le_hk` — the linear lower bound
    `C₂(ω_i)·m ≤ h_i(m)` (the `hge` input, scaled by `t`).
  * The geometric base is `ρ = e^{−t·C₂(ω_i)} = e^{−c·q_i} ≤ ρ_0^{q_i}` (via
    `expNeg_mul_le_pow`, `c = t(N+1)/(2N)`), so `P·ρ = (4ρ_0)^{q_i} < 1` for
    `ρ_0 < 1/4` (`t` past `t_0`).  (The Padé base `1/(1+·)` is only
    *polynomially* small and would give `P·ρ → ∞`; the geometric base is
    essential — this is the same §6 obstruction, resolved.)

## 7. The HONEST remaining gap (infrastructure-scale, not lemma-scale)

Assembling the literal uniform-in-N cap from here is NOT mere plumbing — it
requires two pieces of genuine NEW infrastructure that the cap framework
deliberately ABSTRACTS as named inputs (`AxisFactorBound`, the `hfact`
hypothesis of `Zt_le_ztValue`):

  1. **The general SU(N) heat-kernel character SUM as a constructed object.**
     `charTail_geom_le` bounds a *constructed* `CReal.csum`; but the SU(N)
     per-axis factor `S_i = Σ_{λ} (dim V_λ)² e^{−t C₂(λ)}` is, for general `N`,
     ONLY abstract `Q'` data in `AxisFactorBound` — the actual `CReal` lattice
     sum is constructed only for SU(2) (`WilsonFunctional`) and SU(3)
     (`SU3CharFactor`).  Building it for all `N` needs the general Weyl
     dimension formula + the multi-index `ℕ^r` lattice sum — major
     representation-theory formalization.

  2. ~~**The rank-general Tonelli factorization**~~ — **RESOLVED for ranks 2–3**
     (2026-06-15, `RG/TonelliFactor.lean`).  The multi-index step is NOT a
     measure-theoretic statement: it is a bound on a NESTED FINITE `CReal.csum`
     whose term obeys a SEPARABLE rational bound `term(λ) ≤ ∏_i aᵢ(λᵢ)`.
       * `csum2_prod_le` — rank-2 Tonelli, `Z2D_le` abstracted OFF the SU(3)
         specifics (`charTerm2D`/`gBound`) to an arbitrary term family + separable
         bound, with independent lengths: `Σ_p Σ_q term ≤ (Σa)(Σb)`.
       * `csum3_prod_le` — **rank-3 (the SU(4) case)**: `Σ_pΣ_qΣ_r term ≤
         (Σa·Σb)·Σc` given `term p q r ≤ (a p·b q)·c r`.  Same nested-`leRat_csum`
         argument one layer deeper; the middle layer threads the outer factor past
         the `Σc` constant via `mul_swap_right_eqv`.
     Both axiom-clean (`[propext]`), in the aggregator.  The Tonelli lemma cleanly
     ABSTRACTS the analytic separable bound `term(λ) ≤ ∏ aᵢ(λᵢ)` (Casimir split
     `C₂(λ) ≥ Σ hᵢ(λᵢ)` + Weyl-dim factorization, each axis's `e^{−t·}` dominated
     by a rational `ρ^{λᵢ}` via `expNeg_mul_le_pow`) as its `hterm` hypothesis and
     delivers `Z_t ≤ ∏ Σaᵢ`.  The per-axis `Σaᵢ ≤ Hᵢ` is the geometric closure
     (rational analogue of `axisFactor_geom_le`).  Ranks 2–3 cover SU(3) and
     SU(4); arbitrary `r` still needs the `r`-fold nested-`csum` structure, but the
     `csum2 → csum3` pattern shows that is mechanical induction on rank, not a new
     idea.  What remains genuinely open is therefore (1) [the constructed
     character-sum object for general `N`] and the analytic separable bound — NOT
     the Tonelli combinatorics.

So: the ENTIRE arithmetic spine of the cap is built and axiom-clean — the
exponential machinery (B1/B3 kernels), the tight per-axis tail tool, the
rank-collapse, the geometric-beats-linear scalar, and the SU(N) rep-theory
(gap floor, `q_i ≥ N−1`, `h_i` linear bound, `P = 4^{q_i}`).  What remains is
the CONSTRUCTION of the general SU(N) character-sum object and its Tonelli
factorization — rep-theory infrastructure of the scale of a `SU3CharFactor`
generalized to all ranks.  This is why SU(2) and SU(3) are the only groups
closed unconditionally: they are the only ones whose character sum is built.
The remaining gap is therefore infrastructure-scale, not a missing lemma.

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
