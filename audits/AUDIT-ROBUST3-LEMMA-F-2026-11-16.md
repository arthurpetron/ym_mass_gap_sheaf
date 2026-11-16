# Audit: Robust3LemmaF: Lemma F (i)–(ii) on partial sums; stop conditions for F (iii)/(iv) and the log2 link (2026-11-16)

File: `lean/YMGap/RG/Robust3LemmaF.lean` (238 lines, new). Source: `results/task2h_proof_note.md` (task2i version),
§4 (4f) Lemma F. Check: direct `lean -M 6144`, 1.2 s wall, 1.1 s user CPU, peak RSS 1717 MiB, min MemAvailable
12899 MiB, rc 0, zero warnings. Axiom-check process: 0.7 s, peak RSS 1661 MiB.

## PROVED (rational; for all k, j; n = k+14 ≥ 14, n' = n+j)
- `lemmaF_i` :162: `B_n ≤ B_{n'} ≤ B_n + 2^{-n}`, with `B_n = 22L_n/(3P_n)` exactly as in `ecomp` (`Bn` :110).
  Ingredients:
  - `P_drop` :92: `P_n ≤ P_{n'} + 6t_{n+1}`;
  - `t_le_pow4`;
  - `B_le_one` :153;
  - P ≥ 9;
  - the atomic bound `atomF` :121: 6·4^{-(n+1)} + (22/3)/((n+1)2^n) ≤ 9·2^{-n}.
- `lemmaF_ii` :210: `κ'_{n'} ≤ κ'_n ≤ κ'_{n'} + (9/10)·1/((n+1)2^n)`, with `κ'_n = (51/121)/L_n` (`kn` :207).
  Ingredients: L ≥ 69/100 and κ' ≤ 62/100 ≤ (9/10)(69/100).
- Division helpers: `div_le` :29, `le_div` :43, `divmul_eqv` :57.
- Axioms (temp file, deleted): div_le, le_div, P_drop, atomF, lemmaF_i and lemmaF_ii all depend on
  [propext, Quot.sound]. There is no sorry, admit, Classical, native_decide, omega, simpa or grind.

## Dependency on SERIES_LIMITS_OPEN (explicit, unchanged)
Lemma F compares against the ideal `B = 22 ln2/(3π²)` and `κ' = κ/ln2`. Under the named assumption `SERIES_LIMITS_OPEN`
(ln2 = lim L_n, π²/18 = lim S_n), B_{n'} → B and κ'_{n'} → κ' as j → ∞. That turns `lemmaF_i` into
F (i), `0 ≤ B − B_n ≤ 2^{-n}`, and `lemmaF_ii` into F (ii), `0 ≤ κ'_n − κ' ≤ 0.9·2^{-n}/(n+1)`.
The Lean statements are partial-sum (finite-j) forms; the limit step is the named assumption. Hypotheses: the note
requires m ≥ 60 (n ≥ 70), while the Lean statements hold for every n ≥ 14, which is strictly more general.

## STOP conditions
- **F (iii) is not done.** It bounds η_C = |E^L_C − BD| ≤ (2m+1)2^{-n} and η′ ≤ (3m+3)2^{-n}. It would need a
  decoupled `D_n(m)` (n independent of m), bounds on D_n − D_{n'} (κ and κ² differences times H), D ≤ 2m for m ≥ 60,
  and four-term products. Estimate: +300–400 lines, which together with F (i)/(ii) passes the ~600-line threshold for
  this step. Not started.
- **F (iv) is blocked (new analysis interface).** It propagates η into (4a)–(4e) through Lemmas N and M (the
  Bessel-ratio maps) and the log bounds (I3). None of these exist in Lean (see
  SCOPE-TASK2H-BESSEL-AND-ERROR-PROPAGATION).
- **Task (3), linking `log2` to L_n, is not done (new analysis interface).** The repo's `log2` is `logRat 2 = 2·artanh(1/3)`
  (`Constructive/CRealLog.lean:876`), with rational enclosures `log2Lower/Upper`. L_n = Σ 1/(k2^k) is the Mercator series
  of −ln(1−1/2). The two partial-sum sequences share no finite algebraic relation, so proving they have the same limit
  needs a functional identity of power series. That means either log of a product with a Mercator-series
  characterisation, or term-wise differentiation/integration. The repo has neither (no `log_mul`/Mercator lemma; only
  artanh congruence lemmas in `CRealLogRatCongruence`). So `SERIES_LIMITS_OPEN` stays as is, and no smaller pi-only
  assumption was introduced, because it would only make sense once the ln2 half was discharged.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay. This is direct lean against copied oleans,
not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: these are pure statements about the rational schedule constants, with no gauge-group content. The standing
U(1) note is unchanged.
