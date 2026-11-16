# Audit: Robust3 is the current AF schedule; status of the Numerics task2g/2h/2i results (2026-11-16)

## Decision (additive)
`robust3UndershootSchedule` is now the **current AF schedule** of the undershoot route. It was introduced in
79883f3e (`Robust3UndershootAfSchedule`), 7b072c89 (`Robust3UndershootPhysicalUnits`, analysis audit) and c2ad3d15
(`Robust3UndershootCrossoverInstance`).
- It supersedes the earlier variants for forward work: undershoot (d88a0d1d…), Robust (d7301e07…) and Robust2
  (ecaadc70…). Numerics task2f showed Robust2 fails ℓ ≤ 1 from j = 35128, because of its 1e-9 integer floors and A′ < A.
- The older files are untouched. Their theorems remain true as stated; they are simply no longer the schedule we build on.

Lean additions on top of Robust3, made today (all new files):
- **b8766249** `Robust3SeriesBrackets`: rational brackets on the exact partial sums L_n, S_n and P_n. The limit step is
  the named assumption `SERIES_LIMITS_OPEN`.
- **70739a3a** `Robust3StrictFloor` (strict floor E_k > (k+1)/4 for all k, so the floor is never active) and
  `Robust3MarginDischarge` (hmargin_OPEN discharged: `robust3_physical_floor_noMargin`).

## Numerics results (quoted from `/workspace/ym_tmgap_2026-11-15`: README §12–§14 and `results/task2h_proof_note.md`)
- **task2g (README §12).**
  - (0) Brackets: "CONFIRMED (proved and checked)". ln2 − L_n ∈ [0, 2^{−n}/(n+1)] and P_n − π² ∈ [0, 6·4^{−n−1}].
    The exact-rational vs 400-digit check for n = 1..399 is all OK, with worst ratio 0.9975 (L) and 0.348 (P).
  - (1) Rows: Fraction mirror = Lean formula; the E_34 numerator has 115 digits. "E_k is strictly increasing. The
    (k+1)/4 floor and the running-max envelope are never active for k < 1996."
  - (2) 15 models, j6–2000, exact β_char: tail worst 0.0065889 g⁴ at j24 (matched 2L + c-held); window worst 2σ
    margin 0.0269 at j10 (naive FHK92); spacing minimum 1.0666 at j2000.
  - (3) mpmath, 2e3–1e7: worst 0.0077034 g⁴ (matched 2L + c_top, limit 0.007703); spacing minimum 1.06548. The fitted
    remainder satisfies |R| ≤ 0.0049·ln²m/m, but it is **fitted and is not used** by task2h.
  - (4) arb (python-flint, 192-bit balls) certifies, per j, (T) 1 − ℓ_j − 2sd_j > 0, (S) ρ_j > 2^{1−ℓ_j+2sd_j} and
    (E) E_k < E_{k+1}, E_k > (k+1)/4, for the 10 analytic models. README §13: "The task 2g arb run certifies
    10 ≤ j ≤ 10⁷ with no failures (all four segments A–D done)."
- **task2h (README §13; proof note §0).** "For every j ≥ j0 := 1,000,007 (m ≥ M0 = 10⁶), each of the 10 analytic
  models satisfies (T), (S), (E)". Together with arb: "(T), (S) and (E) hold for every j ≥ 10, for these 10 analytic
  models." Status line: "complete modulo two cited classical facts … and the computer-algebra certificates of §2, §3
  and §5 … There is no fitted lemma."
- **task2i (README §14; proof note dependency table, dated 2026-11-16).** This newer update was not in the
  12:28 PM PT brief. It recasts §3 as Lemmas P1/R/N/M with exact-rational certificate polynomials
  (`results/task2i_maps.json`). (4f) and (4g) become Lemma F and Lemma G, with constants in arb.

## Remaining NON-RIGOROUS items (Numerics' own list, proof note §7 plus §14)
1. (L1) and (L1′): monotonicity of I₂/I₁ and its limits are **cited** (Amos 1974; Segura 2011; DLMF), not proved.
   I2 (the harmonic bracket) is cited too; only 1 ≤ H_m ≤ ln m + 1 is used.
2. §4 (4a)–(4e) (R = 15/670), (4h) (RC = 2), (4i) (RS = 100) and (4j) are **handwritten** with crude constants
   (17–85× slack) and are not machine-checked. Lemmas F and G are explicit, but their constants are evaluated in arb.
3. Lemma P/P1 certificates (§2, §3, §5) and the arb range are **computer-assisted** (sympy plus arb), not Lean.
4. Scope: only the 10 analytic coupling-map models, with constants taken as exact definitions (q; c_top and σ;
   float64 c_trend). The window j6–9 and all literature/data models are **empirical**; c_trend as physics is a fit.
5. Numerics did not execute the Lean source (they used a re-implementation cross-checked against the audit table).
6. No fitted remainder is used in task2h.

## Lean-side status (honest)
- PROVED in Lean:
  - the schedule (`NomeSchedule`), `DyadicRGStep` for n < 45, P₃ ≈ 81.92, the crossover instance and the physical
    floor;
  - now hmargin is discharged;
  - E_k > (k+1)/4 strictly for all k, so the floor is inactive;
  - the partial-sum brackets.
- NOT in Lean:
  - (T), (S) and (E)-monotonicity of `ecomp` for any j (that is, envelope inactivity), and all of task2h;
  - `SERIES_LIMITS_OPEN` (ln2 = lim L_n, π²/18 = lim S_n).
- OPEN hypotheses still carried by `robust3_physical_floor_noMargin`: hcross_OPEN, hafδ_OPEN, hupper_OPEN,
  hschur_OPEN and hspacing_OPEN.
- (T) being numerically/analytically positive is δ_min = 0. **δ_min = 0 is only a necessary condition: it removes
  the obstruction but does not prove hafδ.** No chart closure is claimed.

**Build caveat:** the Lean checks here are direct `lean -M 6144` against the box overlay. This is direct lean
against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
