# STATUS: r49 / Robust3 chain, open hypotheses of the final theorem (2026-11-16, HEAD b990f637)

**This is NOT chart closure.** Every result below is a PROVED *reduction* under the named OPEN hypotheses.
- Numerics are evidence, not proof.
- δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.
- Build caveat: direct lean against copied oleans, not lake-verified.

**Final theorem:** `robust3_physical_floor_noMargin_HK`, `lean/YMGap/RG/Robust3SpacingHeatKernel.lean:75`.
- It specialises `robust3_physical_floor_noMargin` (`Robust3MarginDischarge.lean:99`) and
  `robust3_physical_floor` (`Robust3UndershootCrossoverInstance.lean:137`).
- Conclusion: floor·aHK(w_n) ≤ (P₃·aHK(w_0))·latticeMargin_n, with P₃ ≈ 81.92 and a = aHK ∘ r3Nome.
- `hmargin_OPEN` is discharged (`Robust3MarginDischarge.lean:68`).
- Numerics root: `/workspace/ym_tmgap_2026-11-15/` (README §§ and `results/` files cited below).

| hypothesis | Lean location (binder) | evidence | U(1)? |
|---|---|---|---|
| `hcross_OPEN`: δ_n ≤ etaR3 n = 1/64 for n < 6 (nomes = dyTable, w ≤ 0.735 → 0.779) | SpacingHeatKernel:79; etaR3 at CrossoverInstance:49 | TM (open cube): δ_min = 0 for steps 0–5, with one mixed pairing at 0.0015 ≤ 1/64 (README §7; `results/task2b.json`, `task2b_tables.md`). Spectral lower bound only, in finite volume. | unknown for δ. U(1) loses its gap beyond w_c ≈ 0.46 (README §3, `results/tables.md`), so the floor conclusion would fail for U(1) there. |
| `hafδ_OPEN`: δ_n ≤ (1/10)·afGap_n² for n ≥ 6 | SpacingHeatKernel:80 | δ_min = 0 only (necessary). Window: task2k 1 − ℓ − 2σ ≥ 0.28 / 0.20 at j6 / j7 (`results/task2k_hk.md` §5). Tail: arb for 10 ≤ j ≤ 10⁷ in 10 coupling-map models (README §12, `results/task2g_arb_summary.json`); analytic for j ≥ 10⁶ (README §13, `results/task2h_proof_note.md`, `task2h_lead_1000000_v2.json`, `task2j_lead_1000000.json`). No evidence for the quantitative (1/10)·afGap² bound itself. | unknown. U(1) has no AF regime, and the coupling-map models are SU(2)-specific. |
| `hupper_OPEN`: ‖Φy‖_C ≤ ‖y‖_F | SpacingHeatKernel:87 | None direct. The δ_min analyses presuppose a Φ and the TM identification (README §4 definitions, §6 caveats). | unknown |
| `hschur_OPEN`: Schur decomposition with D ≥ 0 | SpacingHeatKernel:90 | None direct (same presupposition, README §4). | unknown |
| `Phi`, `D`, `width`, `delta` data; `_hd0`/`_hd1` (0 ≤ δ ≤ 1) | SpacingHeatKernel:76–86 | Data. hd0/hd1 are trivially satisfiable alone, but not jointly witnessed with hcross–hschur. | n/a |
| `_hpos`: aHK(w_j) > 0 | SpacingHeatKernel:93; def :47 | SU(2): a√σ > 0 measured at w6–w8 (task2k §4). Witnessed by the toy `aHKw` (`Robust3NomeInjective.lean:207`). | expected to FAIL for j ≥ 2 (w_2 = 0.35 < 0.46 ≤ w_3 = 0.56): σ = 0 in the Coulomb phase (README §3; numerical, not proved) |
| `_hwin_MC`: spacing on aHK for j6–7 | SpacingHeatKernel:94; def :39, window :50 | task2k direct heat-kernel MC: ℓ6 = 0.678±0.018 (+0.204, 11σ), ℓ7 = 0.676±0.018 (+0.077, 4.4σ) (`results/task2k_hk.md` §5, README §17). Earlier naive-map j6 failure: `results/task2i_window.md`. | expected to fail (Coulomb at w6, w7; numerical) |
| `_hoff_OPEN`: spacing on aHK for j < 6 and j ≥ 8 | SpacingHeatKernel:94; def :43 | j < 6: no direct a(w) data. j8: pending (w9 at L ≥ 20–24); literature models only (task2k §7). j ≥ 10: arb or analytic, for the coupling-map models (README §12–13), i.e. map-based, not heat-kernel a(w). | expected to fail for j ≥ 2 (Coulomb; numerical) |
| `SERIES_LIMITS_OPEN`: ln2 = lim L_n, π²/18 = lim S_n | not a binder of the final theorem; named in docstrings `Robust3SeriesBrackets.lean:15`, `Robust3LemmaF.lean:14`, `Robust3LemmaFiii.lean:14` | A standard mathematical fact (classical series), not formalised. Used only to link the Lemma F partial-sum results to the proof note's ideal constants. | group-independent (n/a) |
| Meta: the repo carrier step is one TM step of T = M^{1/2}EM^{1/2} | not in Lean (identification) | README §1, §6 caveats | n/a |

**Witnessed vs not.** Only the spacing and positivity hypotheses (`_hpos`, `_hwin_MC`, `_hoff_OPEN`) have a concrete
witness, `aHKw`, for every window. hcross, hafδ, hupper and hschur, together with the Phi/D data, have **no** joint witness, so
the final theorem is not shown non-vacuous as a whole.

**U(1) summary.** The positivity and spacing hypotheses on a string tension are where U(1) is expected to fail (Coulomb
phase beyond w ≈ 0.46, numerical). So any instance of the final theorem at w ≳ 1/8 encodes genuine non-abelian
content, as the standing U(1) note says. For the δ-type and structural hypotheses the U(1) status is unknown.

**Other recent state.** Proved since 12:28 PM:
- ecomp monotone, and now strict (`Robust3NomeInjective.lean:69`); r3E = ecomp;
- Lemma F (i)–(iii) on partial sums (`Robust3LemmaF.lean:162/210`, `Robust3LemmaFiii.lean:51/112`);
- the hspacing heat-kernel interface;
- r3Nome injective.

Blocked:
- F (iv), which needs the Lemma N/M/I3 interface;
- the log2 ↔ L_n link, which needs a series-identity interface.
