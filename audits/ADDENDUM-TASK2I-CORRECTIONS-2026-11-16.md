# Addendum: task2i corrections to the task2h proof note (2026-11-16)

Supplements AUDIT-ROBUST3-CURRENT-SCHEDULE-AND-NUMERICS-2026-11-16.md and
SCOPE-TASK2H-BESSEL-AND-ERROR-PROPAGATION-2026-11-16.md (commit 74279c33). Additive; no Lean changed.

Source: /workspace/ym_tmgap_2026-11-15/results/task2h_proof_note.md (task2i revision; the earlier
copy is task2h_proof_note.pre2i.md), with its dependency table and lemmas P1, R, N, M, F, G.

- Corrected constants (proof note): B/2 = 0.2575118..., so B = 0.5150236...; q = (b1^2 - b2^L b0)/(2 b0^3) = 0.0832372...
- (4g): YM Bot reports that the older 3.7/m^3 bound was false. The proof note now uses
  Lemma G: |dg/ln2 - T3| <= 2.5/m^3 for m >= 10^6. The constants are in arb
  (results/task2i_constants.json), and the worst arb ratio is 0.965 of 2.5.
- **Thin margins in Lemma G's hypotheses:** min beta-bar/m = 0.2575118 against the required 0.2575, and
  max d-beta = 0.2575120 against the required 0.25752. Both hold numerically on m in [10^6, 10^9]
  (80 log-spaced points plus endpoints). That is a sampled arb check, not a proof over the whole interval,
  so a formalization of G would need these margins proved with rational bounds that are tight to
  about 1e-5 relative. This is added to the non-rigorous items and to the blockers for scoping item (d).
- None of this changes the Robust3 Lean files or their theorems. The open hypotheses are unchanged:
  hcross, hafdelta, hupper, hschur, hspacing, and SERIES_LIMITS_OPEN.

Caveats: direct lean against copied oleans, not lake-verified. delta_min = 0 is only a necessary
condition. The schedule results use SU(2) constants. The U(1) strong-coupling polymer bound does not
settle the gap. No chart closure is claimed.
