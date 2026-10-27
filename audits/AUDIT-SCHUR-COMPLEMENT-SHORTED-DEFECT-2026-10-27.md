# Audit — `SchurComplementShortedDefect` (2026-10-27 PT)

## Classification
- **Linear-algebraic / variational RG descent infrastructure (`V4` / `V2`, following Hayakawa `2610.23695`, Lemma 2.4, Lemma 3.7, Prop. 3.10, Thm. 5.2).**
- **The 4D weak-coupling non-abelian subspace Gram-loss bound `θ̄_j ≤ c0 / side_j` (`side_j · θ̄_j ≤ c0`) remains the OPEN Clay-level dimensional-transmutation input.**
- **NOT a proof of the open conjecture; NOT mass-gap evidence.**

## Scope & Hygiene
- File: `lean/YMGap/RG/SchurComplementShortedDefect.lean` (337 lines).
- Formalizes `SchurBlockEnergy` (`schur_le_energy`, `schur_attained_at_response`, `shorted_le_compression`), `VariationalLocalizationStep` (`effective_energy_decomp`, `gluingDefect_nonneg` `D_τ ≥ 0`, `drop_gluingDefect_lower_bound`), and multi-depth multiplicative retention `multiplicative_retention_of_nonneg_defect` (dropping `D_τ ≥ 0` avoids additive `∑ 2^j eff_j` error blowup and leaves `∏_k (1 - θ̄_k)`).
- Connects to `ScaleDependentContractionCertificate` and `GroupedContractionDoor` via `ShortedGramLossContractionCertificate.toScaleDependentContractionCertificate`, `rateProduct_eq_retentionProduct`, and `toUniformContractionCertificate`.
- Connects to `ScaleDependentShiftedH1Conjecture` via `PathShortedGramLossBound`, `pathScaleDependentShiftedContraction_of_shortedGramLoss`, `shortedGramLoss_inhabits_conjecture`, `shortedGramLoss_closes_padded_shifted_anchor`, and `afPadded_closed_by_shortedGramLoss`.
- Axioms (`#print axioms`): `⊆ {propext, Quot.sound}` on all 25 declarations. Banned-token scan: 0 matches.
