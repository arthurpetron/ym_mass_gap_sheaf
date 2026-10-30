# Audit — Two-Block Schur-Margin Gap Assembly (r50, 2026-10-30)

## Scope & honest label
- Module: `lean/YMGap/RG/TwoBlockSchurMarginGap.lean` (236 lines). Source: Hayakawa 2609.39802 Lemma 9 and Prop. 8 (first half).
- Label: **infrastructure, NOT gap evidence.** Every statement holds verbatim for any finite group, abelian ones (Z2, U(1) truncations) included. The file converts an OPEN Schur margin into a gap; it does not produce the margin.
- Note error flagged: the 2026-10-28 HP note's title for 2609.39802 ("3D lattice YM decimation") is wrong; it is a quantum-double Davies-gap paper.

## Proved
- `TwoBlockForm.absorb_cross`, `TwoBlockForm.diag_floor`, `TwoBlockForm.twoBlock_gap` (`(1-s)·min(a,τ)·N ≤ K`).
- `lsum_le`, `lsum_smul`, `interface_complement_floor` (`g_loc·κ·‖y‖² ≤ r_K·T(y)`).
- `hcross_of_sq_bound` (`B² ≤ s²AT`, `s,A,T ≥ 0` ⟹ `2B ≤ s(A+T)`; degenerate `s(A+T)=0` case handled by a decidable split, no Classical).
- `relative_of_twoBlock` (`K ⪰ gN`, `Ec ≤ Kmax·N`, `γ·Kmax ≤ g` ⟹ `γ·Ec ≤ K`, i.e. `(1-δ)(A-C) ≤ A-F` with `δ = 1-γ`), `schurShape_of_twoBlock` (`K ≈ (1-δ)Ec + D`, `D ≥ 0`).

## OPEN (hypotheses)
- `hA_OPEN` interface gap; `hcross`/margin `s < 1` (= `hschur_OPEN` content); `hT`, `hloc_OPEN`, `hcov_OPEN`, `hG2_OPEN`; `hupper_OPEN`.
- Not formalized: identifying these rational quadratic forms with the completed-carrier energies of `RelativeDissipationScaleChain.SchurDecomposition`. The bridge is rational-level only.

## Verification
- Mac worktree, `LEAN_NUM_THREADS=2 nice -n 10 safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check`: 0 errors, 0 warnings.
- Axioms (temp-file collectAxioms, 37 constants, file deleted): `{propext, Quot.sound}`.
