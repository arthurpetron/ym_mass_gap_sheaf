# Audit: Lemma F (iii) on partial sums, in Robust3LemmaFiiiAlg and Robust3LemmaFiii (2026-11-16)

Source: `results/task2h_proof_note.md` (task2i version), §4 (4f) Lemma F (iii). Builds on 71bc37b7 (`lemmaF_i`, `lemmaF_ii`).
Tail only, m = k+4 ≥ 60 (hypothesis `56 ≤ k`), n = k+14 = m+10. F (iv), the log2 link, j6, rho6 and w6 were not touched.

## Line budget
- Approved budget: about 400 lines; stop threshold: about 550.
- Used: 362 Lean lines (`Robust3LemmaFiiiAlg.lean` 233, `Robust3LemmaFiii.lean` 129), plus this audit and a work_plan entry.
- No stop condition was hit.

## PROVED (rational; `D(c, m)` = `DQ c k`, the schedule's D with the κ' slot set to c)
- `D_eqv'` (Alg:83): the Lean D_n(m) equals D(κ'_n, m).
- `ecomp_eqv` (Alg:96): E^L_C = `ecomp k` equals D(κ'_n, m)·B_n.
- `D_le` (Alg:157): D(c, m) ≤ 2m for m ≥ 60 and 0 ≤ c ≤ 62/100.
- `dD_lean` (Alg:219): D(κ'_N, m) ≤ D(κ'_n, m) ≤ D(κ'_N, m) + 2^{-n}, with N = n+j.
  - Uses `lemmaF_ii`, generic `dD_gen` (Alg:49), H_{m+3} ≤ m+3, and (H_m+1)/m ≤ 4/5.
  - The note's sharper form (n+1 > 2(ln m + 2)) is not needed; the crude bound suffices for all n.
- `lemmaF_iii_C` (Fiii:51), η_C: with N = n+j, both of
  - E^L_C ≤ D(κ'_N, m)·B_N + 2^{-n}(2m+1);
  - D(κ'_N, m)·B_N ≤ E^L_C + 2^{-n}(2m+1).
- `lemmaF_iii_P` (Fiii:112), η′: with N = n+1+j and E^L_F = `ecomp (k+1)` (at n+1 and m+1, as in the note), both of
  - E^L_F + D(κ'_N, m)B_N ≤ E^L_C + D(κ'_N, m+1)B_N + 2^{-n}(3m+3);
  - the reverse inequality, with the same slack.
  - This is the subtraction-free form of |(E^L_F − E^L_C) − Δ_N·B_N| ≤ (3m+3)2^{-n}, with Δ_N = D(κ'_N, m+1) − D(κ'_N, m).
  - It is proved as η_C(m) + η_F(m+1) ≤ (2m+1)2^{-n} + (2m+3)2^{-n-1} ≤ (3m+3)2^{-n} (`eps_sum`, Fiii:101), as in the note.

## What is weaker than the note (honest scope)
- **Partial sums.** The ideal B and κ' are replaced by the Lean values at a deeper index N.
  - The step N → ∞ (B_N → B, κ'_N → κ', then D(·, m) → D(m) by continuity of a polynomial in c) is the named assumption `SERIES_LIMITS_OPEN`.
  - That assumption is not formalised and not changed.
- **No absolute values.** |x| ≤ ε is stated as two one-sided inequalities. η′ is written without subtraction.
- **Monotone direction only.** B_n ≤ B_N and κ'_N ≤ κ'_n come from F (i)/(ii). Nothing about the ideal constants is proved in Lean.

## Checks
| Check | Wall | User CPU | Sys CPU | Peak RSS | Min MemAvailable |
|---|---|---|---|---|---|
| `Robust3LemmaFiiiAlg` | 1.2 s | 1.2 s | 0.3 s | 1710 MiB | 12954 MiB |
| `Robust3LemmaFiii` | 1.0 s | 0.9 s | 0.2 s | 1706 MiB | 13171 MiB |
| Axiom check | 0.8 s | – | – | 1663 MiB | – |

- Both builds: direct `lean -M 6144`, rc 0, zero warnings.
- Axioms (temp file, deleted):
  - `rearr` and `dD_gen`: [propext].
  - `D_eqv'`, `ecomp_eqv`, `W_le`, `seg_le`, `closedD`, `D_le`, `dD_lean`, `lemmaF_iii_C`, `eps_sum` and `lemmaF_iii_P`: [propext, Quot.sound].
- None of sorry, admit, Classical, native_decide, omega, simpa or grind appear.
- Linear Nat side goals use `simp +arith`, whose axioms are within {propext, Quot.sound}.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.
F (iv), i.e. propagation into (4a)–(4e), remains blocked on the missing Lemma N/M/I3 analysis interface.

U(1) note: these are statements about rational schedule constants only, with no gauge-group content.
