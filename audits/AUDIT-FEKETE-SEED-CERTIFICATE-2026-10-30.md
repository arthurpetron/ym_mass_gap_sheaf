# Audit — Fekete Seed Certificate (r51, 2026-10-30)

## Scope & honest label
- Module: `lean/YMGap/RG/FeketeSeedCertificate.lean` (116 lines). Method template: Okuyama–Ohzeki 2610.32291.
- Label: **finite-certificate format, NOT gap evidence.** Abelian/U(1)-valid; a strong-coupling seed is U(1)-valid.

## Proved
- `qpow`, `qpow_nonneg`, `qpow_add`, `qpow_le_one`, `qpow_le_self`.
- `fekete_multiple`: `Λ ≥ 0`, `Λ(n+m) ≤ ΛnΛm`, `Λ N ≤ ρ^N` ⟹ `Λ((k+1)N) ≤ ρ^((k+1)N)`.
- `fekete_general`: `Λ((q+1)N + r) ≤ ρ^((q+1)N)·Λ r`.
- `fekete_seed_lt_one`: `0 ≤ ρ < 1` ⟹ `Λ((k+1)(N+1)) ≤ ρ < 1`.

## OPEN
- `hcert_OPEN`: the certified numerical value `Λ_N ≤ ρ^N` at the crossover nome `w_{j0}` (not computed).
- Identifying `Λ` with transfer-operator norms on the repo carrier (submultiplicativity is then automatic but is not formalized here).
- The `Λ(0)` case (`k = 0`) is excluded on purpose: submultiplicativity alone does not give `Λ 0 ≤ 1`.

## Verification
- Mac worktree, `LEAN_NUM_THREADS=2 nice -n 10 safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check`: 0 errors, 0 warnings.
- Axioms (temp-file collectAxioms, 14 constants, file deleted): `{propext, Quot.sound}`.
