# Audit: Robust3SeriesBrackets (2026-11-16)

File: `lean/YMGap/RG/Robust3SeriesBrackets.lean` (311 lines, new). Uses the Robust3 definitions `lnS`, `piST` and `pUp`
from `Robust3UndershootAfSchedule` verbatim. Check: direct `lean -M 6144`, 1.2 s wall, 1.2 s user CPU,
peak RSS 1717 MiB, minimum MemAvailable 13051 MiB, rc = 0, zero warnings.

## What is PROVED (all over `Q'`, constructive, Mathlib-free)
- NQ semantics: `red_spec` :26 (`red a b` has value a/b), `toQ_red` :47, `toQ_lit` :53, `toQ_add` :57 and
  `toQ_mul` :67 (both up to `eqv`, given positive denominators), and the positivity lemmas `lnS_d_pos` :81 and
  `piST_d_pos` :148.
- **ln 2 bracket on partial sums:** `ln2_partial_bracket` :143 states, for all n and m,
  `L_n ≤ L_{n+m} ≤ L_n + 1/((n+1)·2^n)`. The proof uses `U_n = L_n + 1/((n+1)2^n)`, which decreases (`LU_anti` :128,
  with the atomic step `lcap_step` :108), while `L_n` increases (`LQ_mono` :103).
- **π²/18 bracket on partial sums:** write `V_n = S_n + (4/3)t_{n+1}`; `pUp_eqv` :233 shows `P_n ≃ 18·V_n`.
  `pi2_partial_bracket` :269 states, for all n and m:
  - `S_{n+m} ≤ V_n`;
  - `S_n + t_{n+1} ≤ S_{n+1+m}`;
  - `V_n ≤ (S_n + t_{n+1}) + t_{n+1}/3`.

  The ingredients are the ratio bound `RQ_le` :174 (`t_{k+1}/t_k = k²/((2k+1)(2k+2)) ≤ 1/4`), the core algebra lemma
  `key_V` :188 and `VQ_anti` :248. In P form: `pUp_lower` :278 gives `18·S_{n+m} ≤ P_n`, and `pUp_upper` :284 gives
  `P_n ≤ 18·(S_{n+1+m} + t_{n+1}/3)`.
- `t_le_pow4` :303 states `t_{n+2} ≤ 4^{-(n+2)}`, i.e. `t_{n+1} ≤ 4^{-n-1}` for n ≥ 1. It is false at n = 0, where
  t_1 = 1/2. The schedule uses n ≥ 14.
- Corollaries proved along the way: L_n increasing, V_n = P_n/18 decreasing, S_n increasing.

## NAMED ASSUMPTION (not formalised): `SERIES_LIMITS_OPEN`
`ln 2 = lim_m L_m` and `π²/18 = lim_m S_m` are classical series identities. The repo does have `CReal` constants
(`Constructive/Pi.lean:556 pi`, `Constructive/CRealLog.lean:876 log2 = logRat 2`), but neither comes with a lemma
identifying it as the limit of these particular series. Proving that would mean showing two different series (an
artanh/logRat series, and Machin- or arcsin-type series) have the same limit, plus the arcsin² identity
Σ 1/(k²C(2k,k)) = π²/18. I judged that out of scope Mathlib-free within the caps, so I stopped on the CReal link and
kept the rational statements.

Under the assumption, letting m → ∞ in the proved statements gives exactly the requested brackets:
- `0 ≤ ln2 − L_n ≤ 2^{-n}/(n+1)`;
- `0 ≤ P_n − π² ≤ 6·t_{n+1} ≤ 6·4^{-n-1}` for n ≥ 1.

**Weakening:** the brackets are stated on the partial sums (finite m) rather than against `pi` or `log2`. The limit
step is the named assumption above.

## Axioms
`#print axioms` was run in a temp file, since deleted. `red_spec`, `toQ_add`, `toQ_mul`, `ln2_partial_bracket`,
`key_V`, `pUp_eqv`, `pi2_partial_bracket`, `pUp_lower`, `pUp_upper` and `t_le_pow4` all depend on [propext, Quot.sound].
There is no sorry, admit, Classical, native_decide, omega, simpa or grind. (`grind` was tested and pulls in
Classical.choice, so it is not used.)

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is
direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: these are pure rational/series facts, with no gauge-group content.
