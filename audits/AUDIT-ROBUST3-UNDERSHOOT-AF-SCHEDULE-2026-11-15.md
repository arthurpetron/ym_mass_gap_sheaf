# Audit: Robust3UndershootAfSchedule (2026-11-15)

File: `lean/YMGap/RG/Robust3UndershootAfSchedule.lean` (269 lines, new; additive. All earlier files are untouched).
Compile: 8.0 s wall, peak lean RSS 1766 MiB, min free RAM 9043 MiB (direct lean -M 6144).

## What is PROVED
- Exact-rational tail: `ecomp` :91 (closed form E = D·B as a gcd-reduced Nat fraction, NO integer floors), helpers
  `harm` :65, `lnS` :70, `piST` :75, `pUp` :81, `seg` :86. The running max `r3E` :105 is over
  `r3Raw = max(ecomp k, r3Floor k)` with `r3Floor k = (k+1)/4` :100.
- `r3E_mono` :109, `r3Floor_le` :116, `one_lt_r3E` :125, `r3Gap` :153 (= 1/E_k), `r3Gap_anti` :158,
  `r3Gap_le_of_modulus` :177 (k ≥ 4·eps.den ⇒ gap ≤ eps).
- `robust3UndershootSchedule : NomeSchedule` :232. Modulus `11 + 4·eps.den`.
- `robust3_join` :252 (w_0 ≤ 1/55, dyTable for j < 6, w_6 = 779/1000; no offset).
- `robust3_steps` :265: `DyadicRGStep` for every n < 45, by decide on the exact rationals (E_34 has a 115-digit
  numerator).
- Cross-check (temp file, deleted): Lean's `(r3E 34).num/.den` equals the Python `fractions` mirror digit for digit
  (decide +kernel); a deliberately false equation is rejected.
- Axioms ⊆ {propext, Quot.sound}; `r3Gap_le_of_modulus` {propext}. Zero warnings. Forbidden-tactic scan clean.

## What is NOT proved
- That the running max and the floor are inactive. Analysis (in the analysis audit): ΔE > 0.5 at every j, and
  E > (k+1)/4; numerically E_k = ecomp k for k < 300 exactly, and at every sampled j up to 10⁷.
- That B_n ≤ 1/A (i.e. A'_n ≥ A). This follows from L_n ≤ ln 2 (positive series) and P_n ≥ π² (tail ≤ (4/3)t_{n+1},
  since t_{k+1} ≤ t_k/4). It is analysis, used by no theorem.
- All margins (ℓ ≤ 1, spacing): see `AUDIT-ROBUST3-ANALYSIS-2026-11-15.md`.

## j ≤ 41 table: rows that changed vs Robust2
j0–9 are unchanged. The j10 step changes only through w11 (+8.9e-8). Every tail row changes.
| j | w_j (Robust3, exact) | w_j R3 | w_j R2 | g² R3 | β_n R3 | β_c R3 | u_real R3 | u_real R2 | ℓ matched+c held R3 | worst/g⁴ R3 | worst/g⁴ R2 | binding R3 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 11 | 1 − 1/E_0 (E ≈ 6.446417882; 32-digit num) | 0.84487509 | 0.84487500 | 1.3485 | 2.9662 | 3.3440 | 0.19785 | 0.18172 | 0.9105±0.003 | 0.0456 | 0.0356 | matched 2L+c_top |
| 12 | 1 − 1/E_1 (E ≈ 6.880761832; 31-digit num) | 0.85466726 | 0.85485108 | 1.2563 | 3.1838 | 3.5773 | 0.14880 | 0.13921 | 0.9480±0.003 | 0.0292 | 0.0227 | matched 2L+c_top |
| 13 | 1 − 1/E_2 (E ≈ 7.340125327; 39-digit num) | 0.86376254 | 0.86401916 | 1.1717 | 3.4140 | 3.8211 | 0.11736 | 0.11128 | 0.9672±0.003 | 0.0200 | 0.0155 | matched 2L+c_top |
| 14 | 1 − 1/E_3 (E ≈ 7.815000859; 41-digit num) | 0.87204096 | 0.87231999 | 1.0954 | 3.6518 | 4.0704 | 0.09569 | 0.09165 | 0.9777±0.002 | 0.0145 | 0.0113 | matched 2L+c_top |
| 15 | 1 − 1/E_4 (E ≈ 8.300204545; 44-digit num) | 0.87952104 | 0.87979909 | 1.0270 | 3.8948 | 4.3230 | 0.07994 | 0.07716 | 0.9838±0.002 | 0.0113 | 0.0089 | matched 2L+c_top |
| 16 | 1 − 1/E_5 (E ≈ 8.792642718; 45-digit num) | 0.88626855 | 0.88653492 | 0.9659 | 4.1413 | 4.5775 | 0.06805 | 0.06608 | 0.9874±0.002 | 0.0093 | 0.0075 | matched 2L+c_top |
| 17 | 1 − 1/E_6 (E ≈ 9.290344369; 47-digit num) | 0.89236136 | 0.89261159 | 0.9111 | 4.3904 | 4.8333 | 0.05880 | 0.05738 | 0.9898±0.002 | 0.0081 | 0.0067 | matched 2L+c_top |
| 18 | 1 − 1/E_7 (E ≈ 9.791989846; 53-digit num) | 0.89787571 | 0.89810840 | 0.8618 | 4.6415 | 5.0899 | 0.05142 | 0.05038 | 0.9913±0.002 | 0.0074 | 0.0063 | matched 2L+c_top |
| 19 | 1 − 1/E_8 (E ≈ 10.296660459; 54-digit num) | 0.90288113 | 0.90309644 | 0.8173 | 4.8941 | 5.3471 | 0.04543 | 0.04466 | 0.9924±0.001 | 0.0070 | 0.0062 | matched 2L+c_top |
| 20 | 1 − 1/E_9 (E ≈ 10.803696203; 54-digit num) | 0.90743909 | 0.90763787 | 0.7770 | 5.1478 | 5.6048 | 0.04048 | 0.03990 | 0.9932±0.001 | 0.0068 | 0.0061 | matched 2L+c_top |
| 21 | 1 − 1/E_10 (E ≈ 11.312610456; 59-digit num) | 0.91160307 | 0.91178652 | 0.7404 | 5.4024 | 5.8629 | 0.03634 | 0.03590 | 0.9939±0.001 | 0.0067 | 0.0062 | matched 2L+c_top |
| 22 | 1 − 1/E_11 (E ≈ 11.823036554; 61-digit num) | 0.91541936 | 0.91558875 | 0.7070 | 5.6578 | 6.1212 | 0.03283 | 0.03250 | 0.9945±0.001 | 0.0066 | 0.0062 | matched 2L+c_top |
| 23 | 1 − 1/E_12 (E ≈ 12.334693062; 60-digit num) | 0.91892786 | 0.91908445 | 0.6764 | 5.9138 | 6.3797 | 0.02982 | 0.02958 | 0.9949±0.001 | 0.0066 | 0.0063 | matched 2L+c_top |
| 24 | 1 − 1/E_13 (E ≈ 12.847360508; 64-digit num) | 0.92216300 | 0.92230799 | 0.6483 | 6.1703 | 6.6384 | 0.02723 | 0.02704 | 0.9953±0.001 | 0.0066 | 0.0064 | matched 2L+c_top |
| 25 | 1 − 1/E_14 (E ≈ 13.360865360; 67-digit num) | 0.92515455 | 0.92528903 | 0.6224 | 6.4272 | 6.8972 | 0.02497 | 0.02483 | 0.9957±0.001 | 0.0066 | 0.0065 | matched 2L+c_top |
| 26 | 1 − 1/E_15 (E ≈ 13.875068743; 69-digit num) | 0.92792829 | 0.92805325 | 0.5984 | 6.6844 | 7.1561 | 0.02299 | 0.02289 | 0.9960±0.001 | 0.0066 | 0.0066 | matched 2L+c_top |
| 27 | 1 − 1/E_16 (E ≈ 14.389858322; 75-digit num) | 0.93050661 | 0.93062295 | 0.5762 | 6.9419 | 7.4152 | 0.02125 | 0.02118 | 0.9963±0.001 | 0.0066 | 0.0066 | matched 2L+c_top |
| 28 | 1 − 1/E_17 (E ≈ 14.905142368; 72-digit num) | 0.93290906 | 0.93301758 | 0.5556 | 7.1997 | 7.6743 | 0.01970 | 0.01965 | 0.9965±0.001 | 0.0066 | 0.0067 | matched 2L+c_top |
| 29 | 1 − 1/E_18 (E ≈ 15.420845338; 79-digit num) | 0.93515271 | 0.93525413 | 0.5364 | 7.4576 | 7.9335 | 0.01832 | 0.01829 | 0.9967±0.001 | 0.0066 | 0.0068 | matched 2L+c_top |
| 30 | 1 − 1/E_19 (E ≈ 15.936904546; 82-digit num) | 0.93725256 | 0.93734751 | 0.5184 | 7.7158 | 8.1928 | 0.01708 | 0.01707 | 0.9969±0.001 | 0.0067 | 0.0068 | matched 2L+c_top |
| 31 | 1 − 1/E_20 (E ≈ 16.453267617; 82-digit num) | 0.93922180 | 0.93931086 | 0.5016 | 7.9740 | 8.4521 | 0.01597 | 0.01597 | 0.9971±0.001 | 0.0067 | 0.0069 | matched 2L+c_top |
| 32 | 1 − 1/E_21 (E ≈ 16.969890518; 83-digit num) | 0.94107210 | 0.94115577 | 0.4859 | 8.2324 | 8.7114 | 0.01496 | 0.01497 | 0.9973±0.001 | 0.0067 | 0.0069 | matched 2L+c_top |
| 33 | 1 − 1/E_22 (E ≈ 17.486736022; 87-digit num) | 0.94281380 | 0.94289254 | 0.4711 | 8.4909 | 8.9708 | 0.01405 | 0.01407 | 0.9974±0.001 | 0.0067 | 0.0069 | matched 2L+c_top |
| 34 | 1 − 1/E_23 (E ≈ 18.003772494; 89-digit num) | 0.94445609 | 0.94453031 | 0.4572 | 8.7495 | 9.2301 | 0.01322 | 0.01325 | 0.9976±0.001 | 0.0067 | 0.0070 | matched 2L+c_top |
| 35 | 1 − 1/E_24 (E ≈ 18.520972923; 89-digit num) | 0.94600716 | 0.94607723 | 0.4440 | 9.0082 | 9.4895 | 0.01247 | 0.01249 | 0.9977±0.000 | 0.0067 | 0.0070 | matched 2L+c_top |
| 36 | 1 − 1/E_25 (E ≈ 19.038314151; 85-digit num) | 0.94747434 | 0.94754059 | 0.4316 | 9.2669 | 9.7490 | 0.01178 | 0.01181 | 0.9978±0.000 | 0.0067 | 0.0070 | matched 2L+c_top |
| 37 | 1 − 1/E_26 (E ≈ 19.555776244; 94-digit num) | 0.94886421 | 0.94892693 | 0.4199 | 9.5257 | 10.0084 | 0.01114 | 0.01118 | 0.9979±0.000 | 0.0067 | 0.0071 | matched 2L+c_top |
| 38 | 1 − 1/E_27 (E ≈ 20.073341983; 98-digit num) | 0.95018269 | 0.95024215 | 0.4088 | 9.7845 | 10.2678 | 0.01056 | 0.01059 | 0.9981±0.000 | 0.0067 | 0.0071 | matched 2L+c_top |
| 39 | 1 − 1/E_28 (E ≈ 20.590996442; 98-digit num) | 0.95143508 | 0.95149153 | 0.3983 | 10.0434 | 10.5273 | 0.01002 | 0.01006 | 0.9981±0.000 | 0.0067 | 0.0071 | matched 2L+c_top |
| 40 | 1 − 1/E_29 (E ≈ 21.108726649; 99-digit num) | 0.95262623 | 0.95267988 | 0.3883 | 10.3023 | 10.7867 | 0.00952 | 0.00956 | 0.9982±0.000 | 0.0068 | 0.0072 | matched 2L+c_top |
| 41 | 1 − 1/E_30 (E ≈ 21.626521298; 104-digit num) | 0.95376048 | 0.95381153 | 0.3787 | 10.5613 | 11.0461 | 0.00906 | 0.00910 | 0.9983±0.000 | 0.0068 | 0.0072 | matched 2L+c_top |

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
