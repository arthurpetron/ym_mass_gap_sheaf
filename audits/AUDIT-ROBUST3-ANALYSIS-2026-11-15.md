# Robust3: all-j analysis and numerics (2026-11-15). ANALYSIS, NOT A LEAN THEOREM

Covers `Robust3UndershootAfSchedule` (79883f3e) and `Robust3UndershootPhysicalUnits` (this commit).

## Lean file: Robust3UndershootPhysicalUnits.lean (67 lines, PROVED part)
- `r3Rho` :38, `r3Omega` :41 (the same rational family as Robust2), `r3_weight` :43, `r3_omega_ge_one` :45.
- `r3P = 127996107199191/1562500000000` :48. `r3P_value` :51: ω_0 = r3P exactly and 81 < r3P < 82 (decide).
- `robust3_spacing_bound` :60: under hspacing_OPEN, 2ⁿ·a_n ≤ P₃·a_0. P₃ ≈ 81.9175, U₃ ≈ 6.356.
- Axioms: r3P_value none; robust3_spacing_bound ⊆ {propext, Quot.sound}. 1.0 s, 1704 MiB, zero warnings.

## How A enters (assumption statement)
No Lean statement involves A = 3π²/(22 ln 2). The schedule uses B_n = 22·L_n/(3·P_n), n = j + 3, with:
- L_n = Σ_{k≤n} 1/(k 2^k) ≤ ln 2, and ln 2 − L_n ≤ 2^{−n}/(n+1);
- P_n = 18(Σ_{k≤n} t_k + (4/3)t_{n+1}) ≥ π², with t_k = 1/(k²C(2k,k)) and t_{k+1}/t_k = k²/((2k+1)(2k+2)) < 1/4. So
  0 ≤ P_n − π² ≤ 6 t_{n+1} ≤ 6·4^{−n−1}.

Hence A'_n := 1/B_n ≥ A (rounded UP), and 0 ≤ δ_n := 1 − A·B_n ≤ 1.5·2^{−n}. These standard series facts are
assumed, not formalised. κ'_n = (51/121)/L_n ≥ κ' = κ/ln 2, with relative error ≤ 2^{−n}. This replaces the fixed
A' = 1.941658544 (rounded down, ε_A = +1.6e-10) of Robust2. A FIXED rational A' cannot work for all j:
- A' < A gives ℓ − 1 → ε_A > 0 (Numerics §11).
- A' > A gives 1 − ℓ → |ε_A|, a constant, while ρ − 1 ~ 13/m², so spacing (and P) fails for m ≳ (19/|ε_A|)^{1/2}.

So A'_n must converge to A faster than 1/m². It does (2^{−n}).

## Analytic all-j argument (k = j − 11, m = j − 7, D = E·A'_n)
1. **Exact increments.** Since H_{m+4} − H_{m+3} = 1/(m+4), Δ[(H_m+1)/m] = −(H_m + 1/(m+1))/(m(m+1)), and
   Δ[Σ_{t=m}^{m+16} 1/t] = 1/(m+17) − 1/m:
   ΔD = 1 + κ'/(m+4) − κ'²(H_m + 1/(m+1))/(m(m+1)) − 16/(m(m+17)) + r_n, where |r_n| ≤ 2^{−n}(1 + ln m).
   There are no floors: every term is an exact rational, so the resolution is exact at every j.
2. **Ideal step.** Two-loop ℓ = 1 holds iff the effective D_eff = A·E = D(1 − δ_n) advances by
   Δ*(D) = 1 + κ'/D + e2/D² + O(D⁻³), with e2 = 0.34 − E_§11 = 0.3419 (Numerics §11 expansion).
   Then ℓ_2L − 1 = (ΔD_eff − Δ*)(1 + O(1/D)).
3. **The log terms cancel exactly.** D = m + C + κ'(ln m + γ) + O(ln m/m), with C = 9989/2000. So
   κ'/(m+4) − κ'/D = κ'(C − 4 + κ'(ln m + γ))/m² + O(ln²m/m³), and the κ'² term contributes −κ'²(ln m + γ)/m² +
   O(ln m/m³). The two-loop log behaviour is therefore tracked for ALL j: H_m is exact and no term dies out. The
   residual is
   ΔD_eff − Δ* = −[16 + e2 − κ'(C − 4)]/m² + R(m), with R(m) = O(ln²m/m³) + O(m·2^{−m}),
   and 16 + 0.3419 − 0.6047 = 15.737.
4. **Limits.** g⁴ = 64A²/D²·(1 + O(1/D)) and D/m → 1, so (1−ℓ_2L)/g⁴ → 15.737/(64A²) = **0.06522**. The model
   shifts are those of Numerics §11: 3L ∓0.00773; matched −0.01271; c held −0.0392 with 2σ 0.0056; c trend → 0.
   | model | limit (1−ℓ−2σ)/g⁴ | numerics at j = 10⁷ |
   |---|---|---|
   | naive 2L (and FHK, BSS, slope models, c trend) | 0.06522 | 0.06522 |
   | naive 3L(+q) / 3L(−q) | 0.05749 / 0.07295 | 0.05749 / 0.07295 |
   | matched 2L (and matched BSS95, matched c trend) | 0.05252 | 0.05252 |
   | matched 3L(+q) / 3L(−q) | 0.04479 / 0.06025 | 0.04479 / 0.06025 |
   | naive 2L + c held | 0.0204 | 0.02041 |
   | **matched 2L + c held** | **0.0077** | **0.00770** |
5. **Error bounds.** The surrogate errors are δ_n and the κ'_n error. In g⁴ units they contribute at most
   (D²/64A²)·(m+1)·3·2^{−n} ≤ m³2^{−m}/3000 ≤ 2e-3 at m = 4, < 1e-6 for m ≥ 40, and → 0. The rounding error is 0
   (exact rationals). The O(ln²m/m³) remainder: the observed deviation from the limit is ≤ 1.1e-4 g⁴ for j ≥ 300
   (0.00781 at j = 1970 vs 0.00770), consistent with K·ln²m/m with K ≈ 0.004. So for every model,
   1 − ℓ − 2σ ≥ c'·g⁴ with c' = 0.0077 − 0.004·ln²m/m − m³2^{−m}/3000 ≥ **0.0074·g⁴ for all j ≥ 2000**.
   The remainder constant K is a numerical fit, not a proof. Below j = 2000 every j is checked directly.
6. **Envelope and floor inactive.** ΔE = ΔD·B_{n+1} + D·(B_{n+1} − B_n), with B increasing (L_n ↑, P_n ↓). ΔD ≥ 1 −
   16/(m(m+17)) − κ'²(H_m+1)/m² − |r_n| ≥ 1 − 0.191 − 0.06 − 0.01 > 0.7 for m ≥ 4, so ΔE > 0.36. Numerically the
   minimum is 0.515. Also E ≥ (m + C)·B_14 > (k+1)/4. So r3E_k = ecomp k for all k.
7. **Spacing.** ρ − 1 = 13/(m(m+14)). The worst need is naive 3L(−q): 2^{1−ℓ_lo} − 1 → ln2·0.07295·64A²/m². So the
   ratio → 13/(ln2·0.07295·64A²) = **1.0655 > 1**. It is approached from above (1.1508 at j11 … 1.0666 at
   j1993, 1.0655 at 10⁷). The P₃ chain is unchanged (P₃ = P₂).

## Numerical verification (15 Numerics models, exact β_char)
- Evaluator: every j from 6 to 2000 uses `/workspace/v3logs/rob2/eval15.py` (Numerics `t2common` read-only, 3000/300 MC,
  exact β_char via scaled Bessel, double precision on the exact rational w_j).
- j = 2000..10⁷: 150 log-spaced points with mpmath at 60 digits (`/workspace/v3logs/rob3/mpmodels.py`, mp besseli root
  for β_char, the exact closed form of E in mp). For β > 2.85 the data and slope models reduce exactly to 2L,
  with σ = 0 (as in Numerics' code).
- The mp and Fraction values of w agree exactly at j = 1000 and 2000.

Worst 1 − ℓ − 2σ (window absolute, tail /g⁴; first six columns: min and its j; last four: min over the sampled points):
| model | j6-10 abs | j11-20 | j21-41 | j42-80 | j81-300 | j301-2000 | 2e3–1e4 | 1e4–1e5 | 1e5–1e6 | 1e6–1e7 |
|---|---|---|---|---|---|---|---|---|---|---|
| naive FHK92 | 0.0269 (j10) | 0.0670 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| naive BSS95 | 0.0545 (j8) | 0.0670 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| naive BSS slope (2L ext) | 0.1574 (j8) | 0.0670 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| naive BSS slope (hold ext) | 0.1381 (j10) | 0.0670 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| matched BSS95 | 0.0301 (j7) | 0.0418 (j18) | 0.0422 (j21) | 0.0466 (j42) | 0.0495 (j81) | 0.0519 (j301) | 0.05252 | 0.05252 | 0.05252 | 0.05252 |
| naive 2L | 0.2099 (j10) | 0.0670 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| naive 3L(+q) | 0.1986 (j10) | 0.0602 (j20) | 0.0558 (j41) | 0.0558 (j43) | 0.0564 (j81) | 0.0574 (j301) | 0.05752 | 0.05750 | 0.05749 | 0.05749 |
| naive 3L(-q) | 0.2243 (j10) | 0.0748 (j20) | 0.0710 (j40) | 0.0710 (j42) | 0.0717 (j81) | 0.0728 (j301) | 0.07298 | 0.07296 | 0.07295 | 0.07295 |
| matched 2L | 0.1348 (j10) | 0.0418 (j18) | 0.0422 (j21) | 0.0466 (j42) | 0.0495 (j81) | 0.0519 (j301) | 0.05252 | 0.05252 | 0.05252 | 0.05252 |
| matched 3L(+q) | 0.1250 (j10) | 0.0360 (j19) | 0.0363 (j21) | 0.0399 (j42) | 0.0422 (j81) | 0.0443 (j301) | 0.04481 | 0.04479 | 0.04479 | 0.04479 |
| matched 3L(-q) | 0.1469 (j10) | 0.0483 (j18) | 0.0489 (j21) | 0.0538 (j42) | 0.0569 (j81) | 0.0596 (j301) | 0.06024 | 0.06025 | 0.06025 | 0.06025 |
| naive 2L+c_top | 0.1406 (j10) | 0.0261 (j20) | 0.0198 (j41) | 0.0196 (j56) | 0.0198 (j81) | 0.0204 (j301) | 0.02044 | 0.02042 | 0.02041 | 0.02041 |
| naive 2L+c_trend | 0.1180 (j6) | 0.0657 (j20) | 0.0632 (j40) | 0.0632 (j42) | 0.0639 (j81) | 0.0651 (j301) | 0.06525 | 0.06523 | 0.06522 | 0.06522 |
| matched 2L+c_top | 0.0752 (j10) | 0.0068 (j20) | 0.0066 (j24) | 0.0068 (j42) | 0.0073 (j81) | 0.0078 (j1970) | 0.00774 | 0.00771 | 0.00770 | 0.00770 |
| matched 2L+c_trend | 0.0878 (j6) | 0.0403 (j16) | 0.0418 (j21) | 0.0466 (j42) | 0.0495 (j81) | 0.0519 (j301) | 0.05252 | 0.05252 | 0.05252 | 0.05252 |
| spacing (ρ−1)/(2^{1−ℓ_lo}−1) | (head ρ; ≥1.033 at j6) | 1.1508 | 1.1244 | 1.0979 | 1.0742 | 1.0666 | 1.0657 | 1.0655 | 1.0655 | 1.0655 |

The thinnest margin is matched + c held: 0.00659·g⁴ at j24 (0.00678 at j20), compared with Robust2's 0.0061 at j20.
Every model passes at every checked j up to 10⁷. Matched + c held is 0.00770·g⁴ for j ≥ 10⁵, with no decay.
The window worst is 0.0269 (j10, FHK), unchanged.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
