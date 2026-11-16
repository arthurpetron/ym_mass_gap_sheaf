# DESIGN (numerical only, Lean pending): undershooting AF nome schedule and physical-units bound, 2026-11-15

**Status: NUMERICAL DESIGN ONLY. No Lean in this commit.** The Lean files were written but could not
be compiled. The box was restored at about 16:51 PST (uptime reset), and `/workspace/ym_v3seed_wt/lean/.lake/build`
was lost. 1,876 of the 3,368 modules in the import closure of `DyadicCrossoverSchedule` / `NomeSchedule` now have no
`.olean`: the overlay symlinks dangle, and only 1,485 modules survive in `/workspace/v3logs/box_build_partial`.
A rebuild under the `-M ≤ 6144` rule was tried. The first dependency built (`Continuum/FourAnchorWindowRetune`)
already fails at `-M 4096` with "(kernel) excessive memory consumption", and the repo lakefile notes that some
certificates need up to 32 GiB. The Lean drafts are kept outside the repo, in `/workspace/v3logs/us/drafts/`.
**`δ_min = 0` (ℓ ≤ 1) is only a NECESSARY condition: it removes the README §8 obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report
(numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8,
AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

## Schedule (index-consistent with `scaleChain`, no offset)
* `j < 6`: `dyTable` (1/64 … 147/200), unchanged, so the join is at j = 6 with `w_6 = 779/1000`.
* `j = 6..10` (data window, β_naive 2.00 → 2.98): five finer steps, 779/1000, 1987/2500, 81081/100000,
  205731/250000, 417199/500000.
  * Each step's two-loop length s_j is chosen so that ∫ℓ′_max over the step = 1 − 0.03·g_j⁴.
  * ℓ′ bands, from README §8 (central ± 1σ): [0.90, 1.40] for β < 2.2 (extrapolated); [0.90, 1.02] for 2.2–2.3;
    [1.24, 1.36] for 2.3–2.4; [1.27, 1.39] for 2.4–2.6; [1.09, 1.23] for 2.6–2.7; [1.16, 1.34] for 2.7–2.85;
    [1 − 0.0077 g⁴, 1 + 0.021 g⁴] for β > 2.85.
  * The window needs 5 steps (two-loop τ 0 → 3.56); the old schedule spent 3.56 two-loop doublings there.
* `j ≥ 11`: `w_j = 1 − 1941658544/usF(j−11)`, with an explicit Nat recursion:
  `usF 0 = 12577219337`, `usF(i+1) = usF i + (10⁹ − ⌊7·10⁹/((i+8)(i+16))⌋) + ⌊608078·10¹²/usF i⌋ + ⌊34·10²⁵/usF i²⌋ + 1`.
  * It tracks two-loop running (dD/dτ = 1/(1 − κ′/D), κ′ = κ/ln2 = 0.608078, w = e^{−A/D}) with
    two-loop step s = 1 − 7/((i+8)(i+16)).
  * 7/((i+8)(i+16)) = c_eff·g⁴ with c_eff ∈ [0.0290, 0.0304] for j = 11..1200.
  * The recursion's own error in s is between −0.5 % and +3.9 % of u_design up to j ≈ 1010.
* Checked in python with exact rationals (Lean statements drafted, not compiled):
  * strictly monotone;
  * `DyadicRGStep` on every step j < 210, including 5→6 and 10→11;
  * `NomeSchedule` modulus `11 + 1941658544·ε.den` (from usF i ≥ 12577219337 + i).
* `DyadicRGStep` (`DyadicCrossoverSchedule.lean:47`) bounds a step only from above (SC: w_f² ≤ w_c; AF: D grows by
  at most 3/2), so it accepts ℓ < 1 and no variant is needed.

## Choice of c (bracket)
* For ℓ_max = s(1 + 0.021 g⁴) ≤ 1 in the tail, c must exceed 0.021 (the naive/matched-map mismatch, the largest
  known residual). c = 0.0077 (three-loop) is not enough.
* c = 0.03 gives (1 − ℓ_max)/g⁴ ≥ 0.0081 for every tail step up to j = 1009.
  * The slack ℓ_min − (1 − u_phys) ≥ 0.0047 g⁴ in the tail; it is 0.0013 g⁴ at j = 10 (data window).
* Cost: u_phys ≈ (c + 0.0077 + slack)·g⁴, with K_p = 10, c_phys ∈ [0.041, 0.044]. The tail factor is 17/7, i.e. 1.28
  doublings. c = 0.025 halves the margin; c = 0.04 roughly doubles it but costs about 1.35× more tail factor in log₂.

## Physical units (statement drafted for Lean; numbers exact)
* Abstract lemma (drafted). Assume:
  * a_i ≥ 0 (spacings);
  * ρ_i = 1 + u_i;
  * weights ω_i ≥ 1;
  * the spacing hypothesis `hspacing_OPEN`: 2·a_{i+1} ≤ ρ_i·a_i;
  * the weight step ρ_i·ω_{i+1} ≤ ω_i.

  Then 2ⁿ·a_n ≤ ω_0·a_0 for all n. If additionally floor ≤ 2ⁿ·M_n with M_n ≥ 0, then floor·a_n ≤ (ω_0·a_0)·M_n,
  i.e. M_n/a_n ≥ floor/(ω_0·a_0).
* Link to ℓ: if ℓ_i = log₂(a_i/a_{i+1}) ≥ 1 − u_i with 0 ≤ u_i ≤ 1, then 2^{u} ≤ 1 + u. This holds because 2^u is
  **convex** (not concave), so it lies below its chord 1 + u on [0,1]. Hence a_i/a_{i+1} ≥ 2/2^{u_i} ≥ 2/(1+u_i),
  which is `hspacing_OPEN`.
* Rational u_i and ρ_i for this schedule:
  * crossover, from the TM ℓ of §7: 1/100, 1/40, 1/5, 1/2, 2/3, 4/5;
  * data window, 1 − ℓ_min rounded up to 0.01: 0.44, 0.23, 0.17, 0.19, 0.15;
  * tail (i ≥ 11, m = i − 4): ρ_i = (m+10)(m+1)/(m(m+11)), i.e. u_i = 10/(m(m+11)).
  * Tail weight ω_i = (m+10)/m, decreasing to 1. The weight step holds with equality:
    (m+10)(m+1)·(m+11)·m = (m+10)·m(m+11)·(m+1).
  * The head weights are exact backward products.
* **U (as a rational product):**
  P = ω_0 = ∏_{i<11} ρ_i · 17/7 = 96256076646951/2500000000000 ≈ 38.502, i.e. U = log₂ P ≈ 5.267.
  * Crossover: 5.590 (2.48 doublings).
  * Data window: 2.836 (1.50).
  * Tail: 17/7 ≈ 2.429 (1.28).
* **Physical statement (on the crossover instance: j0 = 0, k = 6, η = 1/64, floor 114517/5000000 as before).**
  Under `hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN` and `hspacing_OPEN`, for every n:

  latticeMargin_n / a_n ≥ (114517/5000000) / (P·a_0) = 114517/(5000000·P·a_0) ≈ 5.95·10⁻⁴ / a_0.

  Measured from a_6 instead (the start of the AF part, P_AF = 2.836·2.429 ≈ 6.89), the factor is about 6.9, not 38.5.
  The crossover factor 5.59 comes from finite-cube TM masses in the strong-coupling region and is the least physical part.

## Sequence (Task 3): w_j, two-loop g² and β = 4/g², two-loop step s_j, u design (c·g⁴; tail 7/((j−3)(j+5))),
intended ℓ = 1 − u_design, the model band of ℓ (data ℓ′ bands; tail [1 − 0.0077 g⁴, 1 + 0.021 g⁴]·s), the three-loop
(Wilson, ℓ − 1 = +0.0077 g⁴ per two-loop doubling) ℓ, and u_phys
| j | w_j (exact) | w_j | g²_j (2L) | β_j | s_j: two-loop doublings j→j+1 | u_j design | ℓ_j intended (=1−u design; data steps: band max) | ℓ_j band [min, max] (model) | ℓ_j three-loop | u_j phys (ρ_j − 1) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 1/64 | 0.015625 | – | – | crossover | – | – | TM ℓ = 1.000 (§7) | – | 0.010 |
| 1 | 1/8 | 0.125000 | – | – | crossover | – | – | TM ℓ = 0.985 (§7) | – | 0.025 |
| 2 | 7/20 | 0.350000 | – | – | crossover | – | – | TM ℓ = 0.839 (§7) | – | 0.200 |
| 3 | 14/25 | 0.560000 | – | – | crossover | – | – | TM ℓ = 0.507 (§7) | – | 0.500 |
| 4 | 67/100 | 0.670000 | – | – | crossover | – | – | TM ℓ = 0.378 (§7) | – | 0.667 |
| 5 | 147/200 | 0.735000 | – | – | crossover | – | – | TM ℓ = 0.25 / 0.42 / 1.30 (§7) | – | 0.800 |
| 6 | 779/1000 | 0.779000000 | 1.99795 | 2.0020 | 0.62876 | 0.11975 | 0.88025 | [0.56588, 0.88027] | (data window) | 0.44000 |
| 7 | 1987/2500 | 0.794800000 | 1.83732 | 2.1771 | 0.74872 | 0.10127 | 0.89873 | [0.77748, 0.89872] | (data window) | 0.23000 |
| 8 | 81081/100000 | 0.810810000 | 1.67777 | 2.3841 | 0.65991 | 0.08445 | 0.91555 | [0.83635, 0.91554] | (data window) | 0.17000 |
| 9 | 205731/250000 | 0.822924000 | 1.55913 | 2.5655 | 0.71716 | 0.07293 | 0.92707 | [0.82016, 0.92709] | (data window) | 0.19000 |
| 10 | 417199/500000 | 0.834398000 | 1.44836 | 2.7617 | 0.80791 | 0.06293 | 0.93707 | [0.85266, 0.93708] | (data window) | 0.15000 |
| 11 | 1 − 1941658544/12577219337 | 0.845621000 | 1.34147 | 2.9818 | 0.94769 | 0.05469 | 0.94531 | [0.93560, 0.98066] | 0.95978 | 0.07937 |
| 12 | 1 − 1941658544/13573028770 | 0.856947290 | 1.23503 | 3.2388 | 0.95609 | 0.04575 | 0.95425 | [0.94569, 0.98445] | 0.96649 | 0.06579 |
| 13 | 1 − 1941658544/14573923150 | 0.866771732 | 1.14384 | 3.4970 | 0.96257 | 0.03889 | 0.96111 | [0.95354, 0.98719] | 0.97160 | 0.05556 |
| 14 | 1 − 1941658544/15578358722 | 0.875361803 | 1.06494 | 3.7561 | 0.96769 | 0.03349 | 0.96651 | [0.95978, 0.98924] | 0.97559 | 0.04762 |
| 15 | 1 − 1941658544/16585300400 | 0.882928949 | 0.99608 | 4.0157 | 0.97180 | 0.02917 | 0.97083 | [0.96483, 0.99081] | 0.97877 | 0.04132 |
| 16 | 1 − 1941658544/17594033445 | 0.889641079 | 0.93550 | 4.2758 | 0.97516 | 0.02564 | 0.97436 | [0.96897, 0.99205] | 0.98135 | 0.03623 |
| 17 | 1 − 1941658544/18604052392 | 0.895632494 | 0.88180 | 4.5362 | 0.97794 | 0.02273 | 0.97727 | [0.97241, 0.99305] | 0.98348 | 0.03205 |
| 18 | 1 − 1941658544/19614992709 | 0.901011508 | 0.83390 | 4.7967 | 0.98028 | 0.02029 | 0.97971 | [0.97530, 0.99386] | 0.98526 | 0.02857 |
| 19 | 1 − 1941658544/20626587224 | 0.905866224 | 0.79091 | 5.0575 | 0.98226 | 0.01823 | 0.98177 | [0.97776, 0.99453] | 0.98676 | 0.02564 |
| 20 | 1 − 1941658544/21638637502 | 0.910268909 | 0.75212 | 5.3183 | 0.98395 | 0.01647 | 0.98353 | [0.97986, 0.99509] | 0.98803 | 0.02315 |
| 21 | 1 − 1941658544/22650994544 | 0.914279325 | 0.71695 | 5.5792 | 0.98541 | 0.01496 | 0.98504 | [0.98168, 0.99557] | 0.98913 | 0.02101 |
| 22 | 1 − 1941658544/23663545493 | 0.917947269 | 0.68492 | 5.8401 | 0.98667 | 0.01365 | 0.98635 | [0.98326, 0.99598] | 0.99008 | 0.01916 |
| 23 | 1 − 1941658544/24676204277 | 0.921314538 | 0.65563 | 6.1010 | 0.98778 | 0.01250 | 0.98750 | [0.98464, 0.99633] | 0.99091 | 0.01754 |
| 24 | 1 − 1941658544/25688904930 | 0.924416453 | 0.62874 | 6.3619 | 0.98875 | 0.01149 | 0.98851 | [0.98586, 0.99664] | 0.99164 | 0.01613 |
| 25 | 1 − 1941658544/26701596734 | 0.927283055 | 0.60397 | 6.6228 | 0.98961 | 0.01061 | 0.98939 | [0.98694, 0.99691] | 0.99229 | 0.01488 |
| 26 | 1 − 1941658544/27714240644 | 0.929940042 | 0.58108 | 6.8837 | 0.99038 | 0.00982 | 0.99018 | [0.98790, 0.99714] | 0.99286 | 0.01377 |
| 27 | 1 − 1941658544/28726806630 | 0.932409524 | 0.55987 | 7.1446 | 0.99106 | 0.00911 | 0.99089 | [0.98875, 0.99735] | 0.99337 | 0.01279 |
| 28 | 1 − 1941658544/29739271669 | 0.934710622 | 0.54015 | 7.4054 | 0.99167 | 0.00848 | 0.99152 | [0.98952, 0.99754] | 0.99382 | 0.01190 |
| 29 | 1 − 1941658544/30751618222 | 0.936859955 | 0.52177 | 7.6662 | 0.99222 | 0.00792 | 0.99208 | [0.99021, 0.99771] | 0.99424 | 0.01111 |
| 30 | 1 − 1941658544/31763833060 | 0.938872033 | 0.50461 | 7.9269 | 0.99272 | 0.00741 | 0.99259 | [0.99084, 0.99786] | 0.99461 | 0.01040 |
| 31 | 1 − 1941658544/32775906362 | 0.940759577 | 0.48854 | 8.1876 | 0.99317 | 0.00694 | 0.99306 | [0.99140, 0.99800] | 0.99494 | 0.00975 |
| 32 | 1 − 1941658544/33787831006 | 0.942533791 | 0.47347 | 8.4483 | 0.99358 | 0.00652 | 0.99348 | [0.99192, 0.99812] | 0.99525 | 0.00916 |
| 33 | 1 − 1941658544/34799602017 | 0.944204576 | 0.45930 | 8.7089 | 0.99396 | 0.00614 | 0.99386 | [0.99239, 0.99823] | 0.99552 | 0.00862 |
| 34 | 1 − 1941658544/35811216129 | 0.945780715 | 0.44596 | 8.9695 | 0.99430 | 0.00579 | 0.99421 | [0.99282, 0.99833] | 0.99578 | 0.00813 |
| 35 | 1 − 1941658544/36822671438 | 0.947270025 | 0.43337 | 9.2300 | 0.99461 | 0.00547 | 0.99453 | [0.99321, 0.99843] | 0.99601 | 0.00768 |
| 36 | 1 − 1941658544/37833967128 | 0.948679489 | 0.42147 | 9.4905 | 0.99490 | 0.00517 | 0.99483 | [0.99358, 0.99851] | 0.99623 | 0.00727 |
| 37 | 1 − 1941658544/38845103246 | 0.950015359 | 0.41022 | 9.7509 | 0.99517 | 0.00490 | 0.99510 | [0.99391, 0.99859] | 0.99642 | 0.00689 |
| 38 | 1 − 1941658544/39856080526 | 0.951283254 | 0.39955 | 10.0113 | 0.99541 | 0.00465 | 0.99535 | [0.99422, 0.99867] | 0.99661 | 0.00654 |
| 39 | 1 − 1941658544/40866900245 | 0.952488235 | 0.38942 | 10.2717 | 0.99564 | 0.00442 | 0.99558 | [0.99451, 0.99873] | 0.99677 | 0.00621 |
| 40 | 1 − 1941658544/41877564109 | 0.953634874 | 0.37980 | 10.5320 | 0.99585 | 0.00420 | 0.99580 | [0.99477, 0.99879] | 0.99693 | 0.00591 |
| 41 | 1 − 1941658544/42888074154 | 0.954727309 | 0.37064 | 10.7923 | 0.99605 | 0.00400 | 0.99600 | [0.99502, 0.99885] | 0.99708 | 0.00563 |

Caveats: numerical only. The ℓ′ bands come from README §8 with ASSUMED FHK error bars. β < 2.2 is extrapolated.
Above 2.85 the band is model-based; the heat-kernel b2 sign is unknown and covered by ±0.0077 g⁴. One repo step is
assumed to equal one TM step.
