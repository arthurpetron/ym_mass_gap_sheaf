# prod6 A2: weak-coupling check of the twisted tree-level normalisation Nhat_T(c, L) (a2_analysis.py)

MC evidence only -- not a proof, not a bound. R = g2_TGF/g0^2 with g2_TGF = t^2<E_clover>/Nhat_T(c,L), g0^2 = 4/beta. Bootstrap 4000 replicas, moving blocks of 10 configurations per chain (same indices for both c).

delta_meas(L) = 2 R(beta=40) - R(beta=20) - 1 = delta_tree(L) - 0.02 b(L) + O(g0^6), where R - 1 = delta_tree + a g0^2 + b g0^4; A(L) = (R20 - R40)/0.1 = a + 0.3 b.

## Ensembles: R per (L, beta), pooled chains; error comparison (bootstrap / Gamma / binned jackknife); tau_int per chain

| L | beta | chains | N | R c=0.3 [boot] (Gamma) {jk} | R c=0.4 [boot] (Gamma) {jk} | tau_int c=0.3 / 0.4 per chain | rho(c) |
|---|---|---|---|---|---|---|---|
| 8 | 20 | 1 | 1500 | 1.09163 [184] (187) {216} | 1.09630 [358] (357) {448} | 0.50/0.51 | 0.92 |
| 8 | 40 | 1 | 3000 | 1.04012 [126] (123) {145} | 1.04204 [230] (227) {267} | 0.50/0.50 | 0.92 |
| 12 | 20 | 1 | 1000 | 1.10284 [235] (232) {245} | 1.10974 [473] (478) {470} | 0.50/0.53 | 0.92 |
| 12 | 40 | 1 | 2000 | 1.05089 [161] (163) {157} | 1.05589 [300] (305) {285} | 0.55/0.56 | 0.91 |
| 16 | 20 | 1 | 800 | 1.10750 [247] (259) {217} | 1.11779 [458] (470) {379} | 0.50/0.50 | 0.92 |
| 16 | 40 | 1 | 1600 | 1.05002 [176] (176) {177} | 1.05276 [364] (373) {367} | 0.50/0.62 | 0.92 |
| 24 | 20 | 3 | 600 | 1.11236 [289] (317) {315} | 1.11442 [563] (634) {600} | 0.66/0.86, 0.50/0.50, 0.50/0.50 | 0.91 |
| 24 | 40 | 3 | 1200 | 1.05852 [210] (212) {199} | 1.06214 [408] (415) {402} | 0.52/0.63, 0.50/0.50, 0.50/0.52 | 0.92 |

## L=24: chain means and between-chain consistency (chi2 of the chain means about their pooled mean, Gamma errors per chain)

| beta | c | chain means (Gamma err) | chi2/dof | p | between-chain error of the pooled mean | bootstrap error |
|---|---|---|---|---|---|---|
| 20 | 0.3 | 1.12526(615), 1.10402(506), 1.10781(518) | 7.89/2 | 0.019 | 0.00654 | 0.00289 |
| 20 | 0.4 | 1.13289(1310), 1.10201(982), 1.10836(970) | 3.97/2 | 0.137 | 0.00941 | 0.00563 |
| 40 | 0.3 | 1.05580(380), 1.05776(330), 1.06200(390) | 1.36/2 | 0.506 | 0.00183 | 0.00210 |
| 40 | 0.4 | 1.05978(782), 1.05737(637), 1.06927(729) | 1.61/2 | 0.447 | 0.00363 | 0.00408 |

## delta_meas(L) = 2 R40 - R20 - 1 and A(L) = (R20 - R40)/0.1  [central(bootstrap error)]

| L | delta c=0.3 | z | delta c=0.4 | z | delta(0.4) - delta(0.3) corr. | A c=0.3 | A c=0.4 | L=24 Birge-inflated delta c=0.3 / 0.4 | Nhat_T/N_T - 1 (0.3 / 0.4): delta if the continuum N_T were the truth |
|---|---|---|---|---|---|---|---|---|---|
| 8 | -0.0114(32) | -3.6 | -0.0122(59) | -2.1 | -0.0008(33) | 0.5151(227) | 0.5425(431) | - | -0.0650 / -0.0359 |
| 12 | -0.0011(40) | -0.3 | +0.0020(76) | +0.3 | +0.0031(42) | 0.5194(283) | 0.5385(556) | - | -0.0277 / -0.0156 |
| 16 | -0.0075(43) | -1.7 | -0.0123(86) | -1.4 | -0.0048(50) | 0.5748(303) | 0.6503(587) | - | -0.0154 / -0.0087 |
| 24 | +0.0047(51) | +0.9 | +0.0099(99) | +1.0 | +0.0052(56) | 0.5384(358) | 0.5228(695) | +0.0047(71) / +0.0099(114) | -0.0068 / -0.0039 |

## Fits of delta_meas over L = 8, 12, 16, 24 (diagonal: ensembles independent)

| c | errors | zero: chi2/4 (p) | constant d0: value, chi2/3 (p) | d0 + d2/L^2: d0, d2, chi2/2 (p) | d0 + d2/L^2: d2 z | max pairwise |delta(L)-delta(L')| z |
|---|---|---|---|---|---|---|
| 0.3 | bootstrap | 16.7 (0.002) | -0.0056(20), 8.9 (0.031) | +0.0019(37), -0.838(355e-3), 3.2 (0.200) | -2.4 | 2.7 |
| 0.3 | L24 Birge-inflated | 16.3 (0.003) | -0.0064(20), 6.7 (0.080) | +0.0007(41), -0.751(379e-3), 2.8 (0.246) | -2.0 | 2.1 |
| 0.4 | bootstrap | 7.4 (0.118) | -0.0054(37), 5.3 (0.151) | +0.0037(73), -1.001(681e-3), 3.1 (0.214) | -1.5 | 1.9 |
| 0.4 | L24 Birge-inflated | 7.1 (0.130) | -0.0060(38), 4.7 (0.195) | +0.0028(76), -0.930(703e-3), 2.9 (0.233) | -1.3 | 1.7 |

## Sensitivity: delta_meas if g2 were normalised with the continuum N_T(c) instead (same data); the measured delta vs this alternative

| L | c=0.3: delta(cont) | (cont - lattice)/sigma | c=0.4: delta(cont) | (cont - lattice)/sigma |
|---|---|---|---|---|
| 8 | -0.0757(30) | -20.2 | -0.0476(57) | -6.0 |
| 12 | -0.0288(39) | -7.0 | -0.0136(75) | -2.1 |
| 16 | -0.0227(42) | -3.6 | -0.0209(85) | -1.0 |
| 24 | -0.0021(51) | -1.3 | +0.0060(99) | -0.4 |
