# P9 addendum to P7_FINAL: Polyakov-sector split (beta 2.95, 48^3x48, side 8)

Sector = sign of the direction-3 smeared spatial Polyakov loop at rho=1.00 (P7 logs it per measurement; rho=1.5 has the same sign history). N=240: P3<0 in 236 meas, P3>0 in 4 meas; 4 sign changes; contiguous segments of length [114, 3, 105, 1, 17]. Bins of 10 meas inside each contiguous segment (remainders dropped), jackknife over bins. E1 = vacuum subtraction with the subset mean; E3f = far-lag Q(n)-Q(Lt/2); E3d = differenced. 'sym' = sector-symmetrized: Q and <O> averaged with EQUAL weight over the two sectors (what an ergodic run would give, since the center transformation maps one sector onto the other and leaves contractible loops invariant).

## Reading (caveated)
* **A sign split is not possible.** The dir-3 loop was NEGATIVE in 236 of 240 meas, not ~115: segments 114 (−), 3 (+), 105 (−), 1 (+), 17 (−). The positive sector has 4 meas (no full bin), so the "P3 > 0" and sector-symmetrized rows cannot be filled from data.
* **A sector-symmetrized estimator is the same as the single-sector one** for every observable used here. The Z2 center transformation on the dir-3 links of one plane flips the sign of P3 and leaves every contractible Wilson loop (and so O(t), W, eps) invariant. So the + sector has the identical distribution of O, and equal-weight symmetrization changes nothing in expectation. The sign is not the issue.
* **The physical issue is the magnitude.** The dir-3 loop stayed ORDERED (mean P3 = −0.112, mean |P3| = 0.113), while dirs 1 and 2 fluctuate around ~0 with 26-28 sign changes. This is a finite-volume, center-symmetry-breaking-like slow mode. The magnitude splits are the relevant check:
  * **eps*side** is insensitive to every split: 2.49-2.81 across stretches and terciles at rho=1, all within ~1.5 sigma of 2.63(8). The ~2.4 sigma Ls=48 vs Ls=32 shift (2.63-2.66 vs 2.36(9)) is therefore not a sector artefact.
  * **W** varies between the two long negative stretches: rho=1 W E1 0.27(10) vs 0.52(9) (1.8 sigma), E3d 0.00(14) vs 0.52(14) (2.6 sigma). The |P3| terciles also trend: 0.27(10), 0.32(13), 0.47(12). So the slow mode probably inflates the true W error by ~1.5x over the quoted 0.068. W remains consistent with the Ls=32 value 0.355(58) within either stretch.
* The "all" row here (0.400(68)) differs slightly from P7_FINAL's 0.371(67) only because bins here never straddle a sign change and remainders are dropped (220 of 240 meas kept).

**Caveat:** the dir-3 sector flipped only 4 times, so each sector is ~2-3 independent stretches; the sector errors and the sector difference are themselves only roughly estimated (bins inside a stretch are correlated through the slow mode).


## rho = 0.75  (Ls=32 reference: W E1 0.351(69), E3f 0.31(10), E3d 0.30(11), eps*s 2.900(78))

| subset | bins | W E1 | W E3f | W E3d | eps*s E1 | eps*s E3f | eps*s E3d | R(s)/R(0) E1 | <O> |
|---|---|---|---|---|---|---|---|---|---|
| all (P7_FINAL, bin 10) | 22 | 0.408(82) | 0.431(92) | 0.27(20) | 3.128(89) | 3.10(10) | 3.63(15) | 0.090(18) | 0.77284 |
| P3 < 0 | 22 | 0.408(82) | 0.431(92) | 0.27(20) | 3.128(89) | 3.10(10) | 3.63(15) | 0.090(18) | 0.77284 |

Stretch 0 only (meas 0-113, 11 bins): W E1 0.26(15), W E3d -0.09(24), eps*s 3.16(16)
Stretch 2 only (meas 117-221, 10 bins): W E1 0.519(84), W E3d 0.62(18), eps*s 3.10(12)
Stretch 4 only (meas 223-239, 1 bins): W E1 n/a, W E3d n/a, eps*s n/a
Tercile split by |P3| (bins of 5 members, chronological): low (0.051): W 0.27(13), eps*s 3.17(12), <O> 0.77220 | mid (0.108): W 0.28(16), eps*s 3.18(13), <O> 0.77222 | high (0.179): W 0.49(12), eps*s 3.15(11), <O> 0.77378
Tercile split by max_d|P_d| (bins of 5 members, chronological): low (0.115): W 0.339(98), eps*s 3.267(94), <O> 0.77184 | mid (0.160): W 0.39(14), eps*s 3.01(12), <O> 0.77250 | high (0.215): W 0.31(13), eps*s 3.25(12), <O> 0.77386

## rho = 1.00  (Ls=32 reference: W E1 0.355(58), E3f 0.354(85), E3d 0.339(98), eps*s 2.363(92))

| subset | bins | W E1 | W E3f | W E3d | eps*s E1 | eps*s E3f | eps*s E3d | R(s)/R(0) E1 | <O> |
|---|---|---|---|---|---|---|---|---|---|
| all (P7_FINAL, bin 10) | 22 | 0.400(68) | 0.428(82) | 0.27(12) | 2.625(80) | 2.59(11) | 3.10(19) | 0.113(20) | 0.88427 |
| P3 < 0 | 22 | 0.400(68) | 0.428(82) | 0.27(12) | 2.625(80) | 2.59(11) | 3.10(19) | 0.113(20) | 0.88427 |

Stretch 0 only (meas 0-113, 11 bins): W E1 0.27(10), W E3d -0.00(14), eps*s 2.64(13)
Stretch 2 only (meas 117-221, 10 bins): W E1 0.517(94), W E3d 0.52(14), eps*s 2.63(12)
Stretch 4 only (meas 223-239, 1 bins): W E1 n/a, W E3d n/a, eps*s n/a
Tercile split by |P3| (bins of 5 members, chronological): low (0.051): W 0.27(10), eps*s 2.72(12), <O> 0.88378 | mid (0.108): W 0.32(13), eps*s 2.64(11), <O> 0.88380 | high (0.179): W 0.47(12), eps*s 2.652(75), <O> 0.88502
Tercile split by max_d|P_d| (bins of 5 members, chronological): low (0.115): W 0.310(90), eps*s 2.766(89), <O> 0.88339 | mid (0.160): W 0.433(95), eps*s 2.49(11), <O> 0.88404 | high (0.215): W 0.27(13), eps*s 2.81(11), <O> 0.88518

## rho = 1.25  (Ls=32 reference: W E1 0.343(58), E3f 0.370(85), E3d 0.383(89), eps*s 1.986(92))

| subset | bins | W E1 | W E3f | W E3d | eps*s E1 | eps*s E3f | eps*s E3d | R(s)/R(0) E1 | <O> |
|---|---|---|---|---|---|---|---|---|---|
| all (P7_FINAL, bin 10) | 22 | 0.384(68) | 0.417(91) | 0.267(97) | 2.250(79) | 2.21(12) | 2.68(20) | 0.134(25) | 0.93592 |
| P3 < 0 | 22 | 0.384(68) | 0.417(91) | 0.267(97) | 2.250(79) | 2.21(12) | 2.68(20) | 0.134(25) | 0.93592 |

Stretch 0 only (meas 0-113, 11 bins): W E1 0.272(99), W E3d 0.07(11), eps*s 2.27(11)
Stretch 2 only (meas 117-221, 10 bins): W E1 0.49(11), W E3d 0.42(14), eps*s 2.28(14)
Stretch 4 only (meas 223-239, 1 bins): W E1 n/a, W E3d n/a, eps*s n/a
Tercile split by |P3| (bins of 5 members, chronological): low (0.051): W 0.267(87), eps*s 2.37(12), <O> 0.93558 | mid (0.108): W 0.33(12), eps*s 2.229(92), <O> 0.93562 | high (0.179): W 0.45(11), eps*s 2.278(88), <O> 0.93644
Tercile split by max_d|P_d| (bins of 5 members, chronological): low (0.115): W 0.296(96), eps*s 2.356(88), <O> 0.93519 | mid (0.160): W 0.437(83), eps*s 2.11(12), <O> 0.93577 | high (0.215): W 0.24(12), eps*s 2.475(91), <O> 0.93669
