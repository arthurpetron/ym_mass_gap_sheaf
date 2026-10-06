# P7 final (auto): beta 2.95, 48^3x48, side 8 — 2026-10-06 12:29 PDT

**Reading (YM Bot, 2026-10-06 12:35 PT).** At rho=1, eps*s = 2.657(81) at Ls=48 vs 2.363(92) at Ls=32: about 2.4 sigma higher in the bigger
spatial box, so the side-8 eps*s is not yet volume-independent at Ls=32. W = 0.371(67) vs 0.355(58): unchanged. The dir-3 smeared spatial
Polyakov loop changed sign only 4 times in 240 meas (26-28 in the other directions), so the slow sector mode persisted for the whole run and
the errors may be underestimated. m_eff(n) at rho=1 keeps falling through n=6-9 (0.19-0.14, large errors), so no clean plateau.
Step-ratio constant at the best lag k=s/2=4 from m_eff(4)=0.268(31): c = 8(1-exp(-0.268)) ~ 1.9, inside the P9 range 1.2-2.4.
Flow-smoothed MC operator only, not the exact Lean anchor Y_j; numerics, not proof.

Records: 240/240 (interval 4 sweeps, therm 1000). Reference: Ls=32 run b2.95_L32x48_s8 (240 meas, P6 numbers).

## Thermalization: smoothed operator mean <O> (side 8, rho=1.00) in blocks of 10 meas

0.88308 0.88329 0.88309 0.88490 0.88469 0.88053 0.88276 0.88556 0.88722 0.88389 0.88678 0.88358 0.88433 0.88381 0.88565 0.88686 0.88293 0.88587 0.88410 0.88048 0.88510 0.88483 0.88412 0.88339

Discard chosen: first **0** measurements (smallest multiple of 10 with half-vs-half difference < 1.5 sigma and total linear drift < 2 sigma over the kept window).


## W = R(s+1)/R(s//2), eps*s (bin 10, N kept 240); Ls=32 values in brackets

| rho | W E1 | W E3f | W E3d | eps*s E1 | eps_shift*s | R(s)/R(0) |
|---|---|---|---|---|---|---|
| 0.00 | 1.3(128) [-5.7(1080)] | 1.1(53) [2.3(32)] | 0.4(78) [-0.7(14)] | 7.662(91) [7.989(67)] | 10.3(78) [32.4(346)] | -0.0086(83) [0.0058(79)] |
| 0.50 | 0.34(11) [0.294(84)] | 0.39(11) [0.21(14)] | 0.46(35) [0.28(15)] | 3.730(84) [3.546(63)] | 1.86(87) [0.9(13)] | 0.058(15) [0.051(15)] |
| 0.75 | 0.371(82) [0.351(69)] | 0.391(82) [0.31(10)] | 0.29(19) [0.30(11)] | 3.151(87) [2.900(78)] | 1.19(60) [0.90(74)] | 0.082(19) [0.092(18)] |
| 1.00 | 0.371(67) [0.355(58)] | 0.393(75) [0.354(85)] | 0.27(12) [0.339(98)] | 2.657(81) [2.363(92)] | 1.03(48) [1.15(50)] | 0.104(20) [0.127(21)] |
| 1.25 | 0.362(64) [0.343(58)] | 0.391(81) [0.370(85)] | 0.277(91) [0.383(89)] | 2.282(75) [1.986(92)] | 1.20(40) [1.38(39)] | 0.126(24) [0.150(25)] |
| 1.50 | 0.349(67) [0.323(67)] | 0.381(88) [0.369(93)] | 0.274(77) [0.410(79)] | 2.040(78) [1.746(82)] | 1.41(38) [1.61(42)] | 0.143(29) [0.161(31)] |

## Binning tau_int of the operator mean (kept window) vs Ls=32

| rho | tau(b) Ls=48 | tau(b) Ls=32 |
|---|---|---|
| 0.00 | b1:0.50, b2:0.47, b4:0.43, b8:0.41, b16:0.31 | b1:0.50, b2:0.47, b4:0.54, b8:0.54 |
| 0.50 | b1:0.50, b2:0.67, b4:0.78, b8:1.00, b16:0.84 | b1:0.50, b2:0.62, b4:0.88, b8:1.07 |
| 0.75 | b1:0.50, b2:0.68, b4:0.89, b8:1.34, b16:1.19 | b1:0.50, b2:0.70, b4:1.09, b8:1.45 |
| 1.00 | b1:0.50, b2:0.72, b4:1.04, b8:1.68, b16:1.62 | b1:0.50, b2:0.76, b4:1.24, b8:1.82 |
| 1.25 | b1:0.50, b2:0.76, b4:1.16, b8:1.94, b16:2.01 | b1:0.50, b2:0.81, b4:1.36, b8:2.15 |
| 1.50 | b1:0.50, b2:0.80, b4:1.26, b8:2.11, b16:2.32 | b1:0.50, b2:0.84, b4:1.46, b8:2.40 |

## m_eff(n) (E1) at rho=1.00, Ls=48 [Ls=32]

n=0: 0.404(15) [0.350(16)] | n=1: 0.358(17) [0.303(19)] | n=2: 0.337(21) [0.282(25)] | n=3: 0.307(28) [0.249(24)] | n=4: 0.268(31) [0.235(27)] | n=5: 0.252(46) [0.219(32)] | n=6: 0.187(54) [0.213(32)] | n=7: 0.147(61) [0.214(52)] | n=8: 0.138(69) [0.156(73)] | n=9: 0.189(88) [0.223(79)]

## Smeared spatial Polyakov loops (spatially flowed links), line means per measurement

rho=1.00: mean |P_d| over meas = [0.0895, 0.1067, 0.1127], mean P_d = [0.073, 0.0298, -0.1122], max |P| = 0.2892, sign changes per direction = [np.int64(28), np.int64(26), np.int64(4)], <P^2> line avg = [0.24949, 0.25233, 0.25092]
  blocks of 10, max_d |P_d|: 0.217 0.181 0.174 0.197 0.208 0.152 0.232 0.239 0.274 0.236 0.213 0.249 0.238 0.198 0.289 0.281 0.191 0.200 0.252 0.203 0.162 0.271 0.248 0.246
  corr(<O>(rho~1), max_d|P_d|) = 0.22

rho=1.50: mean |P_d| over meas = [0.1444, 0.1657, 0.1783], mean P_d = [0.1202, 0.0496, -0.1778], max |P| = 0.4350, sign changes per direction = [np.int64(24), np.int64(22), np.int64(2)], <P^2> line avg = [0.25026, 0.25822, 0.25428]
  blocks of 10, max_d |P_d|: 0.299 0.262 0.255 0.307 0.298 0.255 0.352 0.353 0.397 0.344 0.308 0.375 0.345 0.301 0.427 0.435 0.315 0.316 0.383 0.308 0.226 0.392 0.384 0.384
  corr(<O>(rho~1), max_d|P_d|) = 0.22

## Resources (755 samples, 30 s)
MemAvailable MB min/mean/max 4607/7664/11425; load1 2.29/5.19/11.41; job RSS MB max 3021; threads now 3; throttle events: 5 — # 09:11:10 THROTTLE: threads -> 3 (memavail 7914 MB, load1 8.67); # 09:22:10 RESTORE: threads -> 4 (memavail 5886 MB, load1 4.13); # 09:49:42 THROTTLE: threads -> 3 (memavail 7795 MB, load1 9.33); # 10:07:13 RESTORE: threads -> 4 (memavail 7668 MB, load1 3.50); # 10:30:44 THROTTLE: threads -> 3 (memavail 5148 MB, load1 8.37)

Last log line: `meas 240/240 22650.5s (76.92s/meas) plaq=0.717618 th=3 O_s8=0.00267,0.54141,0.77169,0.88408,0.93616,0.96186 P_last=[-0.2051,-0.3170,-0.1118]`
