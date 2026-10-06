# P8 anchor window survival beta 2.95 48^3x48, 50 P7 cfgs

**Reading (YM Bot, 2026-10-06 10:35 PT): NOT a positive measurement.** 50 P7 configs (meas spaced 12 sweeps; bins of 5).
Boxed Y_j W (E1) at sides 2/4/6/8 = 1.13(64), 0.81(26), 1.05(39), 0.51(48); E3d unresolved at every side.
For a reflection-positive correlator R(s/2) >= R(s+1), so W <= 1; values near or above 1 indicate noise dominates, and the
jackknife errors are likely underestimated (P7 has a slow dir-3 Polyakov sector mode spanning most of the run).
Ground overlap by factorization is consistent with 0 (f0_x(1) = 0.0001(12)). The smoothed NS-k2 / flow loops on the SAME
configs give W 0.12-0.40 with ~0.1-0.15 errors. Conclusion unchanged: window survival on the exact anchor is not resolved
at beta 2.95; the decisive test is the high-statistics beta 2.5 run (p8_hi, 6000 meas, launched 10:30 PT).

data `runs/p8_anchor_b2.95_L48x48/data.bin`, N=50 configs used (skip 0), bins of 5 (10 bins), Lt=48. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.118(72) | 0.118(72) | 0.133(69) | 1.13(64) | 0.9(2147) | -0.07(25) | -0.06(35) | 0.90(65) | 6.8(107) | 2.0(52) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.049(22) | 0.049(22) | -0.016(11) | -0.33(33) | -1.7(12) | 1.2(13) | n/a | 0.90(65) | -2.0(51) | -0.23(92) |
| NS k2 loop | 0.00000(0) | 0.212(14) | 0.212(14) | 0.026(22) | 0.12(10) | 0.08(15) | 1.20(31) | 0.90(65) | 0.90(65) | 0.74(38) | 0.39(51) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.029(30) | 0.029(30) | 0.0009(65) | 0.28(16) | 0.062(60) | 0.22(44) | 0.036(86) | 0.036(86) |

## side 4  (W = R(5)/R(2); Y_j box needs lags up to 13 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.320(86) | 0.298(93) | 0.24(12) | 0.81(26) | -3.5(143) | -0.03(12) | 0.16(18) | 0.34(16) | 2.3(13) | 1.3(14) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.049(22) | 0.014(11) | 0.019(21) | 1.3(15) | 0.8(14) | n/a | 0.8(13) | 0.34(16) | 3.8(56) | 0.10(13) |
| NS k2 loop | 0.00000(0) | 0.451(20) | 0.215(22) | 0.064(21) | 0.298(89) | 0.10(14) | 0.52(10) | 0.13(27) | 0.34(16) | 0.84(18) | 0.36(18) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0022(65) | 0.0001(22) | 0.0014(40) | 0.32(13) | 0.001(10) | 0.001(15) | 0.0004(46) | 0.0004(46) |

## side 6  (W = R(7)/R(3); Y_j box needs lags up to 19 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.449(93) | 0.42(12) | 0.44(19) | 1.05(39) | 1.01(91) | 0.08(12) | -0.072(88) | 0.20(10) | 2.3(17) | 1.7(20) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.049(22) | -0.016(11) | 0.038(18) | -2.4(16) | -0.23(35) | n/a | n/a | 0.20(10) | -5.2(27) | 0.15(13) |
| NS k2 loop | 0.00002(0) | 0.587(17) | 0.238(26) | 0.094(40) | 0.40(15) | 0.21(22) | 0.34(10) | 0.23(15) | 0.20(10) | 0.869(75) | 0.37(14) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0007(31) | 0.0015(31) | 0.010(31) | 0.36(17) | 0.014(36) | 0.019(53) | 0.009(29) | 0.009(29) |

## side 8  (W = R(9)/R(4); Y_j box needs lags up to 25 (> Lt/2: periodic image enters!))

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.55(11) | 0.52(18) | 0.26(33) | 0.51(48) | 5.7(803) | 0.032(85) | 0.28(45) | 0.27(10) | 1.9(28) | 2.9(74) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.049(22) | 0.044(26) | 0.029(29) | 0.66(73) | 1.4(86) | 0.8(13) | -0.2(12) | 0.27(10) | 2.5(27) | 0.32(35) |
| NS k2 loop | 0.00007(0) | 0.677(14) | 0.257(32) | 0.071(36) | 0.28(12) | 0.45(24) | 0.213(67) | 0.32(17) | 0.27(10) | 1.054(79) | 0.79(38) |
| flow rho=1 loop | 0.00007(0) | 0.676(14) | 0.256(32) | 0.071(36) | 0.28(12) | 0.45(24) | 0.213(68) | 0.32(17) | 0.27(10) | 1.055(80) | 0.79(39) |
| flow rho=1 loop + box M=side | 0.00001(0) | 0.768(40) | 0.41(12) | 0.19(26) | 0.46(53) | 0.51(40) | 0.17(15) | 0.16(59) | 0.27(10) | 1.7(21) | 2.1(31) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0001(12) | 0.0005(15) | 0.002(12) | 0.186(86) | 0.003(11) | 0.0021(94) | 0.0006(29) | 0.0006(29) |
