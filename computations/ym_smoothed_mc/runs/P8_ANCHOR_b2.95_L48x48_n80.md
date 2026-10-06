# P8 anchor window survival beta 2.95 48^3x48, all 80 P7 cfgs

**Reading (YM Bot, 2026-10-06 12:35 PT): still NOT a positive measurement (final P7 pass, all 80 cfgs).** Boxed Y_j W (E1) at sides 2/4/6/8 =
0.68(49), 1.00(92), 0.92(67), 0.5(10); E3d unresolved at every side; ground-state overlap of the plaquette family ~0 (0.0000(21)).
Since W <= 1 for a reflection-positive correlator, values near 1 with errors ~0.5-1 are noise. 80 vs 50 configs did not help:
the exact Lean anchor Y_j at beta 2.95 is a statistics wall for direct measurement. Flow rho=1 loop at side 8 on the same
configs: W 0.333(92), consistent with the P7 stream (0.371(67)). MC only; says nothing rigorous about the Lean claim.

data `runs/p8_anchor_b2.95_L48x48/data.bin`, N=80 configs used (skip 0), bins of 5 (16 bins), Lt=48. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.086(59) | 0.086(59) | 0.058(59) | 0.68(49) | 1.3(33) | 0.19(43) | 0.20(52) | 0.75(42) | 3.0(35) | 0.55(84) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.050(15) | 0.050(15) | -0.003(13) | -0.05(27) | -0.51(55) | n/a | n/a | 0.75(42) | -0.2(19) | -0.02(25) |
| NS k2 loop | 0.00000(0) | 0.2079(95) | 0.2079(95) | 0.035(17) | 0.167(80) | 0.22(13) | 1.04(21) | 0.75(42) | 0.75(42) | 0.75(33) | 0.33(29) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.019(17) | 0.019(17) | 0.02(10) | 0.32(15) | 0.050(52) | 0.27(48) | 0.06(13) | 0.06(13) |

## side 4  (W = R(5)/R(2); Y_j box needs lags up to 13 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.16(12) | 0.11(12) | 0.11(12) | 1.00(92) | 4.2(119) | -0.03(35) | 0.08(36) | 0.35(14) | 2.9(31) | 0.67(98) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.050(15) | -0.002(14) | 0.010(15) | -4.4(1359) | 55.4(692) | n/a | 0.9(17) | 0.35(14) | -12.9(3644) | 0.060(95) |
| NS k2 loop | 0.00000(0) | 0.463(13) | 0.233(15) | 0.060(19) | 0.259(77) | 0.14(11) | 0.643(84) | 0.20(19) | 0.35(14) | 0.75(12) | 0.36(15) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0003(16) | 0.00002(68) | 0.0015(52) | 0.31(11) | 0.0001(40) | 0.001(20) | 0.0002(61) | 0.0002(61) |

## side 6  (W = R(7)/R(3); Y_j box needs lags up to 19 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.24(15) | 0.24(17) | 0.22(21) | 0.92(67) | 1.9(132) | 0.08(24) | 0.03(22) | 0.256(90) | 2.5(26) | 1.3(17) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.050(15) | -0.003(13) | 0.001(18) | -0.5(394) | 0.53(98) | n/a | n/a | 0.256(90) | -1.4(1060) | 0.01(10) |
| NS k2 loop | 0.00002(0) | 0.588(14) | 0.239(19) | 0.081(26) | 0.34(10) | 0.09(16) | 0.321(67) | 0.26(14) | 0.256(90) | 0.937(86) | 0.48(17) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0002(12) | 0.00003(75) | 0.004(10) | 0.28(10) | 0.0003(69) | 0.001(12) | 0.0002(41) | 0.0002(41) |

## side 8  (W = R(9)/R(4); Y_j box needs lags up to 25 (> Lt/2: periodic image enters!))

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.34(19) | 0.28(24) | 0.15(33) | 0.5(10) | 0.7(107) | 0.09(28) | n/a | 0.219(62) | 1.5(34) | 1.1(28) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.050(15) | 0.024(19) | 0.009(23) | 0.39(94) | 0.9(222) | 0.9(17) | n/a | 0.219(62) | 1.2(28) | 0.07(17) |
| NS k2 loop | 0.00007(0) | 0.674(13) | 0.259(24) | 0.086(28) | 0.333(92) | 0.39(20) | 0.225(52) | 0.27(12) | 0.219(62) | 0.995(56) | 0.62(18) |
| flow rho=1 loop | 0.00007(0) | 0.673(13) | 0.259(24) | 0.086(28) | 0.333(92) | 0.39(20) | 0.225(52) | 0.28(12) | 0.219(62) | 0.994(56) | 0.62(18) |
| flow rho=1 loop + box M=side | 0.00001(0) | 0.786(32) | 0.440(100) | 0.16(20) | 0.36(39) | 0.66(23) | 0.17(11) | 0.26(49) | 0.219(62) | 1.1(11) | 1.1(13) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0004(12) | 0.00000(26) | 0.0000(16) | 0.236(76) | 0.0000(34) | 0.0001(57) | 0.0000(21) | 0.0000(21) |
