# P8 anchor window survival (p8_hi final: beta 2.50 16^3x32, seed 2511, 6000 meas)

data `runs/p8_hi_b2.50_L16x32/data.bin`, N=5400 configs used (skip 600), bins of 20 (270 bins), Lt=32. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.0931(95) | 0.0931(95) | -0.007(10) | -0.08(11) | -0.015(63) | 2.7(15) | n/a | 0.802(45) | -0.38(58) | -0.08(12) |
| Y_j unboxed (M=0) | 0.00001(0) | 0.0775(23) | 0.0775(23) | 0.0058(25) | 0.075(32) | 0.151(52) | 1.75(19) | 0.83(43) | 0.802(45) | 0.37(15) | 0.065(27) |
| flow rho=1 loop | 0.00003(0) | 0.3023(25) | 0.3023(25) | 0.0507(28) | 0.1678(88) | 0.164(15) | 0.983(21) | 0.802(45) | 0.802(45) | 0.835(40) | 0.563(51) |
| flow rho=1 loop + box M=side | 0.00001(0) | 0.3537(64) | 0.3537(64) | 0.0635(87) | 0.179(22) | 0.169(19) | 0.897(41) | 0.821(87) | 0.802(45) | 0.89(11) | 0.70(10) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0882(35) | 0.0882(35) | 0.0566(97) | 0.302(14) | 0.199(12) | 0.96(12) | 0.193(37) | 0.193(37) |

## side 3  (W = R(4)/R(1); Y_j box needs lags up to 10 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.083(15) | 0.083(15) | 0.002(15) | 0.02(18) | -0.134(80) | 2.8(31) | n/a | 0.747(34) | 0.08(81) | 0.03(30) |
| Y_j unboxed (M=0) | 0.00001(0) | 0.0775(23) | 0.0775(23) | -0.0039(24) | -0.050(32) | -0.029(49) | 1.75(19) | n/a | 0.747(34) | -0.22(14) | -0.077(51) |
| flow rho=1 loop | 0.00020(0) | 0.3973(24) | 0.3973(24) | 0.0410(30) | 0.1033(75) | 0.091(11) | 0.777(12) | 0.757(54) | 0.747(34) | 0.4596(56) | 0.813(54) |
| flow rho=1 loop + box M=side | 0.00004(0) | 0.4465(75) | 0.4465(75) | 0.060(13) | 0.135(27) | 0.095(17) | 0.731(33) | 0.59(11) | 0.747(34) | 0.60(11) | 1.19(23) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0383(17) | 0.0383(17) | 0.035(12) | 0.2037(96) | 0.1038(65) | 0.59(11) | 0.063(15) | 0.133(29) |

## side 4  (W = R(5)/R(2); Y_j box needs lags up to 13 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.084(20) | 0.010(21) | 0.026(22) | 2.6(49) | -5.2(3027) | 0.15(87) | -0.52(68) | 0.644(47) | 18.0(344) | 0.66(55) |
| Y_j unboxed (M=0) | 0.00001(0) | 0.0775(23) | 0.0134(26) | -0.0020(25) | -0.15(19) | -0.07(41) | 0.83(43) | 0.6(13) | 0.644(47) | -1.0(13) | -0.051(64) |
| flow rho=1 loop | 0.00070(0) | 0.4394(24) | 0.2187(29) | 0.0304(32) | 0.139(14) | 0.122(21) | 0.684(20) | 0.602(72) | 0.644(47) | 0.961(43) | 0.76(10) |
| flow rho=1 loop + box M=side | 0.00010(0) | 0.4931(94) | 0.259(14) | 0.051(17) | 0.198(58) | 0.181(37) | 0.595(59) | 0.49(15) | 0.644(47) | 1.37(38) | 1.28(41) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0220(12) | 0.0238(28) | 0.0117(66) | 0.163(14) | 0.0818(98) | 2.2(53) | 0.32(76) | 0.32(76) |
