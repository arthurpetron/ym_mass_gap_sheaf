# P8 anchor window survival (P7 beta 2.95 48^3x48 saved configs, PARTIAL)

data `runs/p8_anchor_b2.95_L48x48/data.bin`, N=11 configs used (skip 0), bins of 1 (11 bins), Lt=48. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | -0.06(17) | -0.06(17) | -0.11(12) | 1.9(68) | -0.9(46) | -0.8(27) | n/a | n/a | n/a | n/a |
| Y_j unboxed (M=0) | 0.00000(0) | 0.018(48) | 0.018(48) | -0.044(34) | -2.4(1467) | -34.2(218) | n/a | n/a | n/a | n/a | n/a |
| NS k2 loop | 0.00000(0) | 0.197(36) | 0.197(36) | -0.050(37) | -0.26(22) | -0.11(14) | n/a | n/a | n/a | n/a | n/a |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| -0.7(38) | -0.7(38) | -0.04(32) | n/a | n/a | n/a | n/a | n/a |

## side 4  (W = R(5)/R(2); Y_j box needs lags up to 13 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | -0.16(41) | -0.20(41) | -0.29(44) | 1.4(35) | 0.2(12) | n/a | n/a | n/a | n/a | n/a |
| Y_j unboxed (M=0) | 0.00000(0) | 0.018(48) | 0.017(36) | -0.010(41) | -0.6(68) | 1.1(27) | n/a | n/a | n/a | n/a | n/a |
| NS k2 loop | 0.00000(0) | 0.396(47) | 0.162(50) | -0.007(21) | -0.04(14) | -0.01(68) | 0.34(32) | n/a | n/a | n/a | n/a |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.027(39) | 0.003(13) | -0.003(47) | n/a | n/a | n/a | n/a | n/a |

## side 6  (W = R(7)/R(3); Y_j box needs lags up to 19 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | -0.4(15) | -0.6(17) | -0.8(18) | 1.2(18) | -0.2(3126) | -0.13(36) | -0.02(27) | n/a | n/a | n/a |
| Y_j unboxed (M=0) | 0.00000(0) | 0.018(48) | -0.044(34) | 0.091(40) | -2.1(22) | -1.4(23) | n/a | n/a | n/a | n/a | n/a |
| NS k2 loop | 0.00002(0) | 0.507(47) | 0.155(38) | 0.019(44) | 0.13(29) | -0.2(10) | 0.34(34) | n/a | n/a | n/a | n/a |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.004(12) | 0.000(15) | 0.009(24) | n/a | n/a | n/a | n/a | n/a |

## side 8  (W = R(9)/R(4); Y_j box needs lags up to 25 (> Lt/2: periodic image enters!))

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | -1.8(152) | -1.9(131) | -1.0(66) | 0.5(11) | 2.0(238) | 0.05(35) | n/a | 0.21(51) | 1.5(238) | -6.3(4008) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.018(48) | 0.016(34) | -0.051(35) | -3.1(154) | -1.5(29) | n/a | n/a | 0.21(51) | -8.9(644) | -0.3(159) |
| NS k2 loop | 0.00006(1) | 0.621(39) | 0.207(56) | 0.064(99) | 0.31(46) | 0.25(49) | 0.33(20) | 0.03(70) | 0.21(51) | 0.88(37) | 0.4(21) |
| flow rho=1 loop | 0.00006(1) | 0.621(39) | 0.207(56) | 0.064(99) | 0.31(46) | 0.25(49) | 0.33(20) | 0.03(68) | 0.21(51) | 0.88(42) | 0.4(23) |
| flow rho=1 loop + box M=side | 0.00001(0) | 0.68(25) | 0.09(59) | -0.33(68) | -3.5(97) | -0.07(72) | n/a | -0.07(39) | 0.21(51) | -10.1(732) | -2.2(2580) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0001(42) | 0.0000(44) | -0.003(10) | 0.25(51) | 0.00(56) | -0.000(38) | -0.000(23) | -0.000(23) |
