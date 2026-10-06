# P8 anchor window survival (p5_b2.50_L24x32)

data `runs/p5_b2.50_L24x32_s2/data.bin`, N=540 configs used (skip 60), bins of 6 (90 bins), Lt=32. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.131(24) | 0.131(24) | -0.009(27) | -0.07(21) | 0.09(14) | 1.74(94) | n/a | 0.57(12) | -0.22(67) | -0.05(15) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.0821(83) | 0.0821(83) | 0.0182(83) | 0.22(11) | 0.44(21) | 1.31(33) | 0.20(57) | 0.57(12) | 0.69(35) | 0.101(55) |
| flow rho=1 loop | 0.00001(0) | 0.2993(85) | 0.2993(85) | 0.0642(95) | 0.215(30) | 0.125(39) | 0.969(71) | 0.57(12) | 0.57(12) | 0.671(90) | 0.355(87) |
| flow rho=1 loop + box M=side | 0.00000(0) | 0.389(20) | 0.389(20) | 0.113(26) | 0.291(56) | 0.252(52) | 0.683(79) | 0.55(12) | 0.57(12) | 0.91(20) | 0.62(19) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.102(11) | 0.102(11) | 0.037(13) | 0.395(59) | 0.288(49) | 1.25(40) | 0.40(21) | 0.40(21) |

## side 3  (W = R(4)/R(1); Y_j box needs lags up to 10 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.106(34) | 0.106(34) | -0.006(44) | -0.06(42) | -0.09(17) | 2.0(26) | n/a | 0.581(70) | -0.2(14) | -0.06(45) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.0821(83) | 0.0821(83) | -0.0079(70) | -0.097(86) | -0.13(17) | 1.31(33) | n/a | 0.581(70) | -0.31(28) | -0.081(76) |
| flow rho=1 loop | 0.00006(0) | 0.4034(79) | 0.4034(79) | 0.0582(100) | 0.144(24) | 0.112(31) | 0.774(48) | 0.53(11) | 0.581(70) | 0.461(22) | 0.595(78) |
| flow rho=1 loop + box M=side | 0.00001(0) | 0.490(24) | 0.490(24) | 0.120(41) | 0.245(76) | 0.154(49) | 0.577(77) | 0.37(14) | 0.581(70) | 0.78(21) | 1.23(37) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0457(60) | 0.0457(60) | 0.0191(98) | 0.262(31) | 0.150(25) | 0.79(31) | 0.139(70) | 0.25(11) |
