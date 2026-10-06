# P8 anchor window survival (p4_b2.50_L24x32)

data `runs/b2.50_L24x32_s2/data.bin`, N=900 configs used (skip 100), bins of 6 (150 bins), Lt=32. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.


## side 2  (W = R(3)/R(1); Y_j box needs lags up to 7 )

| operator | R(0) | R(1)/R(0) | R(s/2)/R(0) | R(s+1)/R(0) | **W** E1 | W E3d | m_eff a @s/2 | m_eff a @s | m0 a (ref) | f0(s/2) = W/λ0^(s/2+1) | f0(0) ≈ R(s+1)/(λ0^(s+1) R(0)) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Y_j (box M=side) | 0.00000(0) | 0.129(20) | 0.129(20) | 0.033(20) | 0.25(14) | 0.15(17) | 0.75(21) | 0.63(38) | 0.82(12) | 1.29(75) | 0.38(26) |
| Y_j unboxed (M=0) | 0.00000(0) | 0.0693(56) | 0.0693(56) | 0.0086(62) | 0.125(90) | -0.06(18) | 1.22(29) | 0.86(75) | 0.82(12) | 0.64(47) | 0.100(78) |
| flow rho=1 loop | 0.00001(0) | 0.2892(59) | 0.2892(59) | 0.0479(72) | 0.166(24) | 0.079(31) | 0.983(53) | 0.82(12) | 0.82(12) | 0.85(11) | 0.55(14) |
| flow rho=1 loop + box M=side | 0.00000(0) | 0.360(16) | 0.360(16) | 0.090(21) | 0.249(51) | 0.236(47) | 0.748(77) | 0.64(14) | 0.82(12) | 1.28(32) | 1.04(34) |

Ground-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).

| f0_x(n=1) | f0_x(n=s/2) | f0_x(n=s) | box gain g0^2 | f0_Y(0) | f0_Y(s/2) | W_Y predicted (ground state only) | f0_Y(s/2)·λ0^(s/2+1) |
|---|---|---|---|---|---|---|---|
| 0.0858(80) | 0.0858(80) | 0.0295(97) | 0.298(38) | 0.187(29) | 0.64(18) | 0.125(64) | 0.125(64) |
