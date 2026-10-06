# P4 interim (first beta finished 20:27 PT, Oct 5 2026), not sent (no SendToAgent tool in this executor)
SU(2) Wilson, beta=2.5, 24^3x32, side=2 (= 1.475 sqrt(t0), t0 from Hirakida et al. 1811.02800), 1000 meas (HB+4OR x3 between),
spatial 3D Wilson flow, rho = sqrt(6 t)/side; observable = A1 zero-momentum sum of smoothed 2x2 spatial loops; jackknife, 200 bins of 5 (tau_int(M) ~0.7 meas).
| rho | eps | eps*side | R(2u)/R(0)=R(2)/R(0) | R(4u)/R(2u)=R(4)/R(2) | kappa_b(u=1) | (1-eps)^2 |
| 0    | 0.8790(53) | 1.758(11) | 0.0274(59) | 0.18(22)  | 0.18(40)  | 0.0147(13) |
| 0.5  | 0.8059(56) | 1.612(11) | 0.0529(60) | 0.29(11)  | -0.09(19) | 0.0377(22) |
| 0.7  | 0.7681(56) | 1.536(11) | 0.0722(61) | 0.282(77) | -0.18(14) | 0.0538(26) |
| 1.0  | 0.7100(59) | 1.420(12) | 0.1069(64) | 0.248(55) | -0.17(10) | 0.0841(34) |
R(n)/R(0) rho=1: 1, 0.2900(59), 0.1069(64), 0.0445(67), 0.0265(64)
Pre-run snapshot: nproc 8; free -g total 15G, used 12G, avail 3G; loadavg 1.25. Sampled (75 x 30 s): MemAvailable 2693/3808/6990 MB (16.8/23.8/43.7%), load1 1.25/5.53/6.79, 0 throttle events.

## Update 20:45 PT: MATH-NOTE-H1 quantities (beta=2.5, 24^3x32, side=2; jackknife)
eps_shift = 1-R(s+1)/R(s) [anchor T^{s/2}x]; eps_half = 1-R(h+1)/R(h), h=floor(s/2) [side/2-lag variant];
eps_box = Fejer box kernel Y=p(T)x with M=side (1-B(Y,TY)/B(Y,Y)); m_eff = ln R(s)/R(s+1); L = side*a; lit m0++ L = 3.78*a*sqrt(sigma)*side = 1.45.
| rho | eps*side | eps_shift | eps_shift*side | eps_half*side | eps_box | eps_box*side | eps_box shifted T^{s/2} *side | a m_eff | m_eff L |
| 0    | 1.758(11) | 0.41(20)  | 0.82(40) | 1.547(92) | 0.822(20) | 1.643(41) | 1.06(44) | 0.53(34) | 1.06(68) |
| 0.5  | 1.612(11) | 0.544(94) | 1.09(19) | 1.455(55) | 0.744(18) | 1.489(36) | 0.96(23) | 0.79(21) | 1.57(41) |
| 1.0  | 1.420(12) | 0.584(52) | 1.17(10) | 1.263(37) | 0.653(16) | 1.306(32) | 1.07(16) | 0.88(12) | 1.75(25) |
(lit m0++ L = 1.45, 2 m0++ L = 2.90.) Single beta only: nothing yet about leveling off.
Resources b2.50 run: pre-run nproc 8, 15G total / 3G avail, load 1.25; sampled MemAvailable 2693/3808/6990 MB (16.8/23.8/43.7%), load1 1.25/5.53/6.79, 0 throttles.
