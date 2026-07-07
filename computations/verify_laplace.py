from mpmath import mp, mpf, quad, exp, pi, ei, inf, fabs
mp.dps = 50

# ============================================================
# CLAIM 1: Laplace of a geometric Borel B(t)=C/(1-s t) has a
# positive-axis pole at t0=1/s and an ambiguity (pi C/s) exp(-t0/g^2).
# We verify by: PV integral (principal value) computes to
#   I = -(C/s) e^{-1/(s g^2)} Ei(1/(s g^2)),   [real part]
# and the discontinuity across the pole (deform +/- i eps) is
#   Delta I = 2 * pi * C/s * e^{-1/(s g^2)}  (full jump = 2*imag).
# Ambiguity |Im| = pi C/s e^{-t0/g^2}.
# ============================================================
def laplace_geom_contour(C, s, g2, sign):
    # integrate along a contour shifted off the real axis by i*sign*eps
    eps = mpf('1e-12')
    p = 1/g2
    f = lambda t: exp(-p*t) * C/(1 - s*(t + 1j*sign*eps))
    # integrate t from 0 to large T; integrand decays like e^{-p t}
    T = 60*g2 + 5/ s  # enough range
    return quad(f, [0, 1/s, T])

for (C, s, g2) in [(mpf(1), mpf(3), mpf('0.4')), (mpf(2), mpf('1.5'), mpf('0.7')),
                   (mpf(1), mpf(16), mpf('0.05'))]:
    t0 = 1/s
    Ip = laplace_geom_contour(C, s, g2, +1)
    Im = laplace_geom_contour(C, s, g2, -1)
    amb_pred = pi * C / s * exp(-t0/g2)
    amb_num  = fabs(Ip.imag)     # |Im of one contour|
    jump     = fabs(Ip - Im)
    # real part predicted: PV = -(C/s) e^{-p/s} Ei(p/s), p=1/g2
    p = 1/g2
    pv_pred = -(C/s) * exp(-p/s) * ei(p/s)
    pv_num  = (Ip.real + Im.real)/2
    print(f"C={C} s={s} g2={g2}: t0={float(t0):.5f}")
    print(f"   ambiguity |Im|: num={mp.nstr(amb_num,12)}  pred(piC/s e^-t0/g2)={mp.nstr(amb_pred,12)}  reldiff={mp.nstr(fabs(amb_num-amb_pred)/amb_pred,4)}")
    print(f"   jump 2Im:       num={mp.nstr(jump,12)}  pred={mp.nstr(2*amb_pred,12)}")
    print(f"   PV real:        num={mp.nstr(pv_num,12)}  pred={mp.nstr(pv_pred,12)}  reldiff={mp.nstr(fabs(pv_num-pv_pred)/fabs(pv_pred),4)}")
