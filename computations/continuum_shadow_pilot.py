"""
continuum_shadow_pilot.py — reproduce the continuum-shadow decomposition of R1
(SaddleVarianceFloor) for the SU(2) heat-kernel character coefficients.

Objects (matching lean/YMGap/Continuum/CircleFourierPowerModel.lean):
  coeffW(w,s)   = (s+1) w^{s(s+2)}
  acNfull(t)    = sum_{p=0}^t coeffW(p) coeffW(t-p)                       ("mass" A_t)
  dmomNfull(t)  = sum_{p=0}^t (t-2p)^2 coeffW(p) coeffW(t-p)             (second moment)
  V(t) = <D^2>_t = dmomNfull(t)/acNfull(t)   (variance of D=t-2p under tilted measure)

R1  :  Delta^2_t V(t) >= -2   for all t,  i.e.  V(s)+V(s+2)-2V(s+1) >= -2.

Decomposition tested here:
  D-lattice / envelope-removed objects: with M=t+2, D runs over {-t,-t+2,...,t},
      theta_t = sum_D w^{D^2/2},  xi_t = sum_D D^2 w^{D^2/2}
      den_t   = sum_D (M^2-D^2) w^{D^2/2} = M^2 theta_t - xi_t
      num_t   = sum_D D^2 (M^2-D^2) w^{D^2/2} = M^2 xi_t - zeta_t,  zeta_t=sum_D D^4 w^{D^2/2}
  V(t) = num_t/den_t   (envelope w^{t^2/2+2t}/4 cancels in the ratio).
  G(t) = xi_t/theta_t  (pure-Gaussian lattice variance).

Recursions (all positive):
  theta_{t+2} = theta_t + 2 w^{(t+2)^2/2}
  xi_{t+2}    = xi_t    + 2 (t+2)^2 w^{(t+2)^2/2}
  den_{t+2}   = den_t + 4 (t+3) theta_{t+2}
  num_{t+2}   = num_t + 4 (t+3) xi_{t+2}
  Delta^2 ((t+2)^2) = 2
Convex combination:  V(t+2) = lam V(t) + (1-lam) G(t+2),  lam = den_t/den_{t+2} in (0,1).
Continuum shadow: V(t) -> G_parity(w);  Delta^2 V(even s->inf) -> -2(G_odd - G_even),
  with G_odd - G_even in [0,1].
"""

from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 60

# ---------- exact rational-in-w objects (w given as Fraction) ----------

def coeffW(w, s):
    return F(s + 1) * w ** (s * (s + 2))

def acNfull(w, t):
    return sum(coeffW(w, p) * coeffW(w, t - p) for p in range(t + 1))

def dmomNfull(w, t):
    return sum(F((t - 2 * p) ** 2) * coeffW(w, p) * coeffW(w, t - p) for p in range(t + 1))

def V(w, t):
    return dmomNfull(w, t) / acNfull(w, t)

# ---------- D-lattice (envelope-removed) objects, mpmath float ----------

def Ds(t):
    return list(range(-t, t + 1, 2))

def theta(wf, t):
    return mp.fsum(wf ** (mp.mpf(D * D) / 2) for D in Ds(t))

def xi(wf, t):
    return mp.fsum(mp.mpf(D * D) * wf ** (mp.mpf(D * D) / 2) for D in Ds(t))

def zeta(wf, t):
    return mp.fsum(mp.mpf(D ** 4) * wf ** (mp.mpf(D * D) / 2) for D in Ds(t))

def den(wf, t):
    M = t + 2
    return mp.fsum((M * M - D * D) * wf ** (mp.mpf(D * D) / 2) for D in Ds(t))

def num(wf, t):
    M = t + 2
    return mp.fsum((D * D) * (M * M - D * D) * wf ** (mp.mpf(D * D) / 2) for D in Ds(t))

def Gvar(wf, t):
    return xi(wf, t) / theta(wf, t)

def envelope(wf, t):
    # acNfull = envelope * den ;  dmomNfull = envelope * num
    return wf ** (mp.mpf(t * t) / 2 + 2 * t) / 4

# ---------- theta-function / continuum limits ----------

def G_even_inf(wf):
    # even lattice D=2j, w^{D^2/2}=r^{j^2}, r=w^2  -> theta3(r); variance in D
    r = wf * wf
    th = mp.fsum(r ** (j * j) for j in range(-400, 401))
    xi_ = mp.fsum((2 * j) ** 2 * r ** (j * j) for j in range(-400, 401))
    return xi_ / th

def G_odd_inf(wf):
    # odd lattice D=2j+1, w^{D^2/2}=r^{(j+1/2)^2}, r=w^2 -> theta2
    r = wf * wf
    th = mp.fsum(r ** (mp.mpf((2 * j + 1) ** 2) / 4) for j in range(-400, 401))
    xi_ = mp.fsum((2 * j + 1) ** 2 * r ** (mp.mpf((2 * j + 1) ** 2) / 4) for j in range(-400, 401))
    return xi_ / th


def hr(title):
    print("\n" + "=" * 72 + "\n" + title + "\n" + "=" * 72)


hr("1. R1 floor  Delta^2 V(s) + 2 >= 0   (exact rational, several w, s=0..10)")
for wq in [F(1, 20), F(1, 4), F(1, 2), F(3, 4), F(9, 10)]:
    mn = None
    for s in range(0, 11):
        d2 = V(wq, s) + V(wq, s + 2) - 2 * V(wq, s + 1) + 2
        mn = d2 if mn is None else min(mn, d2)
    print(f"  w={float(wq):5.3f}   min_s (Delta^2 V + 2) = {float(mn):+.6f}   (>=0 required)")

hr("2. acNfull = envelope * den ,  dmomNfull = envelope * num  (D-lattice reindex)")
wf = mp.mpf('0.3')
for t in range(0, 9):
    a_exact = mp.mpf(str(acNfull(F(3, 10), t)))
    a_dlat = envelope(wf, t) * den(wf, t)
    d_exact = mp.mpf(str(dmomNfull(F(3, 10), t)))
    d_dlat = envelope(wf, t) * num(wf, t)
    print(f"  t={t}: acNfull rel.err={float(abs(a_exact-a_dlat)/abs(a_exact)):.2e}"
          f"   dmomNfull rel.err={float(abs(d_exact-d_dlat)/max(abs(d_exact),mp.mpf(1))):.2e}")

hr("3. Recursions (theta,xi,den,num) — max rel error over t=0..10, several w")
for wv in ['0.05', '0.3', '0.6', '0.9']:
    wf = mp.mpf(wv)
    errs = []
    for t in range(0, 11):
        th2 = theta(wf, t) + 2 * wf ** (mp.mpf((t + 2) ** 2) / 2)
        errs.append(abs(th2 - theta(wf, t + 2)) / abs(theta(wf, t + 2)))
        xi2 = xi(wf, t) + 2 * (t + 2) ** 2 * wf ** (mp.mpf((t + 2) ** 2) / 2)
        errs.append(abs(xi2 - xi(wf, t + 2)) / abs(xi(wf, t + 2)))
        dn2 = den(wf, t) + 4 * (t + 3) * theta(wf, t + 2)
        errs.append(abs(dn2 - den(wf, t + 2)) / abs(den(wf, t + 2)))
        nm2 = num(wf, t) + 4 * (t + 3) * xi(wf, t + 2)
        errs.append(abs(nm2 - num(wf, t + 2)) / abs(num(wf, t + 2)))
    print(f"  w={wv}:  max rel err (theta,xi,den,num recursions) = {float(max(errs)):.2e}")

hr("4. Convex combination  V(t+2) = lam V(t) + (1-lam) G(t+2),  lam=den_t/den_{t+2}")
for wv in ['0.05', '0.3', '0.7', '0.9']:
    wf = mp.mpf(wv)
    me = mp.mpf(0)
    lammin, lammax = mp.mpf(1), mp.mpf(0)
    for t in range(0, 11):
        lam = den(wf, t) / den(wf, t + 2)
        lammin, lammax = min(lammin, lam), max(lammax, lam)
        pred = lam * (num(wf, t) / den(wf, t)) + (1 - lam) * Gvar(wf, t + 2)
        act = num(wf, t + 2) / den(wf, t + 2)
        me = max(me, abs(pred - act) / abs(act))
    print(f"  w={wv}:  max rel err = {float(me):.2e}   lam in [{float(lammin):.4f},{float(lammax):.4f}] (need (0,1))")

hr("5. V(t) -> G_parity(w) ; shadow floor Delta^2 V(even,large) -> -2(G_odd-G_even)")
for wv in ['0.05', '0.2', '0.5', '0.8']:
    wf = mp.mpf(wv)
    Ge, Go = G_even_inf(wf), G_odd_inf(wf)
    # V at large even t via D-lattice (t=40)
    Veven = num(wf, 40) / den(wf, 40)
    Vodd = num(wf, 41) / den(wf, 41)
    d2_large = Veven + (num(wf, 42) / den(wf, 42)) - 2 * Vodd  # Delta^2 V(40)
    print(f"  w={wv}: G_even={float(Ge):.5f} G_odd={float(Go):.5f}  Go-Ge={float(Go-Ge):+.5f} (need in [0,1])")
    print(f"          V(40)={float(Veven):.5f}~Ge  V(41)={float(Vodd):.5f}~Go  "
          f"Delta^2V(40)={float(d2_large):+.5f}  -2(Go-Ge)={float(-2*(Go-Ge)):+.5f}")

hr("6. Finite-t correction  V(t) - G_parity(t):  sign & rate")
for wv in ['0.05', '0.3', '0.7']:
    wf = mp.mpf(wv)
    Ge, Go = G_even_inf(wf), G_odd_inf(wf)
    print(f"  w={wv}:")
    for t in range(2, 14):
        Gpar = Ge if t % 2 == 0 else Go
        corr = num(wf, t) / den(wf, t) - Gpar
        print(f"    t={t:2d} ({'even' if t%2==0 else 'odd '}):  V - G_parity = {float(corr):+.3e}")

hr("7. (a) elementary core:  G_odd - G_even <= 1  scan over w in (0,1)")
worst = mp.mpf(-1)
worst_w = None
for k in range(1, 100):
    wf = mp.mpf(k) / 100
    d = G_odd_inf(wf) - G_even_inf(wf)
    if d > worst:
        worst, worst_w = d, wf
print(f"  sup_w (G_odd-G_even) ~ {float(worst):.6f} at w={float(worst_w):.2f}  (claim: <= 1)")
print(f"  limits:  w->0 gives Go-Ge->1 ;  w->1 gives Go-Ge->0")
for wv in ['0.01', '0.1', '0.5', '0.9', '0.99']:
    wf = mp.mpf(wv)
    print(f"    w={wv}: Go-Ge={float(G_odd_inf(wf)-G_even_inf(wf)):.6f}")

hr("7b. (a) as a HALF-INTEGER vs INTEGER discrete-Gaussian variance excess (in j)")
# G_even = Var_D over even D=2j = 4 Var_j(integer-centred Gaussian r^{j^2})
# G_odd  = Var_D over odd  D=2j+1 = 4 Var_{j+1/2}(half-integer-centred) ; centre at 0 both in D.
# Claim equivalent:  Var_j^{odd-lattice}(j+1/2 centred, but measured about 0) ...
# Direct: (G_odd - G_even)/4 = quarter-integer excess.  Check (G_odd-G_even) in [0,1].
for wv in ['0.05', '0.3', '0.6', '0.9']:
    wf = mp.mpf(wv)
    print(f"  w={wv}: (G_odd-G_even)={float(G_odd_inf(wf)-G_even_inf(wf)):.6f}  /4 ="
          f" {float((G_odd_inf(wf)-G_even_inf(wf))/4):.6f}")

print("\nDONE.")
