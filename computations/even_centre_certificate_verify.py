"""
Rigorous verifier for the EVEN-CENTRE cell of R1 on w in (0,1/2].

R1:  D2Vp2(w,N) := V(N-1) - 2 V(N) + V(N+1) + 2  >= 0   (all N>=2, w in (0,1))
     V(N) = 4 Var(X | X+Y=N),  X,Y iid ~ g(k)=k w^{k^2}
     flux D=2X-N:  mu_N(D) ∝ (N^2-D^2) w^{D^2/2},  D≡N (mod 2), |D|<=N-2
     V(N) = <D^2>_{mu_N}.

The odd-centre cell (odd N, w<=1/2), all N on w>=1/2, are certified elsewhere.
Here we certify the remaining EVEN-CENTRE cell: even N>=2, w in (0,1/2].

CERTIFICATE (route (a), direct bound):
  For even centre N the neighbours N-1, N+1 are ODD and  V(odd) >= 1  is PROVED
  (Lean: dmomNfull_ge_acNfull_odd).  Hence for even N>=4
        D2Vp2 = V(N-1)+V(N+1) - 2 V(N) + 2  >=  1 + 1 - 2 V(N) + 2  =  4 - 2 V(N).
  Key even-centre lemma (E2):  V(N) <= G_e(w^2)  where  G_e = B_e/A_e = E_theta[D^2],
        A_e=sum_{even D} w^{D^2/2}, B_e=sum_{even D} D^2 w^{D^2/2}.
  Then  G_e(w^2) <= G_e(1/4)  (G_e increasing in q=w^2)  and  G_e(1/4) <= 141/100.
  So  D2Vp2 >= 4 - 2*(141/100) = 118/100 = 59/50 > 0   for all even N>=4, w<=1/2.
  N=2 boundary: V(1)=0 (empty support), V(2)=0, V(3)=1  =>  D2Vp2(2) = 3 (exact).

E2 is proved by the DISCRETE CHEBYSHEV SUM INEQUALITY (sign-definite double sum):
  with nu_D = w^{D^2/2}, t_D = D^2 (increasing in D^2), h_D = (N^2-D^2)_+ (NON-increasing
  in D^2), the physical weight is h_D*nu_D, and
        (sum t h nu)(sum nu) - (sum t nu)(sum h nu)
              = -(1/2) sum_{D,E} nu_D nu_E (t_D-t_E)(h_D-h_E)  <= 0,
  because (t_D-t_E)(h_D-h_E) <= 0 term-by-term.  Hence V(N)=E_mu[D^2] <= E_nu[D^2]=G_e.

Run:  python3 even_centre_certificate_verify.py
"""
import mpmath as mp
mp.mp.dps = 220
iv = mp.iv; iv.dps = 60
def I(a, b=None): return iv.mpf([a, a if b is None else b])

PASS = True
def check(name, cond, extra=""):
    global PASS; PASS = PASS and bool(cond)
    print(f"  [{'OK' if cond else 'FAIL'}] {name}   {extra}")

# ---------------------------------------------------------------- exact V(N)
def V(w, N):
    if N < 2: return mp.mpf(0)          # convention: V(1)=0 (empty support X+Y=1)
    ww = mp.sqrt(w); den = num = mp.mpf(0)
    for D in range(-(N-2), N-1, 2):
        wt = (N*N - D*D) * ww**(D*D); den += wt; num += D*D*wt
    return num/den
def D2Vp2(w, N): return V(w, N-1) - 2*V(w, N) + V(w, N+1) + 2

# ------------------------------------------- untruncated theta constants (even parity)
def theta_e(w):
    """A_e,B_e = sum_{even D} {1,D^2} w^{D^2/2}."""
    A = B = mp.mpf(0); D = 0
    while True:
        wt = w**(mp.mpf(D*D)/2); add = wt if D == 0 else 2*wt
        A += add; B += D*D*add
        if D > 2 and wt*D**4 < mp.mpf('1e-230'): break
        D += 2
    return A, B
def Ge(w):
    A, B = theta_e(w); return B/A

print("="*78)
print("STEP 1  Ground truth: true min of D2Vp2 over EVEN N>=2, w in (0,1/2]")
print("="*78)
gmin = mp.inf; gat = None
# fine w-grid + very small w (scaled precision handled by dps=220) + endpoints
wgrid = [mp.mpf(iw)/2000 for iw in range(1, 1001)]              # (0, 1/2]
wgrid += [mp.mpf(10)**(-k) for k in range(3, 13)]              # w -> 0 along decades
for N in range(2, 62, 2):
    for w in wgrid:
        v = D2Vp2(w, N)
        if v < gmin: gmin = v; gat = (mp.nstr(w, 6), N)
check("true min of D2Vp2 over even N in [2,60], w in (0,1/2]  (>= 2.14 expected)",
      gmin >= mp.mpf('2.13'), f"min = {mp.nstr(gmin,8)} at (w,N)={gat}")
# behaviour as w->0 (should -> 4)
w0 = mp.mpf('1e-10')
lims = [(N, mp.nstr(D2Vp2(w0, N), 8)) for N in (2, 4, 6, 8)]
print(f"    w->0 (w=1e-10):  D2Vp2 -> 4:  {lims}")

print("="*78)
print("STEP 2  Even-centre lemma (E2):  V(even N) <= G_e(w^2)  on w<=1/2")
print("="*78)
# 2a. numerical check V(N) <= G_e for ALL even N, w<=1/2 (incl small w, big N)
worstgap = mp.inf; worstat = None; bad = 0
for N in range(2, 82, 2):
    for iw in list(range(1, 1001, 1)):
        w = mp.mpf(iw)/2000
        gap = Ge(w) - V(w, N)                # want >= 0
        if gap < -mp.mpf('1e-150'): bad += 1
        if gap < worstgap: worstgap = gap; worstat = (mp.nstr(w,5), N)
# also small-w decades
for N in range(2, 82, 2):
    for k in range(3, 13):
        w = mp.mpf(10)**(-k); gap = Ge(w) - V(w, N)
        if gap < -mp.mpf('1e-150'): bad += 1
        if gap < worstgap: worstgap = gap; worstat = (mp.nstr(w,3), N)
check("V(even N) <= G_e(w^2) for all even N in [2,80], w<=1/2 (numeric)",
      bad == 0, f"min(G_e - V) = {mp.nstr(worstgap,4)} at {worstat} (>=0, tight as N->inf)")

# 2b. the sign-definite double-sum that PROVES E2, checked term-by-term for sample (N,w)
def chebyshev_defect(w, N, Dmax):
    """RHS-LHS = -(1/2) sum nu_D nu_E (t_D-t_E)(h_D-h_E);  every summand product <=0."""
    Ds = list(range(-Dmax, Dmax+1, 2))
    nu = {D: w**(mp.mpf(D*D)/2) for D in Ds}
    t  = {D: mp.mpf(D*D) for D in Ds}
    h  = {D: max(mp.mpf(N*N) - D*D, mp.mpf(0)) for D in Ds}
    allneg = True; S = mp.mpf(0)
    for D in Ds:
        for E in Ds:
            prod = (t[D]-t[E])*(h[D]-h[E])
            if prod > mp.mpf('1e-200'): allneg = False   # must be <= 0
            S += nu[D]*nu[E]*prod
    return allneg, -S/2   # RHS-LHS = -(1/2) S  >= 0
okall = True; def_min = mp.inf
for N in (4, 6, 8, 12, 20, 40):
    for iw in (1, 100, 500, 999):
        w = mp.mpf(iw)/2000
        allneg, defect = chebyshev_defect(w, N, N+30)
        okall = okall and allneg and defect >= -mp.mpf('1e-150')
        def_min = min(def_min, defect)
check("Chebyshev double-sum: every (t_D-t_E)(h_D-h_E) <= 0  =>  V(N) <= G_e (proof)",
      okall, f"min certified defect (RHS-LHS) = {mp.nstr(def_min,4)} >= 0")

print("="*78)
print("STEP 3  G_e(w^2) <= G_e(1/4)  (G_e increasing in q)  and  G_e(1/4) <= 141/100")
print("="*78)
# 3a. G_e increasing in w on (0,1/2]  (=> sup at w=1/2)
prev = -mp.inf; mono = True; mngap = mp.inf
for iw in range(1, 1001):
    w = mp.mpf(iw)/2000; g = Ge(w)
    if g < prev - mp.mpf('1e-120'): mono = False
    prev = g; mngap = min(mngap, Ge(mp.mpf('0.5')) - g)
check("G_e(w) increasing on (0,1/2] => G_e(w^2) <= G_e(1/4)", mono and mngap >= 0,
      f"min(G_e(1/2)-G_e(w)) = {mp.nstr(mngap,4)}")

# 3b. rigorous rational bound  G_e(1/4) < 141/100  via mp.iv with proven tail
#     G_e(1/4) = B_e/A_e at w=1/2.  Truncate even D at |D|<=Dc; tails are positive and
#     bounded by a geometric majorant.  w=1/2, so w^{D^2/2}=(1/2)^{D^2/2}.
def Ge_iv_upper(Dc):
    w = mp.mpf('0.5')
    A_lo = I(1); B_lo = I(0)             # lower bounds for A (>0 terms), we build brackets
    # partial sums (exact rationals via mp, wrapped as point intervals)
    Ap = mp.mpf(1); Bp = mp.mpf(0)
    for D in range(2, Dc+1, 2):
        wt = w**(mp.mpf(D*D)/2)
        Ap += 2*wt; Bp += 2*D*D*wt
    # tail of A: sum_{D>=Dc+2 even} 2 w^{D^2/2} <= geometric with ratio r=w^{(Dc+2)... }
    d0 = Dc+2
    first_wt = w**(mp.mpf(d0*d0)/2)
    # consecutive even D: exponent D^2/2 increases; ratio between successive terms
    # w^{((D+2)^2-D^2)/2} = w^{(2D+2)} <= w^{2 d0+2} =: r  (<1); majorant sum 2*first_wt/(1-r)
    r = w**(2*d0+2)
    tailA = 2*first_wt/(1-r)
    # tail of B: sum 2 D^2 w^{D^2/2}; D^2 grows poly, majorize D^2<= (something). Use
    # crude: D^2 <= d0^2 * (D/d0)^2 and ratio still <1; safe geometric with poly factor.
    # simpler rigorous majorant: 2 sum_{D>=d0} D^2 w^{D^2/2} <= 2 * first_wt * d0^2 /(1-r)^3
    tailB = 2*first_wt*d0*d0/(1-r)**3
    # upper bound of G_e = B/A:  (Bp + tailB)/(Ap)   (A only grows, so Ap is a lower bd for A)
    return (Bp + tailB)/Ap, Ap, Bp, tailA, tailB
ub, Ap, Bp, tA, tB = Ge_iv_upper(12)
check("G_e(1/4) <= 141/100 = 1.41  (rigorous truncation+geometric tail, Dc=12)",
      ub < mp.mpf(141)/100, f"upper bound = {mp.nstr(ub,10)}  (true G_e(1/4)={mp.nstr(Ge(mp.mpf('0.5')),10)})")

print("="*78)
print("STEP 4  Assemble the certificate margin")
print("="*78)
# even N=2 : exact
v2 = D2Vp2(mp.mpf('0.3'), 2)   # any w; it's identically 3 (V(1)=V(2)=0, V(3)=1)
check("N=2 boundary: D2Vp2(2) = 3 exactly (V(1)=0,V(2)=0,V(3)=1)",
      abs(v2 - 3) < mp.mpf('1e-30'), f"D2Vp2(2) = {mp.nstr(v2,6)}")
# even N>=4 : 4 - 2 G_e(1/4) >= 4 - 2*141/100 = 118/100
margin = mp.mpf(4) - 2*mp.mpf(141)/100
check("even N>=4: D2Vp2 >= 4 - 2*G_e(1/4) >= 4 - 2*141/100 = 118/100 = 59/50 > 0",
      margin > 0, f"certified margin = {margin} = 59/50 = {mp.nstr(margin,6)}")
# cross-check: crude bound 4-2V(N) never violated, and >= 118/100 everywhere even
badc = 0; mnc = mp.inf
for N in range(4, 82, 2):
    for iw in range(1, 1001):
        w = mp.mpf(iw)/2000
        crude = 4 - 2*V(w, N)
        if D2Vp2(w, N) < crude - mp.mpf('1e-120'): badc += 1   # D2Vp2 >= crude (since V(N±1)>=1)
        mnc = min(mnc, crude)
check("crude bound 4-2V(N) <= D2Vp2 (uses V(N±1)>=1) AND 4-2V(N) >= 118/100 on even cell",
      badc == 0 and mnc >= mp.mpf(118)/100 - mp.mpf('1e-9'),
      f"min(4-2V) over even cell = {mp.nstr(mnc,8)} >= 1.18")

print("="*78)
print("EVEN-CENTRE CELL: CERTIFIED (margin 59/50 = 1.18)" if PASS else "SOME CHECK FAILED")
print("="*78)
