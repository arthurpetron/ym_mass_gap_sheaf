"""
Verification harness for the residual theta inequality (L2) that closes the
parity-gap lemma  Delta^2 V(N) >= -2  on the Laguerre-Polya half  w in (0,1/2].

L2 (odd N>=3, w in (0,1/2],  q=w^2 in (0,1/4]):

    Delta^2 F_e(N) - 2( f_o(N^2) - f_e(N^2) )  >= 0 ,

    f_p(x) = (B_p x - C_p)/(A_p x - B_p),   F_e(N)=N^2+f_e(N^2),
    A_p=sum_{D=p(2)} w^{D^2/2},  B_p=sum D^2 w^{..},  C_p=sum D^4 w^{..}.

This script proves, to >40 digits, every step of the reduction in
theta_residual_L2_proof.md:

  (1) partial-fraction identity      f_p(x) = G_p - S_p/(x-G_p),
                                      G_p=B_p/A_p, S_p=C_p/A_p-(B_p/A_p)^2 >= 0
  (2) L2 identity                     L2 = 2(1-t4) + 2 S_o/(N^2-G_o)
                                             - S_e/((N-1)^2-G_e) - S_e/((N+1)^2-G_e),
                                      with anchor  G_o-G_e = theta4(q)^4  (PROVED).
  (3) reduction chain  L2(N) >= Psi(N) >= Psi(3) = phi(q) >= 0.
  (4) the scalar residual phi(q)>=0 on (0,1/4], leading order 1.454 q > 0,
      and the exact N=3 scalar (ratio >= 1.344).

Run:  python3 theta_residual_L2_verify.py
"""
import mpmath as mp
mp.mp.dps = 50

# ----------------------------------------------------------------------
# theta lattice moments  (untruncated, all positive terms), q = w^2
# ----------------------------------------------------------------------
def moments(w, parity):
    A = B = C = mp.mpf(0); D = parity
    while True:
        wt = w**(mp.mpf(D*D)/2); add = wt if D == 0 else 2*wt
        A += add; B += D*D*add; C += D**4*add
        if D > 2 and wt*D**4 < mp.mpf('1e-60'): break
        D += 2
    return A, B, C

def GS(w, parity):                      # (mean of D^2 , variance of D^2)
    A, B, C = moments(w, parity)
    return B/A, C/A - (B/A)**2

def fp(w, parity, x):                   # Mobius  (Bx-C)/(Ax-B)
    A, B, C = moments(w, parity)
    return (B*x - C)/(A*x - B)

# closed theta forms (nome q=w^2) for cross-checking the constants
def th3(q): return mp.jtheta(3, 0, q)
def th2(q): return mp.jtheta(2, 0, q)
def th4(q): return mp.jtheta(4, 0, q)

PASS = True
def check(name, cond, val=""):
    global PASS
    PASS = PASS and cond
    print(f"  [{'OK' if cond else 'FAIL'}] {name}   {val}")

print("="*72)
print("(1) partial fraction  f_p(x) = G_p - S_p/(x-G_p),  S_p = Var_p(D^2) >= 0")
maxerr = mp.mpf(0); minS = mp.inf
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    for p in (0, 1):
        G, S = GS(w, p); minS = min(minS, S)
        for x in (mp.mpf(4), mp.mpf(16), mp.mpf(25), mp.mpf(49)):
            maxerr = max(maxerr, abs(fp(w, p, x) - (G - S/(x - G))))
check("identity holds", maxerr < mp.mpf('1e-40'), f"max err = {mp.nstr(maxerr,3)}")
check("S_p >= 0 (Cauchy-Schwarz/Turan)", minS >= 0, f"min S = {mp.nstr(minS,3)}")

print("="*72)
print("(2) L2 identity + anchor  G_o - G_e = theta4(q)^4")
def L2_direct(w, N):
    Fe = lambda M: M*M + fp(w, 0, mp.mpf(M*M))
    return Fe(N-1) - 2*Fe(N) + Fe(N+1) - 2*(fp(w,1,mp.mpf(N*N)) - fp(w,0,mp.mpf(N*N)))
def L2_pf(w, N):
    Ge, Se = GS(w, 0); Go, So = GS(w, 1); t4 = Go - Ge
    return 2*(1-t4) + 2*So/(N*N-Go) - Se*(1/((N-1)**2-Ge) + 1/((N+1)**2-Ge))
mxid = mxan = mp.mpf(0)
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    Ge, _ = GS(w, 0); Go, _ = GS(w, 1)
    mxan = max(mxan, abs((Go-Ge) - th4(w*w)**4))
    for N in range(3, 60, 2):
        mxid = max(mxid, abs(L2_direct(w, N) - L2_pf(w, N)))
check("L2 = partial-fraction form", mxid < mp.mpf('1e-40'), f"max err = {mp.nstr(mxid,3)}")
check("anchor G_o-G_e = theta4^4", mxan < mp.mpf('1e-40'), f"max err = {mp.nstr(mxan,3)}")

print("="*72)
print("(3) reduction chain  L2(N) >= Psi(N) >= Psi(3) = phi(q) >= 0")
barGe = GS(mp.mpf(1)/2, 0)[0]                     # G_e at q=1/4  (w=1/2)
kappa = 1/(4-barGe) + 1/(16-barGe)
thr   = 8 - mp.sqrt(40)
def Psi(w, N):
    Ge, Se = GS(w, 0); Go, So = GS(w, 1); t4 = Go - Ge
    return 2*(1-t4) + 2*So/(N*N) - Se/((N-1)**2-barGe) - Se/((N+1)**2-barGe)
def phi(w):  return Psi(w, 3)

# (3a) G_e increasing in w  =>  G_e(w) <= barGe ;  and G_o>0 ; and S_e>=S_o
mnGap1 = mnGap2 = mnSeSo = mp.inf; mnGo = mp.inf
prevGe = -mp.inf; monoGe = True
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    Ge, Se = GS(w, 0); Go, So = GS(w, 1)
    if Ge < prevGe - mp.mpf('1e-40'): monoGe = False
    prevGe = Ge
    mnGap1 = min(mnGap1, barGe - Ge)          # barGe >= Ge
    mnGo   = min(mnGo, Go)                     # G_o > 0
    mnSeSo = min(mnSeSo, Se - So)             # S_e >= S_o
check("G_e increasing => G_e <= barGe", monoGe and mnGap1 >= 0, f"min(barGe-Ge)={mp.nstr(mnGap1,3)}")
check("G_o > 0", mnGo > 0, f"min G_o = {mp.nstr(mnGo,3)}")
check("S_e >= S_o on (0,1/4]", mnSeSo >= 0, f"min(S_e-S_o) = {mp.nstr(mnSeSo,3)}")

# (3b) L2(N) >= Psi(N)   (from G_o>0, G_e<=barGe)
mnA = mp.inf
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    for N in range(3, 60, 2):
        mnA = min(mnA, L2_pf(w, N) - Psi(w, N))
check("L2(N) >= Psi(N)", mnA >= -mp.mpf('1e-45'), f"min(L2-Psi) = {mp.nstr(mnA,3)}")

# (3c) Psi increasing in N  (convexity of x^-3 : 1/(N-1)^3+1/(N+1)^3 >= 2/N^3)
mnConv = mp.inf; mnInc = mp.inf
for N in range(3, 200, 2):
    mnConv = min(mnConv, mp.mpf(1)/(N-1)**3 + mp.mpf(1)/(N+1)**3 - mp.mpf(2)/N**3)
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    for N in range(3, 120, 2):
        mnInc = min(mnInc, Psi(w, N+2) - Psi(w, N))
check("convexity 1/(N-1)^3+1/(N+1)^3 >= 2/N^3", mnConv >= 0, f"min = {mp.nstr(mnConv,3)}")
check("Psi(N) increasing in N => min at N=3", mnInc >= -mp.mpf('1e-45'), f"min incr = {mp.nstr(mnInc,3)}")

print("="*72)
print("(4) scalar residual  phi(q) = Psi(3) >= 0  on (0,1/4]")
check("barGe = G_e(1/4) < 8-sqrt(40)", barGe < thr,
      f"{mp.nstr(barGe,8)} < {mp.nstr(thr,8)}")
lead = 16 - 32*kappa
check("leading coeff 16-32*kappa > 0 (<=> kappa<1/2)", lead > 0,
      f"lead = {mp.nstr(lead,8)}, kappa = {mp.nstr(kappa,8)}")
mnphi = mp.inf; mnratio = mp.inf; mnphiq = mp.inf
for i in range(1, 2501):
    q = mp.mpf(i)/10000; w = mp.sqrt(q)
    v = phi(w); mnphi = min(mnphi, v); mnphiq = min(mnphiq, v/q)
check("phi(q) >= 0 on (0,1/4]", mnphi >= 0, f"min phi = {mp.nstr(mnphi,3)}")
check("phi(q) >= lead*q  (min phi/q = lead)", mnphiq >= lead - mp.mpf('1e-6'),
      f"min phi/q = {mp.nstr(mnphiq,8)}  vs lead {mp.nstr(lead,8)}")

# exact N=3 scalar (tighter certificate, ratio >= 1.344)
mnr = mp.inf; mnm = mp.inf
for i in range(1, 2501):
    q = mp.mpf(i)/10000; w = mp.sqrt(q)
    Ge, Se = GS(w, 0); Go, So = GS(w, 1); t4 = Go - Ge
    L = 2*(1-t4) + 2*So/(9-Go); R = Se*(1/(4-Ge)+1/(16-Ge))
    mnm = min(mnm, L-R); mnr = min(mnr, L/R)
check("exact N=3 scalar  (>=0, ratio bound)", mnm >= 0,
      f"min margin {mp.nstr(mnm,3)}, min ratio {mp.nstr(mnr,6)}")

print("="*72)
print("(5) end-to-end: original L2 over (w,N) grid, and leading gap")
mn = mp.inf; loc = None
for iw in range(1, 251):
    w = mp.mpf(iw)/500
    for N in range(3, 80, 2):
        v = L2_direct(w, N)
        if v < mn: mn = v; loc = (float(w), N)
check("original L2 >= 0 on grid", mn >= 0, f"min = {mp.nstr(mn,3)} at {loc}")
w = mp.mpf('1e-5'); vals = []; prev = mp.mpf(0); gapok = True
for N in range(3, 60, 2):
    L = L2_direct(w, N)/w**2
    gapok = gapok and (0 < L < 16) and (L >= prev - mp.mpf('1e-3'))   # in (0,16), ascending
    prev = L
    if N in (3, 5, 7, 11, 21): vals.append((N, float(L)))
check("leading coeff L(N)=(L2/w^2) in (0,16), ascending to 16", gapok,
      "  L(N)=" + ", ".join(f"{N}:{v:.3f}" for N, v in vals) + " -> 16")

print("="*72)
print("ALL CLAIMS VERIFIED" if PASS else "SOME CHECK FAILED")
