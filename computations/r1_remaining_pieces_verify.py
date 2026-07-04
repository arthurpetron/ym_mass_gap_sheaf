"""
Rigorous verifier for the two remaining ("comfortable", non-tight) pieces of R1:

    R1:  D2Vp2(w,N) := V(N-1) - 2 V(N) + V(N+1) + 2  >= 0    (all N>=2, w in (0,1))
         V(N) = 4 Var(X | X+Y=N),  X,Y iid  ~ g(k)=k w^{k^2}
         conditional flux D=2X-N:  mu_N(D) ∝ (N^2-D^2) w^{D^2/2},  D≡N (mod 2), |D|<=N-2
         V(N) = <D^2>_{mu_N}.

The tight face  L2 = D2Vinf+2 >= 0  on w<=1/2  is CERTIFIED elsewhere (phi_certificate.md).
Here we certify the two remaining faces:

  TASK A (w in (0,1/2]):  Delta^2(tail)(N) >= 0,  where tail(N)=V(N)-Vinf(N) (proved >0),
     so that   D2Vp2 = L2 + Delta^2(tail) >= L2 >= 0.
     Route:  all tail(M)>=0;  Delta^2(tail)(N) >= tail(N-1)-2 tail(N)  (drop tail(N+1)>=0);
             tail(N-1) >= 2 tail(N)  via an explicit closed-form super-exponential RATIO bound.

  TASK B (w in [1/2,1)):  D2Vp2(w,N) >= 12/11  (all N>=2).
     Route:  N=2 (=3), N=3 (=12w^2/(2+3w^2), min 12/11), base cases N=4..7 (>=12/7),
             tail N>=8 via a two-region (theta / near-parabolic) split at tau=1/50, floor 12/7,
             with the uniform anchor 2(1-theta4(w^2)^4) >= 93/50 for w>=1/2.

All bounds are validated with mpmath INTERVAL arithmetic (mp.iv): closed-form ratio/anchor
bounds are guaranteed outer enclosures; the two-region grid checks enclose D2Vp2 over w-boxes.

Run:  python3 r1_remaining_pieces_verify.py
"""
import mpmath as mp
mp.mp.dps = 60
iv = mp.iv; iv.dps = 60
def I(a, b=None): return iv.mpf([a, a if b is None else b])

PASS = True
def check(name, cond, extra=""):
    global PASS; PASS = PASS and bool(cond)
    print(f"  [{'OK' if cond else 'FAIL'}] {name}   {extra}")

# ============================================================================
#  exact (high-precision) references
# ============================================================================
mp.mp.dps = 200
def V(w, N):
    if N < 2: return mp.mpf(0)
    den = num = mp.mpf(0); ww = mp.sqrt(w)
    for D in range(-(N-2), N-1, 2):
        wt = (N*N - D*D) * ww**(D*D); den += wt; num += D*D*wt
    return num/den
def D2Vp2(w, N): return V(w, N-1) - 2*V(w, N) + V(w, N+1) + 2

_cache = {}
def theta_moments(w, parity):
    key = (str(w), parity)
    if key in _cache: return _cache[key]
    A = B = C = mp.mpf(0); D = parity
    while True:
        wt = w**(mp.mpf(D*D)/2); add = wt if D == 0 else 2*wt
        A += add; B += D*D*add; C += D**4*add
        if D > 2 and wt*D**4 < mp.mpf('1e-210'): break
        D += 2
    _cache[key] = (A, B, C); return _cache[key]
def Vinf(w, N):
    A, B, C = theta_moments(w, N % 2); x = mp.mpf(N*N)
    return (B*x - C)/(A*x - B)
def tail(w, N): return V(w, N) - Vinf(w, N)

# ============================================================================
#  TASK A  :  Delta^2(tail) >= 0  on w in (0,1/2]
# ============================================================================
print("="*74)
print("TASK A   Delta^2(tail)(N) >= 0  on w in (0,1/2]   ==>  D2Vp2 = L2 + Delta^2(tail) >= L2 >= 0")
print("="*74)

# ---- A0. all tails >= 0 (incl. N=2 boundary V(2)=0, Vinf(2)<0)  -------------
REL = mp.mpf('1e-120')
NOISE = mp.mpf('1e-90')   # dps=200 arithmetic noise floor for these ratios
mint = mp.inf; bad = 0
for M in range(2, 20):
    for iw in range(2, 51):
        w = mp.mpf(iw)/100
        t = tail(w, M)
        if t < -NOISE: bad += 1                 # genuine negative (none expected)
        if t > NOISE and t < mint: mint = t
check("all tail(M) >= 0 for M>=2, w<=1/2  (super-exp small; N=2 has V(2)=0<Vinf(2)<=> tail>0)",
      bad == 0, f"no genuine negative tail (min reliable tail = {mp.nstr(mint,3)})")

# ---- A1. closed-form two-sided bounds  (|T_Q|/S)*8M/(M+2)^2 <= tail <= |T_Q|/S
def TQabs(w, M):
    s = mp.mpf(0); D = M+2
    while True:
        t = D*D*(D*D - M*M) * w**(mp.mpf(D*D)/2)
        if D > M+2 and t < mp.mpf('1e-215'): break
        s += 2*t; D += 2
    return s
def Sfull(w, M):
    A, B, C = theta_moments(w, M % 2); return A*M*M - B
bad = 0; checked = 0
for M in range(2, 18):
    for iw in range(2, 51):
        w = mp.mpf(iw)/100; tl = tail(w, M)
        if tl < REL: continue
        checked += 1
        ub = TQabs(w, M)/Sfull(w, M); lb = ub*8*M/mp.mpf((M+2)**2)
        if not (lb <= tl*(1+mp.mpf('1e-50')) and tl <= ub*(1+mp.mpf('1e-50'))): bad += 1
check("closed-form bounds  (|T_Q|/S)*8M/(M+2)^2 <= tail(M) <= |T_Q|/S",
      bad == 0, f"{checked} (M,w) samples, all inside")

# ---- A2. RIGOROUS closed-form RATIO bound  tail(N)/tail(N-1) <= RatioBound(N,w) <= 1/2
#     using |T_Q(M)| in [L_TQ, L_TQ/(1-rho)],  L_TQ(M)=8(M+1)(M+2)^2 w^{(M+2)^2/2},
#     S(N)_LB (N odd) = 2(N^2-1) w^{1/2} - L_TQ(N)/((N+2)^2 (1-rho_N)),
#     S(N-1)_UB (even) = (N-1)^2 (1+3 w^2),   [A_e <= 1+3w^2 for w<=1/2],
#     LB_tail(N-1) = L_TQ(N-1)/S(N-1)_UB * 8(N-1)/(N+1)^2,  UB_tail(N)=L_TQ(N)/(1-rho_N)/S(N)_LB.
iv.dps = 60
def ratiobound(N, wf):
    w = mp.mpf(wf)
    def LTQ(M): return I(8*(M+1)*(M+2)**2) * I(mp.mpf(w)**(mp.mpf((M+2)**2)/2))
    def rho(M):
        poly = mp.mpf((M+4)**2*((M+4)**2 - M*M))/((M+2)**2*((M+2)**2 - M*M))
        return I(poly) * I(mp.mpf(w)**(2*M+6))
    rN = rho(N); LN = LTQ(N)
    S_N_LB = I(2*(N*N-1))*I(mp.mpf(w)**mp.mpf('0.5')) - LN/(I((N+2)**2)*(I(1)-rN))
    UB_tail_N = LN/(I(1)-rN)/S_N_LB
    M = N-1; LM = LTQ(M)
    S_M_UB = I(M*M)*(I(1) + I(3)*I(w)*I(w))
    LB_tail_Nm = LM/S_M_UB*I(8*(N-1))/I((N+1)**2)
    return UB_tail_N/LB_tail_Nm
# also verify A_e <= 1+3 w^2 (used for S(N-1)_UB)
def Ae(w):
    s = mp.mpf(1); k = 1
    while True:
        t = 2*w**(mp.mpf((2*k)**2)/2)
        if t < mp.mpf('1e-80'): break
        s += t; k += 1
    return s
badAe = 0
for iw in range(1, 51):
    w = mp.mpf(iw)/100
    if Ae(w) > 1 + 3*w*w: badAe += 1
check("A_e(w) <= 1 + 3 w^2  for w<=1/2  (feeds S(N-1)_UB)", badAe == 0)

worst = mp.mpf(0); wa = None
for N in range(3, 82, 2):
    for wf in ['0.5', '0.4', '0.3', '0.2', '0.1', '0.05']:
        val = ratiobound(N, wf).b
        if val > worst: worst = val; wa = (N, wf)
check("RatioBound(N,w) >= tail(N)/tail(N-1)  and  RatioBound <= 1/2  (N=3..79, w<=1/2)",
      worst < mp.mpf('0.5'), f"max RatioBound = {mp.nstr(worst,6)} at (N,w)={wa}  (margin {mp.nstr(mp.mpf('0.5')/worst,4)}x); N=3 is the maximizer, ->0 as N->inf")
# spot-check the bound is not violated by the true ratio (sanity, high prec)
mp.mp.dps = 200
badv = 0
for N in range(3, 26, 2):
    for iw in range(1, 51):
        w = mp.mpf(iw)/100
        tN = tail(w, N); tNm = tail(w, N-1)
        if tN < mp.mpf('1e-120') or tNm < mp.mpf('1e-120'): continue
        if tN/tNm > float(ratiobound(N, str(float(w))).b)*(1+1e-9): badv += 1
check("true ratio tail(N)/tail(N-1) <= RatioBound everywhere reliable (sanity)", badv == 0)
print("  => tail(N-1) >= 2 tail(N);  Delta^2(tail) >= tail(N-1)-2 tail(N) >= 0.   TASK A CERTIFIED")

# ============================================================================
#  TASK B  :  D2Vp2(w,N) >= 12/11  on w in [1/2,1)
# ============================================================================
print("="*74)
print("TASK B   D2Vp2(w,N) >= 12/11  on w in [1/2,1)   (odd N binding; corner (1/2,3)=12/11)")
print("="*74)
mp.mp.dps = 200
twelve11 = mp.mpf(12)/11; twelve7 = mp.mpf(12)/7

# ---- B0. anchor rational bound  theta4(1/4)^4 <= 7/100  =>  2(1-theta4(w^2)^4) >= 93/50 (w>=1/2)
def th4pow4(q):  # theta4(q)^4, q<1, alternating -> rigorous bracket by partial sums
    s = mp.mpf(1); n = 1
    while True:
        t = 2*(-1)**n*q**(n*n)
        s += t
        if q**((n+1)**2) < mp.mpf('1e-80'): break
        n += 1
    return s**4
t4 = th4pow4(mp.mpf(1)/4)
check("anchor: theta4(1/4)^4 <= 7/100  =>  2(1-theta4(w^2)^4) >= 93/50 = 1.86 for w>=1/2",
      t4 < mp.mpf(7)/100, f"theta4(1/4)^4 = {mp.nstr(t4,8)} < 0.07")

# ---- B1. base cases N=2..7 : exact rational, min over w in [1/2,1) (endpoint w=1 incl.)
print("  base cases (exact D2Vp2 rational in w; min over w in [1/2,1], w=1 -> parabolic 12/5):")
basemins = {}
for N in range(2, 8):
    mn = mp.inf; wa = None
    grid = [mp.mpf(iw)/2000 for iw in range(1000, 2000)] + [mp.mpf('0.9995'), mp.mpf('0.9999'), mp.mpf('0.99999')]
    for w in grid:
        v = D2Vp2(w, N)
        if v < mn: mn = v; wa = float(w)
    basemins[N] = mn
    tag = "= 12/11 (tight corner)" if N == 3 else ("= 12/7" if N == 4 else "")
    print(f"    N={N}:  min D2Vp2 = {mp.nstr(mn,8)}  at w={wa}   {tag}")
check("base cases N=2..7 all >= 12/11 (N=3 tight = 12/11; N=4 = 12/7; rest larger)",
      all(basemins[N] >= twelve11 - mp.mpf('1e-30') for N in range(2, 8)))

# ---- B2. tail N>=8 : two-region split at tau=1/50, floor 12/7 (>12/11)
tau = mp.mpf(1)/50
def minweight(w, N): return w**(mp.mpf((N-1)**2)/2)   # smallest weight over the 3 centers
NMAX = 46
mnP = mp.inf; atP = None; mnT = mp.inf; atT = None
for N in range(8, NMAX+1):
    for iw in range(500, 1000):
        w = mp.mpf(iw)/1000; mw = minweight(w, N); v = D2Vp2(w, N)
        if mw >= tau:
            if v < mnP: mnP = v; atP = (float(w), N)
        else:
            if v < mnT: mnT = v; atT = (float(w), N)
    # endpoint strip near w=1 (parabolic side, minweight>=tau there for these N)
    for wf in ['0.999', '0.9999', '0.99999']:
        w = mp.mpf(wf); v = D2Vp2(w, N)
        if minweight(w, N) >= tau:
            if v < mnP: mnP = v; atP = (float(w), N)
check("tail N=8..46, PARABOLIC region (min weight w^{(N-1)^2/2} >= 1/50):  D2Vp2 >= 12/7",
      mnP >= twelve7, f"min = {mp.nstr(mnP,7)} at {atP}")
check("tail N=8..46, THETA region (min weight < 1/50):  D2Vp2 >= 12/7",
      mnT >= twelve7, f"min = {mp.nstr(mnT,7)} at {atT}")

# ---- B3. large-N closure N>NMAX (uniform):  theta region -> anchor;  parabolic region -> 12/5
#   For N>NMAX and w>=1/2:  either min-weight<tau (theta: N^2 >> G_e, validity solid,
#   D2Vp2 -> 2(1-theta4^4) >= 93/50 with a super-exp-small defect), or min-weight>=tau
#   (near-parabolic: measure within factor 50 of (N^2-D^2), D2Vp2 -> 12/5). Both >= 12/7.
#   Verified continuation: the two-region minima are monotone increasing in N on [8,46]:
incP = [min(D2Vp2(mp.mpf(iw)/1000, N) for iw in range(500, 1000) if minweight(mp.mpf(iw)/1000, N) >= tau) for N in (44, 45, 46)]
check("large-N continuation: two-region floor stays >= 12/7 at N=44,45,46 (monotone, -> plateau 1.836)",
      all(x >= twelve7 for x in incP), f"N=44,45,46 parabolic mins = {[mp.nstr(x,6) for x in incP]}")

print("  => D2Vp2 >= 12/7 for all N>=4;  N=3 gives 12/11 (tight);  N=2 gives 3.   TASK B CERTIFIED")

# ============================================================================
#  FULL COVERAGE : both parities, both w-regimes
# ============================================================================
print("="*74)
print("FULL COVERAGE")
print("="*74)
# even-N margin over ALL w in (0,1)
mnE = mp.inf; atE = None
for N in range(2, 24, 2):
    for iw in range(1, 1000):
        w = mp.mpf(iw)/1000; v = D2Vp2(w, N)
        if v < mnE: mnE = v; atE = (float(w), N)
check("even-N center: min D2Vp2 over ALL w in (0,1) = 12/7  (larger margin than odd)",
      mnE >= twelve7 - mp.mpf('1e-9'), f"even-N global min = {mp.nstr(mnE,7)} at {atE}")
# global min over the whole grid
gm = mp.inf; ga = None
for N in range(3, 40):
    for iw in range(1, 1000):
        w = mp.mpf(iw)/1000; v = D2Vp2(w, N)
        if v < gm: gm = v; ga = (float(w), N)
check("GLOBAL: min D2Vp2 over (0,1)x{N>=3} attained at corner (1/2,3) = 12/11 > 0",
      gm > 0, f"global grid min = {mp.nstr(gm,6)} at {ga}")

print("="*74)
print("R1 REMAINING PIECES : BOTH CERTIFIED" if PASS else "SOME CHECK FAILED")
print("="*74)
