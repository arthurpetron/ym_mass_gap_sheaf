"""
Rigorous two-region certificate for the terminal scalar residual

    phi(q) >= 0   for all real q in (0, 1/4]        (q = w^2)

    phi(q) = 2(1 - theta4(q)^4) + (2/9) S_o(q) - kappa * S_e(q),
    kappa  = 1/(4 - barGe) + 1/(16 - barGe),   barGe = G_e(1/4),
    G_p = B_p/A_p,  S_p = C_p/A_p - (B_p/A_p)^2,
    A_p,B_p,C_p = Sum_{D = p (mod 2)} D^{0,2,4} q^{D^2/4}   (untruncated).

This script is the machine-checkable companion to phi_certificate.md.  Everything
is validated with mpmath INTERVAL arithmetic (mp.iv): every truncated theta sum is
enclosed by [partial sum, partial sum + rigorous tail bound], and phi, phi', phi''
are propagated through the quotient/product rules in iv, so each printed enclosure
is a guaranteed outer bound on the true range over the stated q-interval.

Design (see memo):
    q0 = 1/16,  c = 7/5,  delta = 1/10.
    Region I  (0, 1/16] : phi convex (phi'' >= 37/5 > 0) + phi(0)=0, phi'(0)=alpha,
                          alpha = 16-32 kappa >= 7/5   ==>  phi(q) >= alpha q >= (7/5) q.
    Region II [1/16,1/4]: uniform grid q_i = 1/16 + i/64 (M=12 intervals), rigorous
                          node lower bounds, Lipschitz L=4 (sup|phi'| <= 3.942 < 4),
                          min(node lows) - L*h/2 >= delta = 1/10.

Run:  python3 phi_certificate_verify.py
"""
import mpmath as mp
mp.mp.dps = 60
iv = mp.iv; iv.dps = 60

Kser = 20                       # series index k up to Kser  (even D<=40, odd D<=41)
TAIL = mp.mpf('1e-40')          # uniform rigorous tail bound (verified conservative)
q4   = mp.mpf(1)/4

def I(a, b=None):
    return iv.mpf([a, a if b is None else b])

PASS = True
def check(name, cond, extra=""):
    global PASS; PASS = PASS and bool(cond)
    print(f"  [{'OK' if cond else 'FAIL'}] {name}   {extra}")

# ---------------------------------------------------------------------------
# 0. tail bounds are conservative: true tails past k=Kser at q=1/4 << TAIL
# ---------------------------------------------------------------------------
def truetail_even(K):
    s = mp.mpf(0)
    for k in range(K+1, K+60):
        e = k*k
        s += 32*k**4 * e*(e-1) * q4**(e-2)      # covers up to 2nd-deriv weight of C_e
    return s
def truetail_odd(K):
    s = mp.mpf(0)
    for k in range(K+1, K+60):
        e = k*(k+1); d = 2*k+1
        s += d**4 * max(1, e*(e-1)) * q4**max(e-2, 0)
    return s
check("uniform tail 1e-40 dominates true tails past k=20 at q=1/4",
      truetail_even(Kser) < TAIL and truetail_odd(Kser) < TAIL,
      f"true even/odd tails ~ {mp.nstr(truetail_even(Kser),3)}, {mp.nstr(truetail_odd(Kser),3)}")

# explicit GEOMETRIC tail majorant at the certified D_max = 24 (weight D^4, q=1/4)
Dm = 24
rho24  = (mp.mpf(Dm+2)/Dm)**4 * q4**(Dm+1)
first24 = mp.mpf(Dm+2)**4 * q4**((Dm+2)**2//4)
tail24 = first24/(1-rho24)
check("explicit geometric tail bound at D_max=24 is < 1e-90 (weight D^4)",
      tail24 < mp.mpf('1e-90'), f"bound = {mp.nstr(tail24,3)}")

# ---------------------------------------------------------------------------
# 1. iv series evaluators  ->  (S, S', S'')  over q-interval Q
# ---------------------------------------------------------------------------
def pos_series(Q, k0, cfun, efun):
    S = I(0); Sp = I(0); Spp = I(0)
    for k in range(k0, Kser+1):
        c = cfun(k); e = efun(k)
        S += I(c)*Q**e
        if e >= 1: Sp  += I(c*e)*Q**(e-1)
        if e >= 2: Spp += I(c*e*(e-1))*Q**(e-2)
    tl = iv.mpf([0, TAIL])
    return S+tl, Sp+tl, Spp+tl

def even_ABC(Q):
    A, Ap, App = pos_series(Q, 1, lambda k: 2,       lambda k: k*k)
    A = A + I(1)
    B = pos_series(Q, 1, lambda k: 8*k*k,   lambda k: k*k)
    C = pos_series(Q, 1, lambda k: 32*k**4, lambda k: k*k)
    return (A, Ap, App), B, C
def odd_m(Q):
    return (pos_series(Q, 0, lambda k: 1,          lambda k: k*(k+1)),
            pos_series(Q, 0, lambda k: (2*k+1)**2, lambda k: k*(k+1)),
            pos_series(Q, 0, lambda k: (2*k+1)**4, lambda k: k*(k+1)))
def theta4(Q):
    S = I(1); Sp = I(0); Spp = I(0)
    for n in range(1, Kser+1):
        c = 2*(-1)**n; e = n*n
        S += I(c)*Q**e; Sp += I(c*e)*Q**(e-1)
        if e >= 2: Spp += I(c*e*(e-1))*Q**(e-2)
    tl = iv.mpf([-TAIL, TAIL])
    return S+tl, Sp+tl, Spp+tl

def quot(U, V):
    (u, up, upp) = U; (v, vp, vpp) = V
    return (u/v, (up*v - u*vp)/v**2,
            (upp*v**2 - u*vpp*v - 2*up*vp*v + 2*u*vp**2)/v**3)
def sub(A, B): return (A[0]-B[0], A[1]-B[1], A[2]-B[2])
def scal(a, A): a = I(a); return (a*A[0], a*A[1], a*A[2])
def sq(A):
    (a, ap, app) = A
    return (a*a, 2*a*ap, 2*ap*ap + 2*a*app)

# barGe, kappa as rigorous rational-endpoint intervals (established below in 2)
barGe_lo = mp.mpf('1.4095014689866763774417')
barGe_hi = mp.mpf('1.4095014689866763774418')
kap = I(1)/(I(4)-I(barGe_lo, barGe_hi)) + I(1)/(I(16)-I(barGe_lo, barGe_hi))

def phi_derivs(Q):
    (A, B, C) = even_ABC(Q)
    Ge = quot(B, A); Se = sub(quot(C, A), sq(Ge))
    (m0, m1, m2) = odd_m(Q)
    Go = quot(m1, m0); So = sub(quot(m2, m0), sq(Go))
    t4 = theta4(Q); t4_4 = sq(sq(t4))
    one = (I(1), I(0), I(0))
    return (scal(2, sub(one, t4_4))[0] + scal(mp.mpf(2)/9, So)[0] - kap*Se[0],
            scal(2, sub(one, t4_4))[1] + scal(mp.mpf(2)/9, So)[1] - kap*Se[1],
            scal(2, sub(one, t4_4))[2] + scal(mp.mpf(2)/9, So)[2] - kap*Se[2])

# ---------------------------------------------------------------------------
# 2. rigorous rational enclosure of barGe = B_e/A_e at q=1/4  (partial sum + tail)
# ---------------------------------------------------------------------------
Ap = mp.mpf(1); Bp = mp.mpf(0)
for k in range(1, Kser+1):
    t = q4**(k*k); Ap += 2*t; Bp += 8*k*k*t
tailA = 2*q4**((Kser+1)**2)/(1 - q4**(2*Kser+1))
tailB = 8*(Kser+1)**2*q4**((Kser+1)**2)/(1 - (mp.mpf(Kser+1)/Kser)**2*q4**(2*Kser+1))
bGe_lo = Bp/(Ap+tailA); bGe_hi = (Bp+tailB)/Ap
check("barGe in [1.4095014689866763774417, ...18]  (rigorous)",
      bGe_lo > barGe_lo and bGe_hi < barGe_hi, f"[{mp.nstr(bGe_lo,22)}, {mp.nstr(bGe_hi,22)}]")

# ---------------------------------------------------------------------------
# 3. leading coefficient:  73 barGe^2 - 1140 barGe + 1472 >= 0  ==>  alpha >= 7/5
# ---------------------------------------------------------------------------
qval = lambda g: 73*g*g - 1140*g + 1472
check("73 barGe^2 - 1140 barGe + 1472 >= 0  (<=> kappa<=73/160 <=> alpha>=7/5)",
      qval(barGe_hi) > 0 and qval(barGe_lo) > 0, f"value = {mp.nstr(qval(barGe_hi),6)}")
alpha_iv = I(16) - I(32)*kap
check("alpha = 16-32 kappa  and  alpha - 7/5 > 0",
      alpha_iv.a - mp.mpf(7)/5 > 0, f"alpha in [{mp.nstr(alpha_iv.a,18)}, {mp.nstr(alpha_iv.b,18)}], alpha-7/5={mp.nstr(alpha_iv.a-mp.mpf(7)/5,5)}")

# ---------------------------------------------------------------------------
# 4. REGION I : phi convex on [0,1/16]  (phi'' >= 37/5)  + phi(0)=0, phi'(0)=alpha
# ---------------------------------------------------------------------------
q0 = mp.mpf(1)/16; NI = 8; h1 = q0/NI; mnpp = mp.inf
for i in range(NI):
    mnpp = min(mnpp, phi_derivs(I(i*h1, (i+1)*h1))[2].a)
check("Region I: phi''(q) >= 37/5 on [0,1/16]  (=> phi convex)",
      mnpp >= mp.mpf(37)/5, f"phi'' lower bound = {mp.nstr(mnpp,7)}")
pd0 = phi_derivs(I(0))
check("phi(0) = 0 (enclosure contains 0)  and  phi'(0) = alpha >= 7/5",
      pd0[0].a <= 0 <= pd0[0].b and pd0[1].a - mp.mpf(7)/5 > 0,
      f"phi(0) in [{mp.nstr(pd0[0].a,3)}, {mp.nstr(pd0[0].b,3)}], phi'(0) in [{mp.nstr(pd0[1].a,16)}, {mp.nstr(pd0[1].b,16)}]")

# ---------------------------------------------------------------------------
# 5. REGION II : phi >= delta = 1/10 on [1/16,1/4]  via grid + Lipschitz L=4
# ---------------------------------------------------------------------------
a = q0; b = mp.mpf(1)/4; delta = mp.mpf(1)/10
NL = 64; hL = (b-a)/NL; supd = mp.mpf(0)
for i in range(NL):
    d1 = phi_derivs(I(a+i*hL, a+(i+1)*hL))[1]
    supd = max(supd, abs(d1.a), abs(d1.b))
L = mp.mpf(4)
check("Region II: sup|phi'| on [1/16,1/4] <= L = 4  (64 iv-pieces)",
      supd <= L, f"sup|phi'| = {mp.nstr(supd,7)}")
h = mp.mpf(1)/64; M = int((b-a)/h + mp.mpf('0.5'))
nodes = [a + i*h for i in range(M+1)]
lows  = [phi_derivs(I(n))[0].a for n in nodes]
worst = mp.inf
for i in range(M):
    worst = min(worst, min(lows[i], lows[i+1]) - L*h/2 - delta)
check(f"Region II: grid h=1/64, M={M}, L*h/2=1/32, min(node lows)-L*h/2 >= delta=1/10",
      worst >= 0, f"worst per-interval margin = {mp.nstr(worst,6)}; min node lb = {mp.nstr(min(lows),7)}")

print("="*72)
print("phi(q) >= 0 on (0,1/4] : CERTIFIED" if PASS else "SOME CHECK FAILED")
