import mpmath as mp
mp.mp.dps = 60

# coeffW w s = (s+1) * w^(s*(s+2))
def coeffW(w, s):
    return (s+1) * mp.power(w, s*(s+2))

# measure mu_t(p) propto coeffW(w,p)*coeffW(w,t-p), p=0..t ; D = t-2p ; V(t)=<D^2>
def moments_direct(w, t):
    Z = mp.mpf(0); m2 = mp.mpf(0); m4 = mp.mpf(0); m1 = mp.mpf(0)
    for p in range(0, t+1):
        wt = coeffW(w,p)*coeffW(w,t-p)
        D = t - 2*p
        Z += wt; m1 += D*wt; m2 += D*D*wt; m4 += D**4*wt
    return m1/Z, m2/Z, m4/Z

def V(w,t):
    _,m2,_ = moments_direct(w,t); return m2

# ---- check reformulation: weight propto (N^2 - D^2) * q^(D^2/2), N=t+2, q=w ----
def moments_reform(w, t):
    N = t+2; q = w
    Z=mp.mpf(0); m2=mp.mpf(0); m4=mp.mpf(0)
    for a in range(1, N):  # a=p+1 in 1..N-1
        D = 2*a - N
        wt = (N*N - D*D) * mp.power(q, mp.mpf(D*D)/2)
        Z+=wt; m2+=D*D*wt; m4+=D**4*wt
    return m2/Z, m4/Z

# ---- check <a^2>_N identity: V(t)+t^2 = 4<a^2>_N -4N+4 ----
def a2_canonical(w,t):
    N=t+2
    Z=mp.mpf(0); s=mp.mpf(0)
    for a in range(1,N):
        b=N-a
        wt = a*b*mp.power(w, a*a+b*b)
        Z+=wt; s+=a*a*wt
    return s/Z

print("=== VERIFY reformulations (w, t): Vdirect  Vreform  |diff| ; Vplust2 vs 4a2-4N+4 ===")
for w in [mp.mpf('0.3'), mp.mpf('0.7'), mp.mpf('0.9'), mp.mpf('0.99')]:
    for t in [3,4,7,8,15,16]:
        vd = V(w,t)
        m2r,_ = moments_reform(w,t)
        lhs = vd + t*t
        rhs = 4*a2_canonical(w,t) - 4*(t+2) + 4
        print(f"w={float(w):.2f} t={t:2d}  Vd={float(vd):12.6f}  reformdiff={float(abs(vd-m2r)):.2e}  a2id_diff={float(abs(lhs-rhs)):.2e}")

# ---- MAIN TEST: Delta^2 V(t) = V(t+2)-2V(t+1)+V(t) >= -2 ? ----
print("\n=== min over grid of  Delta^2 V(t)+2  (should be >=0). Also cross-parity form ===")
gmin = mp.mpf('1e9'); argmin=None
ws = [mp.mpf(x)/1000 for x in range(5,1000,5)]  # 0.005..0.995
for w in ws:
    for t in range(1, 60):
        d2 = V(w,t+2) - 2*V(w,t+1) + V(w,t)
        val = d2 + 2
        if val < gmin:
            gmin = val; argmin=(float(w),t,float(d2))
print("min(Delta^2 V + 2) =", mp.nstr(gmin,10), " at (w,t,Delta2V)=", argmin)

# near w->1 limit behaviour of V and Delta^2 V
print("\n=== w->1 limit: V(t) and Delta^2 V(t) at w=0.999999 ===")
w=mp.mpf('0.999999')
for t in range(1,12):
    print(f" t={t:2d} V={float(V(w,t)):10.4f}")
