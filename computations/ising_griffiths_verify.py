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
import mpmath as mp
mp.mp.dps = 80

def coeffW(w, s):
    return (s+1) * mp.power(w, s*(s+2))

def cumulants_D(w, t):
    # measure mu_t(p) propto coeffW(w,p)coeffW(w,t-p); D=t-2p
    Z=mp.mpf(0); m2=mp.mpf(0); m4=mp.mpf(0)
    for p in range(0,t+1):
        wt=coeffW(w,p)*coeffW(w,t-p); D=t-2*p
        Z+=wt; m2+=D*D*wt; m4+=D**4*wt
    m2/=Z; m4/=Z
    kappa4 = m4 - 3*m2*m2   # 4th cumulant (mean 0 by symmetry)
    return m2, m4, kappa4

def Vf(w,t):
    return cumulants_D(w,t)[0]

# --- 1. Sharpness of -2 as w->0 at small t ---
print("=== small-w: Delta^2 V(t) approaching -2 ? (t=2) ===")
for w in [mp.mpf('0.1'),mp.mpf('0.01'),mp.mpf('1e-3'),mp.mpf('1e-4'),mp.mpf('1e-6'),mp.mpf('1e-9')]:
    d2 = Vf(w,4)-2*Vf(w,3)+Vf(w,2)
    print(f" w={mp.nstr(w,3):>8}  Delta^2 V(2) = {mp.nstr(d2,12)}")
print("Leading small-w: expand? check ratio (d2+2)/w^k")
for w in [mp.mpf('1e-2'),mp.mpf('1e-3'),mp.mpf('1e-4')]:
    d2 = Vf(w,4)-2*Vf(w,3)+Vf(w,2)
    print(f"  w={mp.nstr(w,3)}  (d2+2)={mp.nstr(d2+2,8)}  /w^3={mp.nstr((d2+2)/w**3,6)}  /w^2={mp.nstr((d2+2)/w**2,6)}")

# --- 2. global min of Delta^2 V + 2 with fine grid incl very small & near-1 w ---
print("\n=== global min Delta^2 V + 2 (fine) ===")
gmin=mp.mpf('1e9'); arg=None
ws=[mp.mpf(10)**mp.mpf(e) for e in [-6,-5,-4,-3,-2.5,-2,-1.5,-1,-0.7,-0.5,-0.3,-0.15,-0.05,-0.02,-0.005,-0.001]]
for w in ws:
    for t in range(1,80):
        d2=Vf(w,t+2)-2*Vf(w,t+1)+Vf(w,t)
        if d2+2<gmin: gmin=d2+2; arg=(mp.nstr(w,4),t,mp.nstr(d2,10))
print(" min(Delta^2 V+2)=",mp.nstr(gmin,8)," at (w,t,d2)=",arg)

# --- 3. Lebowitz/GHS candidate: sign of kappa4(D) (4th Ursell of the spin sum) ---
print("\n=== sign of 4th cumulant kappa4(D) over grid (Lebowitz u4<=0 candidate) ===")
maxk4=mp.mpf('-1e18'); argmax=None; allneg=True; count_pos=0; count_tot=0
for we in range(1,200):
    w=mp.mpf(we)/200
    for t in range(1,50):
        k4=cumulants_D(w,t)[2]; count_tot+=1
        if k4>0: count_pos+=1; allneg=False
        if k4>maxk4: maxk4=k4; argmax=(float(w),t,mp.nstr(k4,8))
print(f" kappa4<=0 everywhere? {allneg};  #positive={count_pos}/{count_tot};  max kappa4={mp.nstr(maxk4,8)} at {argmax}")

# --- 4. Is the ensemble ferromagnetic?  Effective pair coupling sign in D^2 weight ---
# weight propto (N^2-D^2) q^{D^2/2}: the q^{D^2/2}=exp(-beta D^2/2), beta=|ln w|>0 => confining (antiferro sign)
print("\n=== effective quadratic coefficient of D in log-weight (sign) ===")
for w in [mp.mpf('0.3'),mp.mpf('0.9'),mp.mpf('0.99')]:
    beta=-mp.log(w)
    print(f" w={float(w):.2f}: log q^(D^2/2) = -(beta/2)D^2, beta={mp.nstr(beta,6)} > 0  => CONFINING/antiferro-sign")

# --- 5. relation between Delta^2 V and kappa4: test candidate that d2V is bounded below using k4<=0 ---
print("\n=== compare Delta^2 V(t)  vs  a kappa4-based proxy ===")
for w in [mp.mpf('0.5'),mp.mpf('0.9'),mp.mpf('0.99')]:
    for t in [2,3,10,20]:
        d2=Vf(w,t+2)-2*Vf(w,t+1)+Vf(w,t)
        k4a=cumulants_D(w,t)[2]; k4b=cumulants_D(w,t+1)[2]; k4c=cumulants_D(w,t+2)[2]
        print(f" w={float(w):.2f} t={t:2d}: d2V={mp.nstr(d2,8):>12}  k4(t..t+2)=[{mp.nstr(k4a,5)},{mp.nstr(k4b,5)},{mp.nstr(k4c,5)}]")
import mpmath as mp
mp.mp.dps = 60

def coeffW(w, s): return (s+1)*mp.power(w, s*(s+2))
def Vf(w,t):
    Z=mp.mpf(0);m2=mp.mpf(0)
    for p in range(0,t+1):
        wt=coeffW(w,p)*coeffW(w,t-p);D=t-2*p;Z+=wt;m2+=D*D*wt
    return m2/Z

# --- Saturation channel at w->0: which p dominates, and V limit by parity ---
print("=== w->0 dominant fusion channel & V limit ===")
w=mp.mpf('1e-8')
for t in range(1,9):
    # find dominant p (min total Casimir p(p+2)+(t-p)(t-p+2))
    best=min(range(0,t+1), key=lambda p: p*(p+2)+(t-p)*(t-p+2))
    print(f" t={t} parity={'even' if t%2==0 else 'odd'}  V->{mp.nstr(Vf(w,t),6)}  dominant p={best} D={t-2*best}")
print(" => even t: V->0 (D=0 channel); odd t: V->1 (D=+-1 channel) => Delta^2V = 0-2*1+0 = -2 (SHARP)")
print(" Note: C4(s)=s(s+2), Delta^2 C4 = 2, so floor -2 = -Delta^2(Casimir).")

# --- Discrete log-concavity of rho(D)=(N^2-D^2) q^{D^2/2} in D (step 2) ---
print("\n=== is rho(D)=(N^2-D^2)q^{D^2/2} log-concave in D? rho(D)^2 >= rho(D-2)rho(D+2) ===")
def rho(w,N,D):
    v=N*N-D*D
    if v<=0: return mp.mpf(0)
    return v*mp.power(w, mp.mpf(D*D)/2)
lc_ok=True; worst=mp.mpf('1e9')
for we in range(1,100):
    w=mp.mpf(we)/100
    for t in range(2,40):
        N=t+2
        Ds=[d for d in range(-(N-2),N-1,2)]  # support, step2, matching parity of N
        for D in Ds:
            if (D-2) in Ds and (D+2) in Ds:
                lhs=rho(w,N,D)**2; rhs=rho(w,N,D-2)*rho(w,N,D+2)
                if rhs>0:
                    r=lhs/rhs
                    if r<worst: worst=r
                    if lhs<rhs*(1-mp.mpf('1e-40')): lc_ok=False
print(f" log-concave everywhere? {lc_ok};  min ratio rho^2/(rho-rho+) = {mp.nstr(worst,8)} (>=1 confirms)")

# --- Does discrete log-concavity of the FUSION coeff coeffW hold (PF2)? ---
print("\n=== coeffW log-concave? coeffW(s)^2 >= coeffW(s-1)coeffW(s+1) ===")
ok=True; wr=mp.mpf('1e9')
for we in range(1,100):
    w=mp.mpf(we)/100
    for s in range(1,40):
        lhs=coeffW(w,s)**2; rhs=coeffW(w,s-1)*coeffW(w,s+1)
        r=lhs/rhs
        if r<wr: wr=r
        if lhs<rhs*(1-mp.mpf('1e-40')): ok=False
print(f" coeffW log-concave (PF2)? {ok}; min ratio={mp.nstr(wr,8)}")
# analytic: coeffW(s)^2/(coeffW(s-1)coeffW(s+1)) = (s+1)^2/(s(s+2)) * w^{2s(s+2)-((s-1)(s+1)+(s+1)(s+3))}
# exponent: 2s(s+2) - [(s^2-1)+(s^2+4s+3)] = 2s^2+4s - [2s^2+4s+2] = -2. So ratio=(s+1)^2/(s(s+2)) * w^{-2} >= w^{-2} >1.
print("  analytic ratio = (s+1)^2/(s(s+2)) * w^{-2} = [1+1/(s(s+2))]*w^{-2} > 1  => STRICTLY log-concave, unconditional")

# --- parity dependence of kurtosis sign (the cross-parity obstruction) ---
print("\n=== kurtosis sign by parity at moderate w (why no single-sign Ursell) ===")
def k4(w,t):
    Z=mp.mpf(0);m2=mp.mpf(0);m4=mp.mpf(0)
    for p in range(0,t+1):
        wt=coeffW(w,p)*coeffW(w,t-p);D=t-2*p;Z+=wt;m2+=D*D*wt;m4+=D**4*wt
    m2/=Z;m4/=Z; return m4-3*m2*m2
for w in [mp.mpf('0.4'),mp.mpf('0.6')]:
    ev=[k4(w,t) for t in range(10,20,2)]; od=[k4(w,t) for t in range(11,21,2)]
    print(f" w={float(w):.1f}: even-sector kappa4 ~ {mp.nstr(ev[1],4)} (>0), odd-sector kappa4 ~ {mp.nstr(od[1],4)} (<0)")
