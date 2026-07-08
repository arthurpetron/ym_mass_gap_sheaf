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
