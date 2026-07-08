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
