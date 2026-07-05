import mpmath as mp
mp.mp.dps=30
# tilted parabolic ensemble mu_t^mu(D) ∝ (n^2-D^2) e^{-mu D^2/2}, |D|<=t, D≡t(2), n=t+2
def moms_mu(mu,t):
    n=t+2; S0=S2=S4=mp.mpf(0)
    for D in range(-t,t+1,2):
        g=mp.e**(-mu*mp.mpf(D*D)/2); wt=(n*n-D*D)*g
        S0+=wt; S2+=wt*D*D; S4+=wt*D**4
    return S0,S2,S4
def Vmu(mu,t):
    S0,S2,S4=moms_mu(mu,t); return S2/S0
def Varmu(mu,t):  # Var_mu(D^2) = <D^4> - <D^2>^2
    S0,S2,S4=moms_mu(mu,t); return S4/S0-(S2/S0)**2
def P(t): return mp.mpf(t*(t+4))/5
def Varpar(t): return mp.mpf(8*t*(t-1)*(t+4)*(t+5))/175
def D2Varpar(s): return mp.mpf(96*(s*s+6*s+7))/175
# physical V at weight w: mu=-ln w
def Vphys(w,t): return Vmu(-mp.log(w),t)
def D2V2(w,s): return Vphys(w,s)-2*Vphys(w,s+1)+Vphys(w,s+2)+2

print("(1) EXACT formulas:")
for t in [7,8,12]:
    print(f"  t={t}: P={P(t)} vs {Vmu(0,t)} ; Varpar={Varpar(t)} vs Varmu(0)={mp.nstr(Varmu(0,t),8)}")
print(f"  Δ²Varpar(7)=96·98/175={D2Varpar(7)} vs numeric {Varpar(7)-2*Varpar(8)+Varpar(9)}")

print("\n(2) tilt identity dV/dmu = -1/2 Var_mu(D^2):")
for (mu,t) in [(mp.mpf('0.1'),8),(mp.mpf('0.5'),12)]:
    h=mp.mpf('1e-8'); dV=(Vmu(mu+h,t)-Vmu(mu-h,t))/(2*h); print(f"  mu={float(mu)},t={t}: dV/dmu={mp.nstr(dV,8)} vs -1/2 Varmu={mp.nstr(-Varmu(mu,t)/2,8)}")

print("\n(3) LEMMA (C): Δ²Var_mu(s) <= Δ²Var_par(s) for all mu>=0, s>=7 :")
def D2Varmu(mu,s): return Varmu(mu,s)-2*Varmu(mu,s+1)+Varmu(mu,s+2)
worst=-mp.mpf('9')
for s in range(7,60):
    for i in range(0,200):
        mu=mp.mpf(i)/200*mp.mpf(8)
        d=D2Varmu(mu,s)-D2Varpar(s)
        if d>worst: worst=d; wa=(s,float(mu))
print(f"  max(Δ²Var_mu - Δ²Var_par) = {mp.nstr(worst,6)} at {wa}  (must be <=0)")

print("\n(4) RATIONAL certificate + NO GAP (Lean-usable threshold (1-w)/w <= 35/(4(s²+6s+7))):")
# parabolic (rational): (1-w)/w <= 35/(4K), K=s²+6s+7  => w >= 4K/(4K+35). cert floor = 12/5-(λ/2)D2Varpar
# theta: w < w_rat(s); need D2V2>=0 there (and in practice the exact LB). Check actual D2V2>=0 on WHOLE [1/2,1].
badpar=0; mincertfloor=mp.mpf('9'); thetamin=mp.mpf('9')
for s in range(7,120):
    K=s*s+6*s+7; w_rat=mp.mpf(4*K)/(4*K+35)
    # parabolic region w in [w_rat,1): certificate floor
    for i in range(0,60):
        w=w_rat+(1-w_rat)*mp.mpf(i)/60
        if w>=1: w=mp.mpf('0.999999')
        lam=-mp.log(w)
        certfloor=mp.mpf(12)/5-(lam/2)*D2Varpar(s)
        if certfloor<mincertfloor: mincertfloor=certfloor
        if D2V2(w,s)<0: badpar+=1
    # theta region w in [1/2, w_rat): actual D2V2 (proxy for the LBθ>=1.78)
    for i in range(0,60):
        w=mp.mpf('0.5')+(w_rat-mp.mpf('0.5'))*mp.mpf(i)/60
        if w<mp.mpf('0.5') or w>=w_rat: continue
        v=D2V2(w,s)
        if v<thetamin: thetamin=v
print(f"  parabolic: min certfloor(12/5-(λ/2)Δ²Varpar) on rational region = {mp.nstr(mincertfloor,6)} (>=0 wanted); D2V2 violations={badpar}")
print(f"  theta: min actual D2V2 on rational theta region [1/2,w_rat) = {mp.nstr(thetamin,6)} (>0 wanted)")
