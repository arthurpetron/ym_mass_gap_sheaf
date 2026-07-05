import mpmath as mp
mp.mp.dps=35
def pars(u,K=120):
    A=B=Cc=mp.mpf(0)
    for k in range(-K,K+1): t=u**(k*k); A+=t;B+=4*k*k*t;Cc+=16*k**4*t
    a=b=c=mp.mpf(0)
    for k in range(0,K): t=u**(k*(k+1)); a+=t;b+=(2*k+1)**2*t;c+=(2*k+1)**4*t
    return B/A,b/a,(A*Cc-B*B)/(A*A),(a*c-b*b)/(a*a)
def D2Vinf2(u,s):  # infinite-theta Delta^2 V + 2 with EXACT m=s+2
    Ve,Vo,Vare,Varo=pars(u); m=s+2
    if s%2==0:
        if Ve>=m*m or Ve>=(m+2)**2 or Vo>=(m+1)**2: return None
        return 2*(Ve-Vo)+2 - Vare*(1/(m*m-Ve)+1/((m+2)**2-Ve)) + 2*Varo/((m+1)**2-Vo)
    else:
        if Vo>=m*m or Vo>=(m+2)**2 or Ve>=(m+1)**2: return None
        return 2*(Vo-Ve)+2 - Varo*(1/(m*m-Vo)+1/((m+2)**2-Vo)) + 2*Vare/((m+1)**2-Ve)
def V(w,t):
    n=t+2; S0=S2=mp.mpf(0)
    for D in range(-t,t+1,2):
        g=w**(mp.mpf(D*D)/2); wt=(n*n-D*D)*g; S0+=wt; S2+=wt*D*D
    return S2/S0
def P(t): return mp.mpf(t*(t+4))/5
def D2e(w,s): return (P(s)-V(w,s))-2*(P(s+1)-V(w,s+1))+(P(s+2)-V(w,s+2))

tau=mp.mpf(1)/50
print(f"Two-region split at tau={float(tau)} (rho=w^{{(s+2)^2/2}}):")
# THETA region rho<tau: check D2Vinf2 (exact m) >=0
theta_min=mp.mpf('9'); theta_bad=0
for s in range(7,90):
    # rho<tau <=> w < tau^{2/(s+2)^2}; scan w in [1/2, that)
    whi=tau**(mp.mpf(2)/((s+2)**2))
    for i in range(1,120):
        w=mp.mpf('0.5')+(whi-mp.mpf('0.5'))*mp.mpf(i)/120
        if w<=mp.mpf('0.5') or w>=whi: continue
        val=D2Vinf2(w*w,s)
        if val is None: theta_bad+=1; continue
        if val<theta_min: theta_min=val; ta=(s,float(w))
print(f"  THETA region (rho<tau): min D2Vinf2 (exact m) = {float(theta_min):.5f} at {ta}; #invalid(V>=m^2)={theta_bad}")
# PARABOLIC region rho>=tau: check D2e<=12/5
para_max=-mp.mpf('9')
for s in range(7,90):
    wlo=tau**(mp.mpf(2)/((s+2)**2))
    for i in range(0,120):
        w=wlo+(1-wlo)*mp.mpf(i)/120
        if w>=1: w=mp.mpf('0.9999999')
        d=D2e(w,s)
        if d>para_max: para_max=d; pa=(s,float(w))
print(f"  PARABOLIC region (rho>=tau): max Δ²e = {float(para_max):.5f} at {pa}  (need <=12/5=2.4)")
print(f"\n  => If theta_min>=0 AND para_max<=2.4 AND no invalid in theta region: CLOSURE STRUCTURE HOLDS")
