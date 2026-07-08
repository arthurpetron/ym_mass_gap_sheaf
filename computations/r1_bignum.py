import mpmath as mp
mp.mp.dps=50
# level-t weights rho_t(D) ∝ (M^2-D^2) w^{D^2/2}, D≡t, |D|<=t, M=t+2
def moments(w,t):
    M=t+2; th=mp.mpf(0); xi=mp.mpf(0); ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    den=M*M*th-xi; num=M*M*xi-ze
    return num/den, den   # V(t), den_t (up to common factor, fine for sign)
def V(w,t): return moments(w,t)[0]

def slack_norm(w,s):
    # Δ²V+2 (the normalized bracket sign) -- exactly what must be >=0
    return V(w,s)-2*V(w,s+1)+V(w,s+2)+2

print("=== min over w in (0,1) of (Δ²V(s)+2), and argmin, for s up to 60 ===")
grid=[mp.mpf(i)/2000 for i in range(1,2000)]
for s in list(range(0,20))+[30,40,50,60,80,100]:
    vals=[(slack_norm(g,s),g) for g in grid]
    mn,am=min(vals)
    print(f" s={s:>3} ({'even' if s%2==0 else 'odd '}): min(Δ²V+2)={mp.nstr(mn,6):>12} @w={float(am):.4f}   (>=0: {mn>=0})")
