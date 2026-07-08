import mpmath as mp
mp.mp.dps=40
def V(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    den=M*M*th-xi; num=M*M*xi-ze
    return num/den
def sl(w,s): return V(w,s)-2*V(w,s+1)+V(w,s+2)+2

grid=[mp.mpf(i)/4000 for i in range(1,4000)]
print("=== EVEN s: inf over w of (Δ²V+2)/f(w) for candidate envelopes f ===")
print(f"{'s':>4} {'/w^2':>12} {'/(w^2(1-w^2))':>16} {'/(w^2(1-w^2)^2)':>18} {'/(w^2(1+w^2))':>15}")
for s in [2,4,6,8,10,20,40,80,160]:
    r1=r2=r3=r4=mp.inf
    for g in grid:
        v=sl(g,s); w2=g*g
        r1=min(r1, v/w2)
        r2=min(r2, v/(w2*(1-w2)))
        r3=min(r3, v/(w2*(1-w2)**2))
        r4=min(r4, v/(w2*(1+w2)))
    print(f"{s:>4} {mp.nstr(r1,6):>12} {mp.nstr(r2,6):>16} {mp.nstr(r3,6):>18} {mp.nstr(r4,6):>15}")

print("\n=== the ratio (Δ²V+2)/w^2 at w->0 (=leading coeff C(s)+C(s+2)) and its min location ===")
for s in [2,4,6,8,20,80]:
    C=lambda t: mp.mpf(8*t*(t+4))/(t+2)**2
    lead=C(s)+C(s+2)
    vals=[(sl(g,s)/(g*g),g) for g in grid]
    mn,am=min(vals)
    print(f" s={s:>3}: lead C(s)+C(s+2)={float(lead):.4f}, min (Δ²V+2)/w^2 = {mp.nstr(mn,6)} @w={float(am):.3f}")
