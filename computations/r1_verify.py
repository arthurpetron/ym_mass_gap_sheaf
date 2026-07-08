import mpmath as mp
mp.mp.dps=30
def V(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def sl(w,s): return V(w,s)-2*V(w,s+1)+V(w,s+2)+2
C=mp.mpf(144)/25
gmin=mp.inf; worst=None
for s in list(range(0,40))+[50,70,100,150,250]:
    r=mp.inf
    for i in range(1,2000):
        g=mp.mpf(i)/2000
        val=sl(g,s)/(g*g*(1-g*g))
        if val<r: r=val
    if r<gmin: gmin=r; worst=s
print(f"GLOBAL inf (Δ²V+2)/(w^2(1-w^2)) = {mp.nstr(gmin,10)} at s={worst}")
print(f"144/25 = {mp.nstr(C,10)};  inf >= 144/25 - tol : {gmin >= C - mp.mpf('1e-4')}")
# also raw floor: min Δ²V over all s,w (should be > -2)
fl=mp.inf
for s in list(range(0,40))+[100,250]:
    for i in range(1,2000):
        g=mp.mpf(i)/2000
        d=sl(g,s)-2
        if d<fl: fl=d
print(f"min Δ²V over all tested (s,w) = {mp.nstr(fl,8)}  (floor -2, so slack {mp.nstr(fl+2,6)})")
