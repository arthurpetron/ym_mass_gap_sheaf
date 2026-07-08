import mpmath as mp
from mpmath import mpf, mp as MP
MP.dps=50
def coeffs(N,w):
    w=mpf(w); return [n*(N-n)*w**(n*n+(N-n)**2) for n in range(1,N)]
def maximag(N,w):
    rs=mp.polyroots(coeffs(N,w)[::-1],maxsteps=3000,extraprec=400)
    return max(abs(mp.im(r)) for r in rs)
for N in [4,10,40,80,160]:
    lo,hi=mpf('0.5'),mpf('0.9')
    for _ in range(70):
        mid=(lo+hi)/2
        if maximag(N,mid)<mpf(10)**-20: lo=mid
        else: hi=mid
    print(f"N={N:4d}: w*={mp.nstr(lo,10)}  w*^2={mp.nstr(lo*lo,8)}  w*^4={mp.nstr(lo**4,8)}")
