import mpmath as mp
from mpmath import mpf, mp as MP
MP.dps=80
def roots(N,w):
    w=mpf(w)
    cs=[n*(N-n)*w**(n*n+(N-n)**2) for n in range(1,N)]
    return mp.polyroots(cs[::-1], maxsteps=4000, extraprec=600)

# For fixed N=8, sweep w and report: are roots negative-real, or on |z|=1?
N=8
print(f"N={N}: sweep w, check root nature")
for wv in ['0.1','0.3','0.5','0.6','0.7','0.75','0.8','0.82','0.85','0.9','0.95','0.99']:
    rs=roots(N,wv)
    allnegreal = all(abs(mp.im(r))<mpf(10)**-40 and mp.re(r)<0 for r in rs)
    oncircle = max(abs(abs(r)-1) for r in rs)
    negrealres = max(abs(mp.im(r)) for r in rs)
    print(f" w={wv:>5}: allNegReal={allnegreal}  max|Im|={mp.nstr(negrealres,3):>10}  max||z|-1|={mp.nstr(oncircle,3)}")

# find threshold w* for several N (bisection on discriminant sign via max|Im|)
def maximag(N,w):
    return max(abs(mp.im(r)) for r in roots(N,w))
print("\nThreshold w* (real->complex) by bisection:")
for N in [4,6,8,10,14,20,30]:
    lo,hi=mpf('0.5'),mpf('0.999')
    if maximag(N,lo)>mpf(10)**-30: 
        print(f" N={N}: already complex at 0.5"); continue
    for _ in range(60):
        mid=(lo+hi)/2
        if maximag(N,mid)<mpf(10)**-25: lo=mid
        else: hi=mid
    print(f" N={N:2d}: w* = {mp.nstr(lo,8)}")
