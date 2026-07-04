import mpmath as mp
from mpmath import mpf, mp as MP
MP.dps=80

def coeffs(N,w):
    w=mpf(w)
    return [n*(N-n)*w**(n*n+(N-n)**2) for n in range(1,N)]  # z^1..z^{N-1}

def maximag(N,w):
    cs=coeffs(N,w)          # a_1..a_{N-1}
    p=cs[::-1]              # after factoring z: coeff z^{N-2}..z^0
    roots=mp.polyroots(p, maxsteps=2000, extraprec=400)
    mi=max(abs(mp.im(r)) for r in roots)
    mr=max(abs(r) for r in roots)
    return mi, mr, roots

for w in ['0.5','0.7','0.8','0.9','0.95','0.99']:
    print(f"--- w={w} ---")
    for N in [6,10,14,20]:
        mi,mr,roots=maximag(N,w)
        print(f"  N={N:2d}: max|Im|={mp.nstr(mi,4):>12}  max|root|={mp.nstr(mr,4)}  -> {'REAL' if mi<mr*mp.mpf(10)**-30 else 'COMPLEX'}")
