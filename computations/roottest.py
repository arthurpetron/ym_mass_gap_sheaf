import mpmath as mp
from mpmath import mpf, mp as MP
import numpy as np
MP.dps=40

# generating poly over n in 1..N-1 : coeff_n = n*(N-n)*w^(n^2+(N-n)^2)
# factor out z^1 -> poly in z of degree N-2 with coeffs a_j = (j+1)(N-1-j)w^{...}, j=0..N-2
def coeffs(N,w):
    w=mpf(w)
    cs=[]
    for n in range(1,N):
        m=N-n
        cs.append(n*m*w**(n*n+m*m))
    return cs  # for powers z^1..z^{N-1}; drop the z^1 factor -> a_j for n=1..N-1

def realrooted(N,w):
    cs=coeffs(N,w)
    # polynomial sum cs[k] z^{k+1}; roots (excluding z=0): use numpy on reversed
    # build coeff array high->low for powers z^{N-1} down to z^1, then factor z
    arr=[float(c) for c in cs]  # a_1..a_{N-1} for z^1..z^{N-1}
    # poly = z*(a_1 + a_2 z + ... ); nonzero part deg N-2
    poly = arr[::-1] + [0.0]  # highest power first: coeff of z^{N-1}...z^1, z^0=0
    # remove trailing zero (factor z): poly of z^{N-1}..z^1 -> divide by z
    p = arr[::-1]  # coeff z^{N-1} down to z^1 ; as poly in z after factoring one z: z^{N-2}..z^0
    roots=np.roots(p)
    maximag=max(abs(r.imag) for r in roots) if len(roots)>0 else 0.0
    maxabs=max(abs(r) for r in roots) if len(roots)>0 else 1.0
    return maximag, roots

for w in ['0.1','0.3','0.5','0.7','0.9']:
    print(f"--- w={w} ---")
    for N in [4,6,8,10,14,20]:
        mi,roots=realrooted(N,w)
        # relative imaginary part
        print(f"  N={N:2d}: max|Im(root)| = {mi:.3e}  (real-rooted if ~0);  #roots={len(roots)}")
