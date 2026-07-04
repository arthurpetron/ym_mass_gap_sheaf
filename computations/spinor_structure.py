import mpmath as mp
from mpmath import mpf, mp as MP
MP.dps=60
def coeffs(N,w):
    w=mpf(w); return [n*(N-n)*w**(n*n+(N-n)**2) for n in range(1,N)]

# (a) unit-circle above w*
print("(a) roots on |z|=1 for w>w* ?")
for w in ['0.85','0.9','0.95','0.99','0.999']:
    for N in [8,16]:
        rs=mp.polyroots(coeffs(N,w)[::-1],maxsteps=6000,extraprec=800)
        dev=max(abs(abs(r)-1) for r in rs)
        print(f"  w={w:>6} N={N}: max||z|-1|={mp.nstr(dev,4)}")

# (b) theta grounding: A=sum_{k odd} k w^{k^2}, B=sum_{k even}. G_even=A^2+B^2 (same parity), G_odd=2AB
def A(w,K=400): w=mpf(w); return sum(k*w**(k*k) for k in range(1,K,2))
def B(w,K=400): w=mpf(w); return sum(k*w**(k*k) for k in range(2,K,2))
def theta4(q,K=400): q=mpf(q); return 1+2*sum((-1)**n*q**(n*n) for n in range(1,K))
print("\n(b) G_odd - G_even = -(A-B)^2 ; compare to theta-derivative")
for w in ['0.3','0.6','0.9']:
    a=A(w); b=B(w); Ge=a*a+b*b; Go=2*a*b
    diff=Go-Ge
    # (A-B) = sum (-1)^{k-1} k w^{k^2} = (1/2) d/d? relate: this is -(1/2) w^{1/4}... just report
    print(f"  w={w}: A-B={mp.nstr(a-b,10)}  G_odd-G_even={mp.nstr(diff,10)}  =-(A-B)^2={mp.nstr(-(a-b)**2,10)}")

# (c) is Z_N log-concave, and does V relate to it? Z_N = sum g(n)g(N-n)
def Z(N,w): return sum(coeffs(N,w))
def Vd(N,w):
    cs=coeffs(N,w); den=sum(cs)
    return sum(cs[i]*(( (N-(i+1))-(i+1))**2) for i in range(len(cs)))/den
print("\n(c) log-concavity of Z_N (Delta^2 log Z <=0) and V vs -Delta^2 log Z:")
for w in ['0.2','0.5','0.8','0.95']:
    print(f"  w={w}:")
    for N in [5,8,12]:
        lz=lambda M: mp.log(Z(M,mpf(w)))
        d2logZ=lz(N+1)-2*lz(N)+lz(N-1)
        print(f"    N={N}: Delta^2 logZ={mp.nstr(d2logZ,8):>14}  V(t={N-2})={mp.nstr(Vd(N,mpf(w)),8)}  ratio V/(-d2logZ)={mp.nstr(Vd(N,mpf(w))/(-d2logZ),6)}")
