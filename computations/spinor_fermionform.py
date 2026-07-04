import mpmath as mp
from mpmath import mpf, mp as MP
MP.dps=60
def coeffs(N,w):
    w=mpf(w); return [n*(N-n)*w**(n*n+(N-n)**2) for n in range(1,N)]
def Vdirect(N,w):
    cs=coeffs(N,w); den=sum(cs); 
    num=sum(cs[i]*(( (N-(i+1))-(i+1) )**2) for i in range(len(cs)))
    return num/den
def V_from_fermion(N,w):
    cs=coeffs(N,w)
    rs=mp.polyroots(cs[::-1], maxsteps=4000, extraprec=600)  # roots of poly deg N-2
    # p_k = 1/(1+rho_k), rho_k = -root (should be >0 & real)
    var=mpf(0); ok=True
    for r in rs:
        if abs(mp.im(r))>mpf(10)**-30 or mp.re(r)>=0: ok=False
        rho=-mp.re(r); p=1/(1+rho); var+=p*(1-p)
    # V = 4 Var(n) since D=N-2n, and n=1+sum B_k so Var(n)=Var(sum B_k)=var
    return 4*var, ok

print("Verify V(t)=4*sum p_k(1-p_k) in real-rooted regime:")
for w in ['0.1','0.3','0.5','0.7','0.8']:
    print(f" w={w}:")
    for N in [4,6,8,12]:
        vd=Vdirect(N,mpf(w)); vf,ok=V_from_fermion(N,mpf(w))
        print(f"   t={N-2:2d}: Vdirect={mp.nstr(vd,15)}  Vfermion={mp.nstr(vf,15)}  match={abs(vd-vf)<mpf(10)**-25}  realroots={ok}")
