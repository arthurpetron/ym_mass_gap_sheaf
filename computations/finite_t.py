import mpmath as mp
mp.mp.dps=40
# Finite-t: real residual uses |D|<=t. even D in {0,+-2,...,+-2*floor(t/2)}, odd D in {+-1,...}.
# In j-vars: even weight r^{j^2}, |2j|<=t -> |j|<=t/2. odd weight r^{(j+1/2)^2}, |2j+1|<=t.
# Compute G_odd-G_even at finite t and compare to 1 (target G_odd-G_even<=1) and to infinite limit.

def G_even_t(w,t):
    r=w*w; Z=mp.mpf(0);M2=mp.mpf(0)
    D=0
    while D<=t:
        we=mp.power(w,D*D/mp.mpf(2)); mult=1 if D==0 else 2
        Z+=mult*we; M2+=mult*D*D*we; D+=2
    return M2/Z
def G_odd_t(w,t):
    Z=mp.mpf(0);M2=mp.mpf(0); D=1
    while D<=t:
        wo=mp.power(w,D*D/mp.mpf(2)); Z+=2*wo; M2+=2*D*D*wo; D+=2
    return M2/Z

def th4(r,N=600): return 1+2*sum((-1)**n*mp.power(r,n*n) for n in range(1,N))

print("Check G_odd-G_even<=1 at FINITE t, and approach to (1/4)th4^4*4 = th4^4 as t->inf")
for w in ['0.2','0.5','0.8','0.95']:
    ww=mp.mpf(w); r=ww*ww
    inf=th4(r)**4  # G_odd-G_even limit = 4*(Var_o-Var_e)=th4^4
    print(f"\nw={w}  infinite-t limit G_odd-G_even = {mp.nstr(inf,20)}")
    for t in [3,5,9,15,25,50,100]:
        d=G_odd_t(ww,t)-G_even_t(ww,t)
        print(f"  t={t:4}: G_odd-G_even={mp.nstr(d,20)}  (<=1? {d<=1})  gap_to_limit={mp.nstr(d-inf,5)}")
