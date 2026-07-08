import mpmath as mp
mp.mp.dps = 50

def var_e(r):
    Z=mp.mpf(0); M2=mp.mpf(0)
    N=int(mp.sqrt(300/(-mp.log(r)+1e-30)))+60
    for n in range(-N,N+1):
        w=mp.power(r, n*n); Z+=w; M2+=n*n*w
    return M2/Z
def var_o(r):
    Z=mp.mpf(0); M2=mp.mpf(0)
    N=int(mp.sqrt(300/(-mp.log(r)+1e-30)))+60
    for n in range(-N,N+1):
        x=n+mp.mpf(1)/2; w=mp.power(r,x*x); Z+=w; M2+=x*x*w
    return M2/Z
def theta4(r):
    s=mp.mpf(0)
    N=int(mp.sqrt(300/(-mp.log(r)+1e-30)))+60
    for n in range(-N,N+1):
        s+=(-1)**n*mp.power(r,n*n)
    return s

print("r     Var_o-Var_e        (1/4)theta4^4      difference")
for rexp in [0.01,0.05,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,0.99,1e-4,1e-8]:
    r=mp.mpf(rexp)
    d=var_o(r)-var_e(r)
    pred=theta4(r)**4/4
    print(f"{rexp:8} {mp.nstr(d,18):22} {mp.nstr(pred,18):22} {mp.nstr(d-pred,6)}")
