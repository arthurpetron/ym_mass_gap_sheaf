import mpmath as mp
mp.mp.dps = 60

def var_e(r):
    # weight r^{n^2}, mean 0, var = sum n^2 r^{n^2}/sum r^{n^2}
    Z=mp.mpf(0); M2=mp.mpf(0)
    N=int(mp.sqrt(200/(-mp.log(r)+1e-30)))+50
    for n in range(-N,N+1):
        w=mp.power(r, n*n); Z+=w; M2+=n*n*w
    return M2/Z

def var_o(r):
    # weight r^{(n+1/2)^2}, mean -1/2, var = <(n+1/2)^2>
    Z=mp.mpf(0); M2=mp.mpf(0)
    N=int(mp.sqrt(200/(-mp.log(r)+1e-30)))+50
    for n in range(-N,N+1):
        x=n+mp.mpf(1)/2
        w=mp.power(r, x*x); Z+=w; M2+=x*x*w
    return M2/Z

print("r, Var_o-Var_e, slack=1/4-(Var_o-Var_e)")
for rexp in [0.01,0.05,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,0.95,0.99,0.999]:
    r=mp.mpf(rexp)
    d=var_o(r)-var_e(r)
    print(f"r={rexp:6}  d={mp.nstr(d,20)}  slack={mp.nstr(mp.mpf(1)/4-d,20)}")
