import mpmath as mp
mp.mp.dps=40
def coeffW(w,p): return (p+1)*w**(p*(p+2))
def V(w,t):
    num=mp.fsum((t-2*p)**2*coeffW(w,p)*coeffW(w,t-p) for p in range(t+1))
    den=mp.fsum(coeffW(w,p)*coeffW(w,t-p) for p in range(t+1))
    return num/den
def theta_var(w, parity, K=400):
    # full even/odd lattice variance G = <D^2> under w^{D^2/2}, D≡parity
    if parity==0: Ds=[2*k for k in range(-K,K+1)]
    else:         Ds=[2*k+1 for k in range(-K,K+1)]
    wts=[w**(mp.mpf(D*D)/2) for D in Ds]
    th=mp.fsum(wts); xi=mp.fsum(D*D*wt for D,wt in zip(Ds,wts))
    return xi/th

print("=== V(t) -> G_parity(w)?  and  Delta^2 V(large even s) -> 2(G_even - G_odd)? ===")
for w in [mp.mpf('0.05'), mp.mpf('0.2'), mp.mpf('0.5'), mp.mpf('0.8')]:
    Ge=theta_var(w,0); Go=theta_var(w,1)
    # large even s
    s=40
    d2=V(w,s)-2*V(w,s+1)+V(w,s+2)
    print(f" w={float(w):.2f}: G_even={float(Ge):.6f} G_odd={float(Go):.6f}  "
          f"2(Ge-Go)={float(2*(Ge-Go)):+.6f}   Delta^2V(s=40)={float(d2):+.6f}   "
          f"V(40 even)={float(V(w,40)):.5f}~Ge? V(41 odd)={float(V(w,41)):.5f}~Go?")

print("\n=== the -2 floor as the parity gap:  G_odd - G_even  (should be in [0,1], ->1 as w->0, ->0 as w->1) ===")
for w in [mp.mpf(x) for x in ['0.01','0.05','0.1','0.2','0.3','0.5','0.7','0.9','0.99']]:
    Ge=theta_var(w,0); Go=theta_var(w,1)
    print(f" w={float(w):.2f}:  G_odd-G_even = {float(Go-Ge):.6f}   (=> asymptotic Delta^2V floor = {float(-2*(Go-Ge)):+.5f})")
