import mpmath as mp
mp.mp.dps = 45
p = mp.mpf(2)
# Closed form: B_mu(u) = ∫_{μ²}^1 ξ^{p-1-u} dξ = (1 - μ^{2(p-u)})/(p-u)
# The renormalon pole at u=p is EXACTLY cancelled by the zero of numerator.
def Bmu_closed(u, mu2):
    return (1 - mu2**(p-u))/(p-u)
def Bmu_series(u, mu2, N=300):
    Lam=-mp.log(mu2); s=mp.mpf(0)
    for n in range(N+1):
        dn=mp.gammainc(n+1,0,p*Lam)/p**(n+1)
        s+=dn*mp.power(u,n)/mp.factorial(n)
    return s
mu2=mp.mpf('0.1')
print("closed form vs series (should match to ~1e-40):")
for uu in ['1.0','1.99','2.5','3.0']:
    uu=mp.mpf(uu)
    print(f"  u={float(uu)}: closed={mp.nstr(Bmu_closed(uu,mu2),12)} series={mp.nstr(Bmu_series(uu,mu2),12)} reldiff={mp.nstr(abs(Bmu_closed(uu,mu2)-Bmu_series(uu,mu2)),3)}")
# value AT the renormalon pole u=p: limit = -ln(μ²) = Λ (finite -> pole removed)
print(f"\nAt renormalon pole u=p=2: B_mu(2)=lim=(−lnμ²)=Λ={mp.nstr(-mp.log(mu2),12)}")
print(f"  closed form at u=2 (via limit eps->0): {mp.nstr(Bmu_closed(2-mp.mpf('1e-20'),mu2),12)}")
print("=> The mass μ CANCELS the positive-axis Borel pole: numerator (1-μ^{2(p-u)}) ")
print("   has a simple zero at u=p that kills the 1/(p-u) pole. B_mu ENTIRE. QED.")
print("\nNON-UNIFORMITY as μ²->0 (a->0): for u>p, μ^{2(p-u)}=μ^{neg}->∞, B_mu blows up:")
for m2 in ['0.1','0.01','1e-4','1e-8']:
    m2=mp.mpf(m2)
    print(f"  μ²={mp.nstr(m2,2)}: B_mu(3)={mp.nstr(Bmu_closed(mp.mpf(3),m2),6)}  (pole region reforms)")
