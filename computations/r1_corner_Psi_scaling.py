import mpmath as mp
mp.mp.dps=30
# CORRECT continuum object: g(τ)=Var(x²)_0 − Var(x²)_τ, density ∝(1−x²)e^{−τx²} on [−1,1]
def moms(tau):
    Z=mp.quad(lambda x:(1-x*x)*mp.e**(-tau*x*x),[-1,1])
    m2=mp.quad(lambda x:x*x*(1-x*x)*mp.e**(-tau*x*x),[-1,1])/Z
    m4=mp.quad(lambda x:x**4*(1-x*x)*mp.e**(-tau*x*x),[-1,1])/Z
    return m4-m2*m2   # Var(x²)
V0=mp.mpf(8)/175
def g(tau): return V0-moms(tau)
def Psi(tau):
    h=mp.mpf('1e-5')
    gp=(g(tau+h)-g(tau-h))/(2*h); gpp=(g(tau+h)-2*g(tau)+g(tau-h))/(h*h)
    return 12*g(tau)+18*tau*gp+4*tau*tau*gpp
print("CORRECT g=Var(x²) deficit.  Ψ(τ)=12g+18τg'+4τ²g''  (want ≥0):")
mn=mp.inf
for i in list(range(1,80,3)):
    tau=mp.mpf(i)/8; p=Psi(tau)
    if p<mn: mn=p; ma=float(tau)
print(f"  MIN Ψ over τ∈(0,10] = {float(mn):.6f} at τ={ma:.3f}")
# scaling collapse: Δ²e(s) ~ s^? · G(τ); check Δ²e vs s²Ψ(τ) with τ=μs²  (discrete >= continuum ?)
def Varq(qv,t):
    N=t+2;Ds=list(range(-t,t+1,2));w=[float(N*N-D*D)*float(qv)**(D*D) for D in Ds];Z=sum(w)
    m2=sum(D*D*wi for D,wi in zip(Ds,w))/Z;m4=sum(D**4*wi for D,wi in zip(Ds,w))/Z;return m4-m2*m2
def Varpar(t): return 8*t*(t-1)*(t+4)*(t+5)/175.0
print("\nScaling collapse  Δ²e(s)/s²  vs  Ψ(τ),  τ=μs²  (want discrete ≥ Ψ, gap ≥0):")
for tau0 in [1.0,2.0,4.0]:
    print(f"  τ={tau0}: Ψ={float(Psi(mp.mpf(tau0))):.5f}")
    for s in [20,40,80,160]:
        mu=tau0/(s*s); q=mp.e**(-mu)
        d2e=(Varpar(s)-Varq(q,s))-2*(Varpar(s+1)-Varq(q,s+1))+(Varpar(s+2)-Varq(q,s+2))
        print(f"     s={s}: Δ²e/s²={float(d2e)/(s*s):.5f}  gap={float(d2e)/(s*s)-float(Psi(mp.mpf(tau0))):.5f}")
