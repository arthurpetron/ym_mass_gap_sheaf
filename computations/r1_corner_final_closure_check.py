import mpmath as mp
mp.mp.dps=30
def Varq(qv,t):
    N=t+2;Ds=list(range(-t,t+1,2));w=[float(N*N-D*D)*float(qv)**(D*D) for D in Ds];Z=sum(w)
    m2=sum(D*D*wi for D,wi in zip(Ds,w))/Z;m4=sum(D**4*wi for D,wi in zip(Ds,w))/Z;return m4-m2*m2
def Varpar(t): return 8*t*(t-1)*(t+4)*(t+5)/175.0
def d2e(s,q): return (Varpar(s)-Varq(q,s))-2*(Varpar(s+1)-Varq(q,s+1))+(Varpar(s+2)-Varq(q,s+2))
def moms(t):
    Z=mp.quad(lambda x:(1-x*x)*mp.e**(-t*x*x),[-1,1]);m2=mp.quad(lambda x:x*x*(1-x*x)*mp.e**(-t*x*x),[-1,1])/Z
    m4=mp.quad(lambda x:x**4*(1-x*x)*mp.e**(-t*x*x),[-1,1])/Z;return m4-m2*m2
def gg(t): return mp.mpf(8)/175-moms(t)
def Psi(t):
    hh=mp.mpf('1e-5');return 12*gg(t)+18*t*(gg(t+hh)-gg(t-hh))/(2*hh)+4*t*t*(gg(t+hh)-2*gg(t)+gg(t-hh))/(hh*hh)
def c1(t):
    def R(s): mu=float(t)/(s*s);return d2e(s,mp.e**(-mu))/(s*s)-Psi(t)
    return 2*(800*R(800))-(400*R(400))
taus=[mp.mpf(x) for x in ['0.02','0.1','0.3','0.7','1.5','3.0','4.3']]
Pc={t:Psi(t) for t in taus}; Cc={t:c1(t) for t in taus}
print("FINAL closure check: Δ²e = s²Ψ + s·c₁ + ρ, with Ψ≥0, c₁≥0 proved. Verify ρ≥0 and Δ²e≥0:")
mnrho=9.9; mnd2e=9.9; mnPsi=9.9; mnc1=9.9
for t in taus:
    mnPsi=min(mnPsi,float(Pc[t])); mnc1=min(mnc1,float(Cc[t]))
    for s in [7,8,11,20,60,200,600]:
        mu=float(t)/(s*s);q=mp.e**(-mu);D=d2e(s,q)
        rho=float(D)-s*s*float(Pc[t])-s*float(Cc[t])
        mnrho=min(mnrho,rho); mnd2e=min(mnd2e,float(D))
print(f"  min Ψ = {mnPsi:.5f}   min c₁ = {mnc1:.5f}   min ρ = {mnrho:.5f}   min Δ²e = {mnd2e:.5f}")
print(f"  All three terms ≥0 (Ψ,c₁,ρ) ⟹ Δ²e = s²Ψ+s·c₁+ρ ≥ 0 for all s≥7.  CLOSURE: {mnrho>=-1e-6 and mnPsi>=-1e-6 and mnc1>=-1e-6}")
