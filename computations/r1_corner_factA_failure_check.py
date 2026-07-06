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
def c2(t):  # lim ρ = lim (d2e - s²Ψ - s c1)
    P=Psi(t);C=c1(t)
    def rho(s): return d2e(s,mp.e**(-float(t)/(s*s)))-s*s*P-s*C
    return 2*rho(800)-rho(400)  # Richardson: ρ=c2+c3/s → eliminate 1/s
# (A) FAILURE: interior-s dip at τ≈3.4
print("(A) Fact A failure — ρ(s,τ=3.4) vs s (interior dip below endpoints?):")
t=mp.mpf('3.4');P=Psi(t);C=c1(t)
vals=[(s,float(d2e(s,mp.e**(-float(t)/(s*s)))-s*s*P-s*C)) for s in [7,10,14,20,30,60,200,800]]
print("   "+", ".join(f"s{s}:{v:.3f}" for s,v in vals))
rho7=vals[0][1]; c2v=float(c2(t)); interior_min=min(v for _,v in vals)
print(f"   ρ(7)={rho7:.3f}  c₂={c2v:.3f}  min_endpoints={min(rho7,c2v):.3f}  actual_interior_min={interior_min:.3f}  ⟹ endpoint-min FALSE: {interior_min < min(rho7,c2v)-0.01}")
# (STILL CLOSES) ρ≥0 globally + tail arithmetic c₂≥0.283 vs 16.49/60
print("\n(closure) global min ρ over s=7..3000, τ∈(0,35/8]  and  tail arithmetic:")
mn=9.9
for i in range(1,88):
    t=mp.mpf(i)/20
    P=Psi(t);C=c1(t)
    for s in [7,9,14,25,60,300,3000]:
        r=float(d2e(s,mp.e**(-float(t)/(s*s)))-s*s*P-s*C); mn=min(mn,r)
c2min=min(float(c2(mp.mpf(i)/20)) for i in range(1,88))
print(f"   global min ρ = {mn:.4f} (want ≥0)   min c₂ = {c2min:.4f}")
print(f"   tail: for s≥60, ρ≥c₂−16.49/s ≥ {c2min:.4f}−{16.49/60:.4f} = {c2min-16.49/60:.4f} (>0 ⟹ tail closes); s=7..59 finite sweep")
