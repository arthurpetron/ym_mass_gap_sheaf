import sympy as sp
w = sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))

print("=== exact V(t) = dmomNfull/acNfull, cancelled + factored ===")
for t in range(1,7):
    V=sp.cancel(dmomNfull(t)/acNfull(t))
    num,den=sp.fraction(V)
    print(f"\n t={t} ({'even' if t%2==0 else 'odd'}):")
    print(f"   num = {sp.factor(num)}")
    print(f"   den = {sp.factor(den)}")

print("\n=== the moment form: den_t = M^2*theta_t - xi_t, num_t = M^2*xi_t - zeta_t (M=t+2) ===")
print("   theta_t=sum_{D~t,|D|<=t} w^(D^2/2), xi=sum D^2 w^, zeta=sum D^4 w^   (D=t-2p)")
for t in range(1,7):
    M=t+2
    Ds=[t-2*p for p in range(t+1)]
    th=sum(w**sp.Rational(D*D,2) for D in Ds)
    xi=sum(D**2*w**sp.Rational(D*D,2) for D in Ds)
    ze=sum(D**4*w**sp.Rational(D*D,2) for D in Ds)
    den=sp.expand(M**2*th-xi); num=sp.expand(M**2*xi-ze)
    Vm=sp.cancel(num/den)
    Vd=sp.cancel(dmomNfull(t)/acNfull(t))
    print(f" t={t}: moment-form V matches direct: {sp.simplify(Vm-Vd)==0}")
