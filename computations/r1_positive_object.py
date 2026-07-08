import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def V(t): return sp.cancel(dmomNfull(t)/acNfull(t))

print("=== numerator of (Delta^2 V(s) + 2), factored -- the TRUE positive object ===")
for s in range(0,6):
    expr=sp.cancel(V(s)-2*V(s+1)+V(s+2)+2)
    num,den=sp.fraction(sp.together(expr))
    num=sp.expand(num); den=sp.expand(den)
    fn=sp.factor(num)
    # check num>=0 on (0,1): roots
    Pn=sp.Poly(num,w); k=min(m for (m,) in Pn.monoms())
    Bn=sp.Poly(sp.expand(num/w**k),w)
    nr=int(Bn.count_roots(0,1))
    print(f"\n s={s}: (Delta^2V+2) numerator factored:")
    print(f"    {fn}")
    print(f"    [after w^{k}: deg {Bn.degree()}, roots in (0,1) = {nr}, B(0)={int(Bn.eval(0))}, sign(den@0.5)={sp.sign(den.subs(w,sp.Rational(1,2)))}]")

print("\n=== theta-moment recursion check: theta_{t+2}=theta_t+2 w^{(t+2)^2/2}, etc. ===")
def thmom(t,j):
    return sum((t-2*p)**(2*j)*w**sp.Rational((t-2*p)**2,2) for p in range(t+1))
for t in range(0,5):
    ok0=sp.simplify(thmom(t+2,0)-(thmom(t,0)+2*w**sp.Rational((t+2)**2,2)))==0
    ok1=sp.simplify(thmom(t+2,1)-(thmom(t,1)+2*(t+2)**2*w**sp.Rational((t+2)**2,2)))==0
    print(f" t={t}: theta_(t+2)=theta_t+2w^m2/2 : {ok0};  xi recursion: {ok1}")
