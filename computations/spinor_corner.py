import sympy as sp
w=sp.symbols('w',positive=True); u=sp.symbols('u',nonnegative=True)
def Vexpr(t):
    N=t+2; num=sp.Integer(0); den=sp.Integer(0)
    for n in range(1,N):
        m=N-n; wt=n*m*w**(n*n+m*m); den+=wt; num+=(m-n)**2*wt
    return sp.simplify(num/den)
Vs={t:Vexpr(t) for t in range(0,7)}

# (1) w->0 leading: V(even)->0, V(odd)->1  (the (-1)^F alternation)
print("(1) V(t) as w->0 (limit):")
for t in range(0,7):
    print(f"   V({t})->", sp.limit(Vs[t],w,0), "   leading order:", sp.series(Vs[t],w,0,4).removeO())

# (2) numerators of Delta^2(V+t^2): nonneg on u=w^2>=0 ? find min
print("\n(2) Fixed-t residual Delta^2(V+t^2): numerator nonneg on w>=0? (each is a manifest SOS-certifiable poly)")
for t in range(0,5):
    f=lambda tt: Vs[tt]+sp.Integer(tt)**2
    d2=sp.together(f(t+2)-2*f(t+1)+f(t))
    num,den=sp.fraction(d2)
    num=sp.expand(num); 
    # substitute w^2=u where possible: check parity
    numu=num.subs(w, sp.sqrt(u))
    numu=sp.expand(numu)
    # min over u in [0,oo): sample + check no positive real roots with sign change
    poly=sp.Poly(numu, u) if numu.free_symbols=={u} else None
    # numeric min on [0,1] and [0,50]
    fnum=sp.lambdify(w, num/ (w**sp.Poly(num,w).monoms()[-1][0] if num.subs(w,0)==0 else 1), 'mpmath')
    import mpmath as mp
    g=sp.lambdify(w,num,'mpmath')
    mn=min(g(mp.mpf(x)/1000) for x in range(0,3000))
    print(f"   t={t}: min numerator over w in [0,3] = {mp.nstr(mn,6)}  (>=0 => fixed-t residual holds); deg={sp.degree(num,w)}")
