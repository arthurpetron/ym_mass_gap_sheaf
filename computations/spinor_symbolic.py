import sympy as sp
w=sp.symbols('w', positive=True)
def Vexpr(t):
    N=t+2
    num=sp.Integer(0); den=sp.Integer(0)
    for n in range(1,N):
        m=N-n
        wt=n*m*w**(n*n+m*m)
        den+=wt; num+=(m-n)**2*wt
    return sp.simplify(num/den)
Vs={t:Vexpr(t) for t in range(0,7)}
for t in range(0,7):
    print(f"V({t}) =", Vs[t])
# Delta^2(V+t^2) for t=0..4
print("\nDelta^2(V+t^2):")
for t in range(0,5):
    f=lambda tt: Vs[tt]+sp.Integer(tt)**2
    d2=sp.simplify(f(t+2)-2*f(t+1)+f(t))
    print(f" t={t}:", d2)
    # check >=0 as w in (0,1): numerator sign
    num,den=sp.fraction(sp.together(d2))
    print("     numerator:", sp.expand(num))
