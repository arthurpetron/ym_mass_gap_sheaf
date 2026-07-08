import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def A(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def N(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=A(s),A(s+1),A(s+2); dS,d1,d2=N(s),N(s+1),N(s+2)
    return sp.expand(dS*a1*a2 + d2*aS*a1 + 2*aS*a1*a2 - 2*d1*aS*a2)

# Three-body form: slack_s = sum_{D0,D1,D2} (D0^2+D2^2-2*D1^2+2) c_s(D0)c_{s+1}(D1)c_{s+2}(D2)
def cfac(t,D):  # coeffW-product weight for level t at value D (D=t-2p)
    p=(t-D)//2
    return coeffW(p)*coeffW(t-p)
def slack_threebody(s):
    tot=0
    for D0 in range(-s,s+1,2):
        for D1 in range(-(s+1),s+2,2):
            for D2 in range(-(s+2),s+3,2):
                f=D0**2+D2**2-2*D1**2+2
                tot+=f*cfac(s,D0)*cfac(s+1,D1)*cfac(s+2,D2)
    return sp.expand(tot)

print("=== verify three-body representation matches slack_s ===")
for s in range(0,6):
    diff=sp.simplify(slack(s)-slack_threebody(s))
    print(f" s={s}: slack - threebody = {diff}")
