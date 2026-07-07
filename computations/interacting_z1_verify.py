import sympy as sp
from mpmath import mp, mpf, nsum, inf
mp.dps = 45

w = sp.symbols('w')
# 1) exact factorization  1 - w - 4 w^3 = (1-2w)(2w^2 + w + 1)
lhs = 1 - w - 4*w**3
fac = sp.factor(lhs)
print("factor(1 - w - 4w^3) =", fac)
print("expand check:", sp.expand((1-2*w)*(2*w**2+w+1)) == sp.expand(lhs))
# 2w^2+w+1 discriminant
print("disc(2w^2+w+1) =", sp.discriminant(2*w**2+w+1, w), " (neg => always >0)")

# 2) 4w^3 <= 1-w on [0,1/2]; equality at 1/2
for ww in [mpf(0), mpf('0.1'), mpf('0.25'), mpf('0.4'), mpf('0.49'), mpf('0.5')]:
    print(f"w={float(ww):.3f}  4w^3={float(4*ww**3):.5f}  1-w={float(1-ww):.5f}  ok={4*ww**3 <= 1-ww}")

# 3) exact interacting non-Gaussian single-plaquette activity  A(w)=sum_{s>=1}(s+1) w^{s(s+2)}
def A(w):
    return nsum(lambda s: (s+1)*mpf(w)**(s*(s+2)), [1, inf])
for ww in ['0.1','0.3','0.5']:
    a = A(ww); ub = 4*mpf(ww)**3; fa = 1-mpf(ww)
    print(f"w={ww}: A(w)={mp.nstr(a,20)}  <=4w^3={mp.nstr(ub,12)} ? {a<=ub}   <=1-w={mp.nstr(fa,6)} ? {a<=fa}")

# 4) weak coupling clearing FAILS at w=9/10
ww=mpf('0.9')
print(f"w=0.9: 4w^3={float(4*ww**3):.4f}  1-w={float(1-ww):.4f}  4w^3<=1-w? {4*ww**3<=1-ww}")
print(f"w=0.9: A(w)={mp.nstr(A('0.9'),12)}  1-w=0.1  A<=1-w? {A('0.9')<=1-ww}")
