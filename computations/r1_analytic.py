import sympy as sp
w,s = sp.symbols('w s')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def Vexp(t, order):
    # V(t) = dmomNfull/acNfull as a w-series to given order
    num=dmomNfull(t); den=acNfull(t)
    return sp.series(num/den, w, 0, order).removeO()

# 1) V(t) leading structure, even vs odd, low order
print("=== V(t) series (even t=2m and odd t=2m+1): leading + next ===")
for t in range(2,9):
    ser=sp.series(dmomNfull(t)/acNfull(t), w, 0, 12).removeO()
    print(f" t={t} ({'even' if t%2==0 else 'odd'}): V(t) = {sp.nsimplify(ser)}")

# 2) closed forms: even leading C(t)=8t(t+4)/(t+2)^2 ; odd next-coeff 8(M^2-9)/(M^2-1)
print("\n=== check closed forms ===")
for t in [2,4,6,8]:
    C=sp.Rational(8*t*(t+4),(t+2)**2); ser=sp.series(dmomNfull(t)/acNfull(t),w,0,4).removeO()
    print(f" even t={t}: pred C={C}  vs series w^2 coeff={ser.coeff(w,2)}")
for t in [3,5,7]:
    M=t+2; D4=sp.Rational(8*(M**2-9),(M**2-1)); ser=sp.series(dmomNfull(t)/acNfull(t),w,0,6).removeO()
    print(f" odd  t={t}: pred w^4 coeff={D4}  vs series w^4 coeff={ser.coeff(w,4)}")
