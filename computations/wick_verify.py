import mpmath as mp
from sympy import factorial2, Integer, Rational, sqrt, pi, integrate, symbols, exp, oo, simplify
mp.mp.dps = 50

# 1. Isserlis double factorial (2n-1)!! = number of pairings of 2n points
print("=== numPairings n = (2n-1)!! (sympy exact) ===")
def numPairings(n):
    return 1 if n==0 else (2*n-1)*numPairings(n-1)
for n in range(6):
    df = factorial2(2*n-1) if n>0 else Integer(1)
    print(f" n={n}: recursion={numPairings(n)}  (2n-1)!!={df}  match={numPairings(n)==df}")

# 2. Gaussian moment <x^{2n}> = (2n-1)!! s^{2n} via mpmath integration (s=1, unit variance)
print("\n=== <x^{2n}>_Gauss (mpmath dps50) vs (2n-1)!! ===")
s = mp.mpf(1)
norm = mp.sqrt(2*mp.pi)*s
for n in range(5):
    mom = mp.quad(lambda x: x**(2*n)*mp.e**(-x**2/(2*s**2)), [-mp.inf,0,mp.inf])/norm
    exact = numPairings(n)*s**(2*n)
    print(f" n={n}: numeric={mp.nstr(mom,20)}  exact={exact}  reldiff={mp.nstr(abs(mom-exact)/(exact if exact!=0 else 1),5)}")

# 3. wick4 diagonal = 3 pairings each V^2 => 3V^2 ; V=1 => 3
print("\n=== wick4 diagonal (C=1): C_ij C_kl + C_ik C_jl + C_il C_jk = 3 ===")
print("  = 1+1+1 =", 3, " matches gaussMoment 1 2 = numPairings(2)=", numPairings(2))

# 4. odd moments vanish
print("\n=== odd moments <x^{2n+1}> = 0 (symmetry) ===")
for n in range(3):
    mom = mp.quad(lambda x: x**(2*n+1)*mp.e**(-x**2/2), [-mp.inf,0,mp.inf])/norm
    print(f" 2n+1={2*n+1}: numeric={mp.nstr(mom,5)} (=0)")

# 5. leg-count recursion wickMoment: m+2 -> (m+1)*V*wickMoment(m), check even gives double factorial
print("\n=== leg-count recursion wickMoment(m): 0->1,1->0,(m+2)->(m+1)*V*wm(m) ===")
def wm(m, V=Integer(1)):
    if m==0: return Integer(1)
    if m==1: return Integer(0)
    return (m-1)*V*wm(m-2,V)
for m in range(9):
    print(f" m={m}: wm={wm(m)}  expected(even=(m-1)!!,odd=0)={factorial2(m-1) if (m%2==0 and m>0) else (1 if m==0 else 0)}")

# 6. KP geometric bound given z1<=g2: Sum (mu g2)^n <= 1/(1-mu g2)
print("\n=== KP resummation given finite z1: geometric 1/(1-mu*g2) ===")
mu=mp.mpf('3'); g2=mp.mpf('0.1')  # mu*g2=0.3<1
partial=sum((mu*g2)**n for n in range(60))
print(f"  mu*g2={mp.nstr(mu*g2,5)}  Sum_60={mp.nstr(partial,20)}  1/(1-mu g2)={mp.nstr(1/(1-mu*g2),20)}")
