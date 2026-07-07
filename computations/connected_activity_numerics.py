"""
DECISIVE CHECK: does the CONNECTED (Ursell/cumulant) reorganization tame the
factorial growth of the perturbative series, or does the factorial SURVIVE
connectedness (= the renormalon)?

Model: zero-dimensional phi^4 (the exact analog where every diagram is computable).
  Z(g) = (1/sqrt(2pi)) * int e^{-x^2/2 - g x^4} dx   (partition function)
  W(g) = log Z(g)                                     (CONNECTED generating fn / free energy)
  G2(g) = <x^2>(g)                                    (full 2-point)
  G2c(g) = <x^2>(g) - <x>(g)^2 = <x^2>(g)             (connected 2-point; <x>=0)

We compare the LARGE-ORDER growth of:
  (a) FULL   series a_k   of Z(g)
  (b) CONNECTED series c_k of W(g) = log Z  (disconnected diagrams removed)
  (c) CONNECTED 2-point series of G2c(g) = z_1 analog
If (b),(c) still grow factorially -> connectedness does NOT tame it -> renormalon survives.
"""
import sympy as sp

g = sp.symbols('g')
x = sp.symbols('x')
N = 16  # order

# Exact perturbative coefficients of Z(g) via Gaussian moments:
# Z(g) = sum_k (-g)^k/k! * <x^{4k}>_0 ,  <x^{2m}>_0 = (2m-1)!!
def double_factorial(m):
    # (2m-1)!! = product of odd numbers up to 2m-1 ; (−1)!! = 1
    r = sp.Integer(1)
    j = 2*m - 1
    while j > 0:
        r *= j
        j -= 2
    return r

a = []  # Z coefficients a_k
for k in range(N+1):
    coeff = sp.Rational((-1)**k, sp.factorial(k)) * double_factorial(2*k)  # <x^{4k}> = (4k-1)!! = double_factorial(2k)
    a.append(sp.nsimplify(coeff))
Zser = sum(a[k]*g**k for k in range(N+1))

# Connected free energy W = log Z as a power series
Wser = sp.series(sp.log(Zser + sp.O(g**(N+1))), g, 0, N+1).removeO()
c = [sp.nsimplify(Wser.coeff(g, k)) for k in range(N+1)]

# Connected 2-point: <x^2>(g). Use Z2(g) = <x^2 e^{-g x^4}>_0 / <e^{-g x^4}>_0
# numerator series: sum_k (-g)^k/k! <x^{4k+2}>_0
num = []
for k in range(N+1):
    num.append(sp.Rational((-1)**k, sp.factorial(k)) * double_factorial(2*k+1))  # <x^{4k+2}>=(4k+1)!!=double_factorial(2k+1)
Numser = sum(num[k]*g**k for k in range(N+1))
G2 = sp.series(Numser / (Zser + sp.O(g**(N+1))), g, 0, N+1).removeO()
d = [sp.nsimplify(G2.coeff(g, k)) for k in range(N+1)]  # <x^2>_c coefficients (=z_1 analog)

def ratios(seq, label):
    print(f"\n=== {label} ===")
    print("k :   coeff (exact)                        |c_{k+1}/c_k|")
    for k in range(1, N):
        ck = seq[k]; ck1 = seq[k+1]
        if ck == 0:
            r = "inf(0 denom)"
        else:
            r = sp.Abs(ck1/ck)
            r = sp.N(r, 8)
        print(f"{k:2d}: {str(ck):>34s}   {r}")

ratios(a, "FULL Z(g) coefficients a_k")
ratios(c, "CONNECTED W=log Z coefficients c_k (disconnected removed)")
ratios(d, "CONNECTED 2-point <x^2>_c coefficients (z_1 analog)")

# Growth-law fit: for factorial a_k ~ C * (-A)^k * k!  =>  |a_{k+1}/a_k| ~ A*(k+1) grows LINEARLY in k.
# Geometric would be BOUNDED. Print the ratio/(k) to see if it tends to a constant (=> factorial).
print("\n=== ratio / k  (factorial => tends to constant A; geometric => ->0) ===")
for k in range(4, N):
    ra = sp.N(sp.Abs(a[k+1]/a[k])/k, 6) if a[k]!=0 else None
    rc = sp.N(sp.Abs(c[k+1]/c[k])/k, 6) if c[k]!=0 else None
    rd = sp.N(sp.Abs(d[k+1]/d[k])/k, 6) if d[k]!=0 else None
    print(f"k={k:2d}:  full/k={ra}   conn(logZ)/k={rc}   conn2pt/k={rd}")
