import mpmath as mp
from sympy import Rational, nsimplify, Integer, symbols, solve, root, S, simplify, summation, oo
mp.mp.dps = 50

print("=== Simon-Lieb single-step correlation rho = coeffW(w,1) = 2 w^3 ===")
def rho(w): return 2*w**3

# crossover: rho = 1
wc = mp.root(mp.mpf(1)/2, 3)   # (1/2)^(1/3)
print("crossover w* where 2w^3=1 :", wc, "  check 2*w*^3 =", rho(wc))
print("2^{-1/3} =", mp.power(2,-mp.mpf(1)/3))
print("task claim w<0.79 :", wc, "-> ~0.7937 OK")

print()
print("=== rho at the anchors ===")
print("rho(1/2)  =", rho(mp.mpf(1)/2), " exact", Rational(2,1)*Rational(1,2)**3, "  (<1)")
print("rho(1)    =", rho(mp.mpf(1)),   " exact", Integer(2), "  (>1  => criterion FAILS at continuum)")

print()
print("=== AF trajectory w_k = 1 - 1/(k+1) -> 1, so rho_k -> 2 > 1 ===")
for k in [0,1,2,5,10,50,200]:
    w = 1 - mp.mpf(1)/(k+1)
    print(f"k={k:4d}  w_k={mp.nstr(w,12):14s}  rho_k=2w^3={mp.nstr(rho(w),12):14s}  <1? {rho(w)<1}")

print()
print("=== Simon-Lieb single-step contraction: connSum(n+1) <= rho*connSum(n) ===")
# connChain w r n = coeffW(w,r)^{n+1}, coeffW(w,r)=dim(r) w^{C4(r)}, dim(r)=r+1, C4(r)=r(r+2)
def coeffW(w,r): return (r+1)*w**(r*(r+2))
def connSum(w,M,n): return sum(coeffW(w,r)**(n+1) for r in range(1,M+1))
w = mp.mpf(1)/2; M=8
for n in range(0,6):
    lhs = connSum(w,M,n+1); rhs = rho(w)*connSum(w,M,n)
    print(f"n={n}: connSum(n+1)={mp.nstr(lhs,10):14s} <= rho*connSum(n)={mp.nstr(rhs,10):14s}  {lhs<=rhs+mp.mpf(10)**-40}")

print()
print("=== excited coeff bounded by head at strong coupling w<=1/2: coeffW(w,r)<=coeffW(w,1)=rho ===")
w=mp.mpf(1)/2
for r in range(1,7):
    print(f"r={r}: coeffW={mp.nstr(coeffW(w,r),10):14s} <= rho={mp.nstr(rho(w),10)}  {coeffW(w,r)<=rho(w)}")

print()
print("=== BUT at w=1 the head itself is 2>1, and coeffW(1,r)=r+1 grows: character expansion diverges ===")
w=mp.mpf(1)
for r in range(1,7):
    print(f"r={r}: coeffW(1,r)=r+1 =", coeffW(w,r))
print("Sum diverges; character/strong-coupling expansion radius = w* = 2^{-1/3}.")
