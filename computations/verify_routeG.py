import mpmath as mp
from sympy import Rational, nsimplify, symbols, simplify
mp.mp.dps = 50

print("=== 1. Crossover complementarity: no uncovered w in [0,1] ===")
# block-spin defect 6*(1-w)^2 < 1/2  <=> w > 1 - sqrt(1/12)
wb = 1 - mp.sqrt(mp.mpf(1)/12)
# character w^3 < 1/2 <=> w < (1/2)^(1/3)
wc = (mp.mpf(1)/2)**(mp.mpf(1)/3)
print(f"  block-spin 6(1-w)^2<1/2  holds for w > {wb}")
print(f"  character  w^3<1/2       holds for w < {wc}")
print(f"  union covers [0,1]? block-lo {float(wb):.4f} < char-hi {float(wc):.4f} => overlap, NO GAP: {wb < wc}")

print("\n=== 2. inverse-square partial sum <= 2 (recipSq_tailSum_le_two) ===")
S = mp.nsum(lambda k: mp.mpf(1)/(k+1)**2, [0, mp.inf])
print(f"  sum_{{k>=0}} 1/(k+1)^2 = {S}  (= pi^2/6 = {mp.pi**2/6}); <= 2 ? {S <= 2}")

print("\n=== 3. geometric partial sum <= 1/(1-r) ===")
for r in [mp.mpf('0.3'), mp.mpf('0.5'), mp.mpf('0.9')]:
    g = mp.nsum(lambda k: r**k, [0, mp.inf])
    print(f"  r={float(r)}: sum r^k = {g} = 1/(1-r) = {1/(1-r)}  eq? {abs(g-1/(1-r))<mp.mpf(10)**-40}")

print("\n=== 4. union majorant: if d<=A or d<=B (A,B>=0) then d<=A+B ===")
print("  elementary (A,B>=0): d<=A => d<=A+B ; d<=B => d<=A+B. TRUE by monotonicity.")

print("\n=== 5. middle additive budget Sigma 6(1-w)^2 over w=1/2,2/3,3/4 (>1) ===")
mid = Rational(6)*((Rational(1,2))**2+(Rational(1,3))**2+(Rational(1,4))**2)
print(f"  6*(1/4+1/9+1/16) = {mid} = {float(mid):.4f}  > 1 ? {mid>1}  (=> Weierstrass fails, need exp floor)")

print("\n=== 6. crossover budget R = 2*Ddelta + K/(1-r) is finite; exp floor e^{-2R}>0 all R ===")
for (Dd,K,r) in [(mp.mpf('0.5'),mp.mpf('0.1'),mp.mpf('0.5')), (mp.mpf('2.0'),mp.mpf('1.0'),mp.mpf('0.9'))]:
    R = 2*Dd + K/(1-r)
    print(f"  Dd={float(Dd)},K={float(K)},r={float(r)}: R={float(R):.4f}, e^(-2R)={mp.e**(-2*R)} >0")

print("\n=== 7. delta<=1/2 requires TAIL: strong bound 6(1-w)^2 at small w exceeds 1/2 ===")
for w in [mp.mpf('1')/6, mp.mpf('0.5'), mp.mpf('0.9')]:
    v = 6*(1-w)**2
    print(f"  w={float(w):.3f}: 6(1-w)^2 = {float(v):.4f}  <=1/2? {v<=mp.mpf(1)/2}  (head not <=1/2 => tail-shift needed)")
