import mpmath as mp, sympy as sp
mp.mp.dps = 50

# 1) crossover w* where rho=2w^3 = 1
wstar = mp.mpf(2)**(mp.mpf(-1)/3)
print("w* = 2^(-1/3) =", wstar, " ; 2*w*^3 =", 2*wstar**3)

# 2) g^2 bracket: (1-w) <= -log w <= (1-w)/w
for w in [mp.mpf('0.9'), mp.mpf('0.99'), mp.mpf('0.999')]:
    lo, mid, hi = 1-w, -mp.log(w), (1-w)/w
    print(f"w={w}  1-w={lo}  g2=-logw={mid}  (1-w)/w={hi}  bracket_ok={lo<=mid<=hi}")

# 3) field vs char activity inversion at w=9/10
w = mp.mpf(9)/10
print("field a=1-w =", 1-w, " char a=2w^3 =", 2*w**3)

# 4) Sum_k 6(1-w_k)^2 with w_k=1-1/(k+1) => 6*zeta(2)=pi^2
S = sum(6*(mp.mpf(1)/(k+1))**2 for k in range(200000))
print("Sum 6(1-w_k)^2 (200k terms) =", S, " target 6*zeta(2)=pi^2 =", mp.pi**2)

# 5) The dimensional-transmutation scalar picture: per-step defect -> 0 but product floor > 0
# model: delta_k <= 6*(1-w_k)^2 = 6/(k+1)^2 ; product prod(1-delta_k)
# check prod_{k<N}(1 - 6/(k+B)^2) converges to a POSITIVE limit (offset B so terms<1)
B = 4  # offset so 6/(k+B)^2 < 1
prod = mp.mpf(1)
for k in range(500000):
    prod *= (1 - mp.mpf(6)/(k+B)**2)
print(f"prod_(1 - 6/(k+{B})^2) over 500k =", prod, " (POSITIVE floor => uniform physical contraction)")

# exact sympy: crossover 1-w = 2w^3 real root (the OTHER crossover mentioned in doc, 0.58975)
w = sp.symbols('w', positive=True)
roots = sp.nroots(2*w**3 + w - 1)
print("real root of 2w^3+w-1 (field=char crossover):", [r for r in roots if r.is_real])
