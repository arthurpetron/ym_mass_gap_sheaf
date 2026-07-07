import mpmath as mp
from sympy import symbols, Rational, simplify, integrate, sqrt, pi, cos, sin, S
from sympy.physics.wigner import wigner_6j, wigner_3j
mp.mp.dps = 45

# SU(2) heat-kernel character coefficients (the library's coeffW):
#   coeffW(w,s) = dim_s * w^{c4(s)},  dim_s = s+1,  c4(s) = s(s+2) = C2 eigenvalue*4-ish
# rep index s = 2j (twice-spin). dim_s = s+1. Casimir-exponent c4(s)=s(s+2).
def dim_s(s): return s+1
def c4(s): return s*(s+2)
def coeffW(w,s): return dim_s(s)*mp.mpf(w)**c4(s)

print("="*70)
print("1. coeffW ratios and the character-expansion convergence parameter")
print("="*70)
# The single-line chain per-step factor is rho = coeffW(w,1) = 2 w^3 (excited/vacuum, dominant).
# Library: rho = 2 w^3 < 1  iff  w < (1/2)^{1/3} = 0.7937...
for w in [0.5, 0.7937, 0.9, 0.99, 0.999, 0.9999]:
    rho = 2*mp.mpf(w)**3
    print(f"  w={w:8}:  rho=coeffW(w,1)=2w^3 = {mp.nstr(rho,10):12}  (<1? {rho<1})")
print("  => as w->1 (a->0, continuum end) the character per-step factor 2w^3 -> 2 > 1:")
print("     the strong-coupling CHARACTER expansion DIVERGES at the continuum limit.")

print()
print("="*70)
print("2. z_n^char (lattice Haar) for small clusters via orthogonality/6j")
print("="*70)
# Single-plaquette connected activity (excited character mass), z_1^char:
#   the deviation of the plaquette from vacuum = sum_{r>=1} coeffW(w,r) integrated appropriately.
# Two-plaquette sharing one link: character orthonormality int chi_a chi_b = delta_ab
#   => z_2^char = sum_{r>=1} coeffW(w,r)^2   (two plaquettes, common excited rep r)
# (matches library wilsonG collapse: sum_r connChain = sum_r coeffW^{n+1})
def z_char_chain(w, nplaq, Rmax=200):
    # chain of nplaq plaquettes, single common excited rep r>=1: sum_r coeffW(w,r)^nplaq
    return mp.fsum([coeffW(w,r)**nplaq for r in range(1,Rmax)])
for w in [0.5,0.7,0.79]:
    print(f"  w={w}:  z2^char=sum coeffW^2={mp.nstr(z_char_chain(w,2),8)}, "
          f"z3^char=sum coeffW^3={mp.nstr(z_char_chain(w,3),8)}")

print()
print("="*70)
print("3. Compare z_n^char vs the KP bound (mu g^2)^n with g^2 = 1-w, mu=6")
print("="*70)
# The field-space KP object requires |z_1| <= g^2 = 1-w and |z_n| <= (mu g^2)^n.
# Is the CHARACTER z_1^char <= g^2 = 1-w?
for w in [0.5,0.7,0.79,0.9,0.99]:
    g2 = 1-mp.mpf(w)
    z1c = mp.fsum([coeffW(w,r) for r in range(1,200)])  # excited char mass
    print(f"  w={w:6}: z1^char(excited mass)={mp.nstr(z1c,8):12} vs g^2=1-w={mp.nstr(g2,8):12}"
          f"  ratio={mp.nstr(z1c/g2,6)}")

print()
print("="*70)
print("4. >=3-body link integral: int chi_a chi_b chi_c dHaar (triangle) and 4-body")
print("="*70)
# int chi_a chi_b chi_c dHaar = mult of trivial in a⊗b⊗c = triangle indicator (twice-spin labels).
def tri3(a,b,c):
    # multiplicity of trivial rep in tensor of three SU(2) reps (twice-spin a,b,c)
    # = 1 if triangle(a,b,c) and a+b+c even, else 0
    return 1 if (abs(a-b)<=c<=a+b and (a+b+c)%2==0) else 0
for (a,b,c) in [(1,1,2),(1,2,3),(2,2,2),(1,1,1),(1,2,2)]:
    print(f"  int chi_{a} chi_{b} chi_{c} = {tri3(a,b,c)}")
# 4-body link (up to 6 plaquettes at a 4D link): mult of trivial in a⊗b⊗c⊗d = sum_x tri3(a,b,x)tri3(c,d,x)
def mult4(a,b,c,d):
    return sum(tri3(a,b,x)*tri3(c,d,x) for x in range(0,a+b+1))
for t in [(1,1,1,1),(2,2,2,2),(1,2,1,2)]:
    print(f"  mult4{t} = {mult4(*t)}  (Wigner 3nj / 6j structure)")

print()
print("="*70)
print("5. The signed 6j is genuinely irrational (sixjCReal content)")
print("="*70)
for (j1,j2,j3,j4,j5,j6) in [(S(1)/2,S(1)/2,0, S(1)/2,S(1)/2,S(1)/2),
                             (S(1)/2,S(1)/2,1, 1,2,S(3)/2)]:
    val = wigner_6j(j1,j2,j5,j4,j3,j6)
    print(f"  {{6j}} for {(j1,j2,j3,j4,j5,j6)} = {val} = {mp.nstr(mp.mpf(str(float(val))),8)}")
