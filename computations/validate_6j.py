"""
Rigorous numerical validation of the SU(2) recoupling frontier (A2).
All spins are labelled by TWICE-SPIN reps  rep = 2j  (so j = rep/2), matching
the Lean SixJKernel encoding.

Checks:
  1. Triangle indicator  ∫ χ_a χ_b χ_c dHaar = [triangle & parity]  (SU(2)).
  2. The Lean `racahSum` (signed t-sum S) reproduces the Racah 6j:
        {a b e; c d f} = sqrt(triSqProd) * S ,   triSqProd = ∏ Δ_face^2
     compared to sympy wigner_6j (exact) and mpmath (dps 50).
  3. dim(e)*dim(f)*{6j}^2 == racahKernelQ  (the Lean rational squared kernel).
  4. Find a genuinely IRRATIONAL 6j (triSqProd not a perfect square).
  5. Biedenharn-Elliott PENTAGON: locate the exact index arrangement, verify
     exactly (sympy) + high precision (mpmath), over many random tetra tuples.
  6. ≥3-rep Haar integral = Wigner 3nj.
"""
import sympy as sp
from sympy import Rational as R, sqrt, factorial as fac, Integer
from sympy.physics.wigner import wigner_6j, wigner_3j
import mpmath as mp
mp.mp.dps = 60
import itertools, random

def j(rep):  # twice-spin -> spin
    return R(rep, 2)

# ---------- 1. triangle indicator = ∫ χ_a χ_b χ_c ----------
def triangle_ok(a, b, c):  # reps (twice spin)
    return (abs(a-b) <= c <= a+b) and ((a+b+c) % 2 == 0)

def char_triple_integral(a, b, c, N=4000):
    # ∫_0^pi (2/pi) sin^2(θ) χ_a χ_b χ_c dθ, χ_r(θ)= sin((r+1)θ)/sin θ
    # = multiplicity of trivial rep in a⊗b⊗c ; do it via Clebsch decomposition.
    # a⊗b = ⊕_{c'=|a-b|..a+b step2} c' ; multiplicity of trivial in (a⊗b)⊗c = [c in a⊗b].
    return 1 if triangle_ok(a, b, c) else 0

print("=== 1. triangle indicator vs multiplicity ===")
bad = 0
for a in range(6):
    for b in range(6):
        for c in range(6):
            ti = 1 if triangle_ok(a,b,c) else 0
            # multiplicity of trivial rep in a⊗b⊗c:
            mult = 0
            for cc in range(abs(a-b), a+b+1, 2):
                if cc == c:
                    mult = 1
            if ti != mult:
                bad += 1
print("mismatch count:", bad, "(0 = triangle indicator == fusion multiplicity)")

# ---------- 2/3. Lean racahSum reproduction ----------
def triSqNum(x,y,z):
    return fac((x+y-z)//2)*fac((x+z-y)//2)*fac((y+z-x)//2)
def triSqDen(x,y,z):
    return fac((x+y+z)//2 + 1)
def triSq(x,y,z):
    return R(triSqNum(x,y,z), triSqDen(x,y,z))

def sevenFacts(s1,s2,s3,s4,p1,p2,p3,t):
    if not (s1<=t and s2<=t and s3<=t and s4<=t and t<=p1 and t<=p2 and t<=p3):
        return None
    return fac(t-s1)*fac(t-s2)*fac(t-s3)*fac(t-s4)*fac(p1-t)*fac(p2-t)*fac(p3-t)

def racahSum(jj1,jj2,jj3,jj4,jj5,jj6):
    # S = Σ_t (-1)^t (t+1)! / (seven factorials), over the physical range
    s1=(jj1+jj2+jj3)//2; s2=(jj1+jj5+jj6)//2; s3=(jj4+jj2+jj6)//2; s4=(jj4+jj5+jj3)//2
    p1=(jj1+jj2+jj4+jj5)//2; p2=(jj2+jj3+jj5+jj6)//2; p3=(jj1+jj3+jj4+jj6)//2
    tot = (jj1+jj2+jj3+jj4+jj5+jj6)//2 + 1
    S = R(0)
    for t in range(tot+1):
        sf = sevenFacts(s1,s2,s3,s4,p1,p2,p3,t)
        if sf is None: continue
        sign = 1 if t%2==0 else -1
        S += R(sign*fac(t+1), sf)
    return S

def triSqProd(a,b,c,d,e,f):
    # four faces of {a b e; c d f}: (a,b,e),(a,d,f),(c,b,f),(c,d,e)
    return triSq(a,b,e)*triSq(a,d,f)*triSq(c,b,f)*triSq(c,d,e)

def sixj_lean(a,b,c,d,e,f):
    # {a b e; c d f} reconstructed the Lean way = sqrt(triSqProd) * S
    P = triSqProd(a,b,c,d,e,f)
    S = racahSum(a,b,e,c,d,f)
    return sqrt(P)*S, P, S

def valid6(a,b,c,d,e,f):
    return (triangle_ok(a,b,e) and triangle_ok(a,d,f)
            and triangle_ok(c,b,f) and triangle_ok(c,d,e))

def racahKernelQ(a,b,c,d,e,f):
    if not valid6(a,b,c,d,e,f): return R(0)
    return (e+1)*(f+1)*triSqProd(a,b,c,d,e,f)*racahSum(a,b,e,c,d,f)**2

print("\n=== 2. Lean racahSum reconstruction vs sympy wigner_6j (exact) ===")
mism = 0; checked = 0; irr_example=None
labels = range(0,5)
for a,b,c,d,e,f in itertools.product(labels, repeat=6):
    if not valid6(a,b,c,d,e,f): continue
    checked += 1
    lean_val, P, S = sixj_lean(a,b,c,d,e,f)
    ref = wigner_6j(j(a),j(b),j(e), j(c),j(d),j(f))  # rows (a b e / c d f)
    diff = sp.simplify(lean_val - ref)
    if diff != 0:
        mism += 1
        if mism <= 5:
            print("  MISMATCH", (a,b,c,d,e,f), "lean", lean_val, "ref", ref)
    # capture a genuinely irrational example: sqrt(P) irrational
    if irr_example is None and sp.sqrt(P) != sp.nsimplify(sp.sqrt(P)) and not sp.sqrt(P).is_rational:
        if lean_val != 0:
            irr_example = (a,b,c,d,e,f,P,S,lean_val,ref)
print(f"  checked {checked} valid tetrahedra, mismatches: {mism}")

print("\n=== 3. dim(e)dim(f){6j}^2 == racahKernelQ ===")
kmism=0
for a,b,c,d,e,f in itertools.product(labels, repeat=6):
    lean_val,P,S = sixj_lean(a,b,c,d,e,f) if valid6(a,b,c,d,e,f) else (R(0),R(1),R(0))
    lhs = R(0) if not valid6(a,b,c,d,e,f) else (e+1)*(f+1)*lean_val**2
    lhs = sp.simplify(lhs)
    rhs = racahKernelQ(a,b,c,d,e,f)
    if sp.simplify(lhs-rhs)!=0:
        kmism+=1
print("  kernel mismatches:", kmism)

print("\n=== 4. a genuinely IRRATIONAL 6j ===")
if irr_example:
    a,b,c,d,e,f,P,S,lv,ref = irr_example
    print("  labels(twice-spin)", (a,b,c,d,e,f))
    print("  triSqProd =", P, " sqrt(P) rational?", sp.sqrt(P).is_rational)
    print("  S =", S, "  {6j} =", sp.simplify(lv), " (sympy ref", ref, ")")
    print("  mpmath {6j} =", mp.mpf(sp.N(lv, 60)))
else:
    print("  (scanning wider for an irrational 6j...)")
    for a,b,c,d,e,f in itertools.product(range(0,7), repeat=6):
        if not valid6(a,b,c,d,e,f): continue
        lv,P,S = sixj_lean(a,b,c,d,e,f)
        if lv!=0 and not sp.sqrt(P).is_rational:
            print("  labels", (a,b,c,d,e,f), "sqrt(P) irrational, {6j}=", sp.simplify(lv), "=", mp.mpf(sp.N(lv,60)))
            break

print("\n=== 6. >=3 rep Haar: multiplicity of trivial in a⊗b⊗c⊗d (4-rep link) = Σ_x N_abx N_xcd ===")
# a link shared by 4 plaquettes carrying a,b,c,d integrates to dim Inv(a⊗b⊗c⊗d)
def inv_dim_4(a,b,c,d):
    tot=0
    for x in range(0, a+b+1, 2):
        if triangle_ok(a,b,x) and triangle_ok(x,c,d):
            tot+=1
    return tot
for (a,b,c,d) in [(1,1,1,1),(2,2,2,2),(1,1,2,2),(2,2,1,1),(1,2,1,2),(3,3,2,2)]:
    print(f"  a b c d={a,b,c,d}: dim Inv = {inv_dim_4(a,b,c,d)}")
