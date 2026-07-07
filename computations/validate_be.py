"""
Pin down the exact Biedenharn-Elliott PENTAGON arrangement and verify it
exactly (sympy) + high precision (mpmath). Also a non-degenerate irrational 6j.
Spins are ordinary half-integers here (not twice-spin) for clarity with sympy.
"""
import sympy as sp
from sympy import Rational as R, sqrt
from sympy.physics.wigner import wigner_6j
import itertools, random
import mpmath as mp
mp.mp.dps = 50

def w6(a,b,c,d,e,f):
    return wigner_6j(a,b,c,d,e,f)

def tri(a,b,c):
    return abs(a-b)<=c<=a+b and ( (a+b+c) == int(a+b+c) )

# Biedenharn-Elliott (standard form, Varshalovich 9.8.4 / Wikipedia):
#  {a b e}{c d e}   summed ... The canonical BE sum rule:
#   sum_x (-1)^{x+ a+b+c+d+e+f+g+h+j} (2x+1)
#        {a b x}{c d x}{e f x}
#        {c d p}{e f q}{a b r}   <- placeholder; we TEST several forms.
#
# We test the widely-quoted form:
#   sum_x (2x+1) (-1)^{phi+x}
#        {a b x; c d p} {c d x; e f q} {e f x; b a r}
#     = {p q r; e a d} {p q r; f b c}
# with phi = a+b+c+d+e+f+p+q+r.

def be_lhs(a,b,c,d,e,f,p,q,r):
    tot = R(0)
    # x ranges over half-integers where all three 6j triangles can be satisfied
    xmax = int(2*min(a+b, c+d, e+f)) + 2
    x = 0
    vals = set()
    # enumerate x in steps of 1/2 up to a+b etc.
    xx = R(0)
    hi = min(a+b, c+d, e+f)
    lo = max(abs(a-b), abs(c-d), abs(e-f))
    n = lo
    while n <= hi:
        t1 = w6(a,b,n, c,d,p)
        t2 = w6(c,d,n, e,f,q)
        t3 = w6(e,f,n, b,a,r)
        term = (2*n+1)*t1*t2*t3
        sign = (-1)**int(a+b+c+d+e+f+p+q+r + n)
        tot += sign*term
        n += 1
    return sp.simplify(tot)

def be_rhs(a,b,c,d,e,f,p,q,r):
    return sp.simplify(w6(p,q,r, e,a,d) * w6(p,q,r, f,b,c))

print("=== Biedenharn-Elliott candidate (signed) ===")
tests = [
    (R(1,2),R(1,2),R(1,2),R(1,2),R(1,2),R(1,2), 1,1,1),
    (1,1,1,1,1,1, 1,1,1),
    (1,R(1,2),R(1,2),1,R(1,2),R(1,2), 1,1,0),
    (1,1,R(1,2),R(1,2),1,1, 1,1,1),
]
for t in tests:
    a,b,c,d,e,f,p,q,r = t
    L = be_lhs(a,b,c,d,e,f,p,q,r); Rr = be_rhs(a,b,c,d,e,f,p,q,r)
    print("  ", t, "LHS", L, "RHS", Rr, "EQ" if sp.simplify(L-Rr)==0 else "NEQ")

# Try the cleaner "composition" BE form actually used to derive pentagon:
#   {a b p}{c d p}  ->  sum_x (2x+1){a b x;c d p}...
# The TRUE, textbook Biedenharn-Elliott (Messiah / Edmonds):
#   sum_n (-1)^{n+ ...}(2n+1){a b n; c d p}{c d n; e f q}{e f n; b a r}
#      = {p q r; e a d}{p q r; f b c}
# Above 'be_lhs' already encodes exactly this. Report tally over random valid tuples.

print("\n=== BE over random half-integer tuples ===")
random.seed(0)
def randspin():
    return R(random.randint(0,4),2)
ok=0; tot=0; neq=0
for _ in range(400):
    a,b,c,d,e,f = [randspin() for _ in range(6)]
    # p,q,r are the three "diagonal" couplings; choose valid ones
    for p in [x/1 for x in []]:
        pass
    # choose p in tri(a,b,.) & tri(c,d,.); q in tri(c,d,.)&tri(e,f,.); r in tri(e,f,.)&tri(b,a,.)
    ps=[R(k,2) for k in range(0,9) if tri(a,b,R(k,2)) and tri(c,d,R(k,2))]
    qs=[R(k,2) for k in range(0,9) if tri(c,d,R(k,2)) and tri(e,f,R(k,2))]
    rs=[R(k,2) for k in range(0,9) if tri(e,f,R(k,2)) and tri(b,a,R(k,2))]
    if not(ps and qs and rs): continue
    p=random.choice(ps); q=random.choice(qs); r=random.choice(rs)
    # RHS 6j's need triangles (p,q,r,e,a,d) and (p,q,r,f,b,c)
    L=be_lhs(a,b,c,d,e,f,p,q,r); Rr=be_rhs(a,b,c,d,e,f,p,q,r)
    tot+=1
    if sp.simplify(L-Rr)==0: ok+=1
    else:
        neq+=1
        if neq<=6:
            print("  NEQ", (a,b,c,d,e,f,p,q,r), "L",L,"R",Rr)
print(f"  BE holds on {ok}/{tot} random valid tuples")

# non-degenerate irrational 6j (all reps >=1)
print("\n=== non-degenerate irrational 6j (all spins>0) ===")
def twicej(a,b,c,d,e,f): return  # placeholder
found=0
for a,b,c,d,e,f in itertools.product([R(1,2),1,R(3,2),2], repeat=6):
    v=w6(a,b,c,d,e,f)
    if v==0: continue
    if not v.is_rational:
        print("  {%s %s %s; %s %s %s} = %s = %s"%(a,b,c,d,e,f,v, mp.mpf(sp.N(v,50))))
        found+=1
        if found>=4: break
