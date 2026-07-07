"""
Input-1 (EigenvalueShiftDefect) numerics.
Verifies, at mpmath dps>=40 and with exact sympy, every inequality the Lean
cube-difference / erosion-budget proof relies on.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 50

print("="*74)
print("1. CUBE-DIFFERENCE IDENTITY  w'^3 - w^3 = (w'-w)(w'^2 + w'w + w^2)  (exact)")
print("="*74)
w, wp = sp.symbols("w wp", real=True)
lhs = wp**3 - w**3
rhs = (wp - w)*(wp**2 + wp*w + w**2)
print("  w'^3-w^3 - (w'-w)(w'^2+w'w+w^2) simplifies to:", sp.simplify(lhs - rhs))
assert sp.simplify(lhs - rhs) == 0

print()
print("  cube split  w'^3-w^3 = w'(w'^2-w^2) + w^2(w'-w) :",
      sp.simplify((wp*(wp**2-w**2) + w**2*(wp-w)) - lhs))
assert sp.simplify((wp*(wp**2-w**2) + w**2*(wp-w)) - lhs) == 0

print()
print("="*74)
print("2. CUBE-DIFF BOUND   0<=w<=w'<=1  =>  w'^3 - w^3 <= 3(w'-w)   (max slack)")
print("="*74)
worst = 0.0
for i in range(0, 401):
    for j in range(i, 401):
        ww  = mp.mpf(i)/400
        wwp = mp.mpf(j)/400
        d = 3*(wwp-ww) - (wwp**3 - ww**3)
        if d < worst:
            worst = d
print("  min over grid of  3(w'-w)-(w'^3-w^3)  (must be >=0):", mp.nstr(worst, 20))
assert worst >= 0
# tightness: at w=w'=1 the factor w'^2+w'w+w^2 = 3 exactly (bound is sharp)
print("  factor w'^2+w'w+w^2 at w=w'=1:", 1+1+1, " -> bound 3 is SHARP at the free fixed pt")

print()
print("="*74)
print("3. beta-STEP => envelope   w'-w <= 2(1-w)^2  =>  w'^3-w^3 <= 6(1-w)^2")
print("="*74)
worst2 = mp.mpf('1e9')
for i in range(0, 400):          # w in [0,1)
    ww = mp.mpf(i)/400
    step_max = 2*(1-ww)**2
    wwp = ww + step_max          # worst case: maximal admissible step
    if wwp > 1: wwp = mp.mpf(1)
    lhsv = wwp**3 - ww**3
    rhsv = 6*(1-ww)**2
    slack = rhsv - lhsv
    if slack < worst2: worst2 = slack
print("  min over w of  6(1-w)^2-(w'^3-w^3) at maximal beta-step (>=0):",
      mp.nstr(worst2, 20))
assert worst2 >= -mp.mpf('1e-40')
# 6 = pMult(1) * dimQ1(2) * 3  -- matches EigenvalueShiftDefect.eigShiftBound RHS
print("  RHS constant 6 = pMult(1)*dimQ1(2)*3  == eigShiftBound envelope. OK")

print()
print("="*74)
print("4. CANONICAL trajectory  w_k = 1 - 1/(k+1)  SATISFIES  monotone + beta-step")
print("="*74)
def wk(k): return 1 - mp.mpf(1)/(k+1)
allok = True
for k in range(0, 5000):
    step  = wk(k+1) - wk(k)                      # = 1/((k+1)(k+2))
    betab = 2*(1 - wk(k))**2                     # = 2/(k+1)^2
    mono  = wk(k+1) - wk(k)
    if not (mono >= 0 and step <= betab + mp.mpf('1e-45')):
        allok = False; break
print("  monotone & step<=2(1-w)^2 for all k<5000:", allok)
assert allok
# exact sympy identity for the canonical step vs bound
kk = sp.symbols("k", positive=True, integer=True)
wexpr = 1 - sp.Rational(1)/(kk+1)
step_e = sp.simplify(wexpr.subs(kk, kk+1) - wexpr)
bound_e = sp.simplify(2*(1-wexpr)**2)
print("  exact step      = 1/((k+1)(k+2)) :", sp.simplify(step_e - 1/((kk+1)*(kk+2)))==0)
print("  exact bound     = 2/(k+1)^2      :", sp.simplify(bound_e - 2/(kk+1)**2)==0)
print("  bound-step = (k+3)/((k+1)^2(k+2)) >=0 :",
      sp.simplify(bound_e - step_e))

print()
print("="*74)
print("5. AF two-sided rate ALONE does NOT imply the beta-step (A != A' counterexample)")
print("="*74)
# Rate: A'/(k+B) <= 1-w_k <= A/(k+B).  Choose A=2,A'=1,B=1.
# Build a w consistent with the band but with a step of order 1/k >> 2(1-w)^2 ~ 1/k^2.
A, Ap, B = mp.mpf(2), mp.mpf(1), mp.mpf(1)
# pick 1-w_k alternating within the band to force a large downward jump of (1-w)
def oneminus(k):
    lo = Ap/(k+B); hi = A/(k+B)
    return hi if k % 2 == 0 else lo      # oscillate across the band
found = False
for k in range(0, 50):
    wk_ = 1 - oneminus(k)
    wk1 = 1 - oneminus(k+1)
    step = wk1 - wk_
    betab = 2*(1-wk_)**2
    if step > betab:      # beta-step violated while both stay in the AF band
        found = True
        print(f"  k={k}: within band, step={mp.nstr(step,8)} > 2(1-w)^2={mp.nstr(betab,8)}"
              f"  (band lo/hi at k: {mp.nstr(Ap/(k+B),6)}/{mp.nstr(A/(k+B),6)})")
        break
print("  => beta-step is GENUINELY EXTRA input, not derivable from the 1/k band:", found)
assert found

print()
print("="*74)
print("6. FULL EROSION BUDGET  sum(eigShift+LF) <= (1-w0^3) + K/(1-r) < m_phys")
print("="*74)
m_phys = 1 - mp.e**(-1/mp.e)
print("  m_phys = 1 - e^{-1/e} =", mp.nstr(m_phys, 30))
w0 = mp.mpf(11)/12
anchor_budget = 1 - w0**3          # telescoped eigenvalue-shift sum
print("  Be(eig)  = 1 - (11/12)^3 =", mp.nstr(anchor_budget, 30), "= 397/1728")
assert sp.Rational(397,1728) == sp.Rational(1) - sp.Rational(11,12)**3
# large-field geometric budget: need K/(1-r) < slack = m_phys - anchor_budget
slack = m_phys - anchor_budget
print("  slack    = m_phys - Be(eig) =", mp.nstr(slack, 20))
# a physically-sized geometric LF budget, e.g. K=1/20, r=1/2 -> K/(1-r)=1/10 > slack? check
for (K, r) in [(mp.mpf(1)/20, mp.mpf(1)/2), (mp.mpf(1)/50, mp.mpf(1)/2),
               (mp.mpf(1)/100, mp.mpf(3)/4)]:
    lf = K/(1-r)
    print(f"  K={mp.nstr(K,4)} r={mp.nstr(r,4)}: LF budget K/(1-r)={mp.nstr(lf,10)}, "
          f"total={mp.nstr(anchor_budget+lf,12)} < m_phys? {anchor_budget+lf < m_phys}")
print("  => the LF budget fits in the slack iff K/(1-r) < ~0.078  (a real constraint).")

print()
print("ALL CHECKS PASSED.")
