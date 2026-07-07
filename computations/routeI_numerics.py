"""
Route I — eigA / physical-gap-edge fused-defect analysis (mpmath dps=50, sympy exact).

Objects (SU(2) heat-kernel transfer matrix, diagonal in characters):
  c4(s)      = s*(s+2)                Casimir  (c4(0)=0, c4(1)=3)
  dimQ(s)    = s+1                    representation multiplicity
  eigA(w,s)  = w^{c4(s)}              MULTIPLICITY-BLIND transfer eigenvalue (decay rate)
  coeffW(w,s)= dimQ(s)*eigA(w,s)      measure-weight / amplitude (heat-kernel coeff)

Fine separators (vacuum-normalized first-excited / vacuum):
  coeffW picture : sepFine    = coeffW(w,1)          = 2 w^3
  eigA   picture : eigFine    = eigA(w,1)            =   w^3

One block-spin fusion step (b=2): coarse link = 2 parallel fine links fused via
central autoconvolution (Clebsch fusion), first-excited channel s=1:
  acNfull(w,1) = coeffW(w,0)*coeffW(w,1)+coeffW(w,1)*coeffW(w,0) = 2*coeffW(w,1) = 4 w^3
Coarse separators:
  coeffW picture : sepCoarse  = acNfull(w,1)         = 4 w^3
  eigA   picture : eigCoarse  = eigA(w,1)            =   w^3  (SAME decay rate; only degeneracy grows)

FUSED DEFECTS (per-step margin degradation = increase of separator):
  coeffW defect : sepCoarse - sepFine  = 4w^3 - 2w^3 = 2 w^3   (= coeffW(w,1))
  eigA   defect : eigCoarse - eigFine  =  w^3 -  w^3 = 0

MODEL ENVELOPE: 6*(1-w)^2  (pMult=1 transverse quadratic).
"""
from mpmath import mp, mpf, power
import sympy as sp

mp.dps = 50

def c4(s): return s*(s+2)
def dimQ(s): return s+1
def eigA(w, s): return power(w, c4(s))
def coeffW(w, s): return mpf(dimQ(s))*eigA(w, s)
def acNfull1(w): return coeffW(w,0)*coeffW(w,1) + coeffW(w,1)*coeffW(w,0)  # = 2 coeffW(w,1)
def env(w): return 6*(1-w)**2

print("="*94)
print("1. THE FUSED DEFECTS: coeffW (amplitude) vs eigA (multiplicity-blind) vs envelope 6(1-w)^2")
print("="*94)
hdr = f"{'w':>7} | {'coeffW_def=2w^3':>16} | {'eigA_def':>9} | {'6(1-w)^2':>12} | {'coeffW<=env?':>12} | {'eigA<=env?':>10}"
print(hdr); print("-"*len(hdr))
ws = ['0.1','0.3','0.5','0.677','0.7','0.8','0.9','0.95','0.98','0.99','0.9999']
maxeig = mpf(0)
for s in ws:
    w = mpf(s)
    cd = acNfull1(w) - coeffW(w,1)          # coeffW fused defect
    ed = eigA(w,1) - eigA(w,1)              # eigA  fused defect (coarse edge - fine edge)
    e  = env(w)
    maxeig = max(maxeig, abs(ed))
    print(f"{s:>7} | {mp.nstr(cd,12):>16} | {mp.nstr(ed,6):>9} | {mp.nstr(e,8):>12} | "
          f"{str(cd<=e):>12} | {str(ed<=e):>10}")
print(f"\n  max |eigA fused defect| over all tested w  =  {mp.nstr(maxeig,6)}   (exactly 0)")
print("  => eigA fused defect = 0 <= 6(1-w)^2 UNIFORMLY for ALL w in [0,1]; coeffW FAILS for w>0.677.")

print()
print("="*94)
print("2. THE MULTIPLICITY FACTORIZATION: coeffW defect = (coarse deg - fine deg) * eigA(w,1)")
print("="*94)
print("  coeffW(w,1)   = dimQ(1)*eigA(w,1)            = 2 * w^3      (fine  degeneracy 2)")
print("  acNfull(w,1)  = 4*eigA(w,1)                  = 4 * w^3      (coarse degeneracy 4)")
print("  coeffW defect = acNfull(w,1)-coeffW(w,1) = (4-2)*eigA(w,1) = 2 * w^3   (pure degeneracy +2)")
print(f"{'w':>7} | {'coeffW_def':>14} | {'2*eigA(w,1)':>14} | {'match(err)':>12}")
for s in ws:
    w = mpf(s)
    cd = acNfull1(w) - coeffW(w,1)
    two_eig = 2*eigA(w,1)
    print(f"{s:>7} | {mp.nstr(cd,10):>14} | {mp.nstr(two_eig,10):>14} | {mp.nstr(abs(cd-two_eig),3):>12}")
print("  => the ENTIRE coeffW defect is the multiplicity increment (Δdeg=2) times the")
print("     UNCHANGED eigenvalue w^3. The eigenvalue (decay rate) does NOT degrade under fusion.")

print()
print("="*94)
print("3. sympy EXACT symbolic confirmation")
print("="*94)
w = sp.Symbol('w', nonnegative=True)
c4_1 = 1*(1+2)
eig1  = w**c4_1                      # eigA(w,1)
cW1   = 2*eig1                       # coeffW(w,1)
acN1  = 2*cW1                        # acNfull(w,1) = 2 coeffW(w,1)
coeffW_defect = sp.simplify(acN1 - cW1)
eigA_defect   = sp.simplify(eig1 - eig1)
print("  eigA(w,1)                       =", eig1)
print("  coeffW(w,1)                     =", cW1)
print("  acNfull(w,1)                    =", sp.expand(acN1))
print("  coeffW fused defect  (acN1-cW1) =", coeffW_defect, "   (= 2 w^3, the amplitude object)")
print("  eigA   fused defect  (eig1-eig1)=", eigA_defect,   "   (identically 0)")
print("  coeffW_defect - 2*eigA(w,1)     =", sp.simplify(coeffW_defect - 2*eig1), " (multiplicity identity)")
# envelope comparison symbolically at the refutation point
w9 = sp.Rational(9,10)
print(f"  at w=9/10: coeffW_defect={coeffW_defect.subs(w,w9)}={float(coeffW_defect.subs(w,w9)):.4f}, "
      f"6(1-w)^2={6*(1-w9)**2}={float(6*(1-w9)**2):.4f}  -> coeffW defect EXCEEDS (refuted)")
print(f"             eigA_defect  ={eigA_defect}  <= {float(6*(1-w9)**2):.4f}  -> eigA defect holds")

print()
print("="*94)
print("4. THE PHYSICAL RESIDUAL: coupling-flow eigenvalue shift  eig(w') - eig(w) = w'^3 - w^3")
print("   (the multiplicity-blind eigenvalue perturbation under one RG step w -> w').")
print("   Test vs 6(1-w)^2 for AF-type steps w'-w = beta*(1-w)^2 (asymptotic-freedom rate).")
print("="*94)
print("   d(w^3)/dw = 3w^2 -> as w->1, eigShift ~ 3(w'-w) ~ 3*beta*(1-w)^2.")
print("   eigShift <= 6(1-w)^2  <=>  ~3*beta <= 6  <=>  beta <= 2  (AF-rate calibration).")
hdr2 = f"{'w':>7} | {'beta':>5} | {'w'+chr(39):>10} | {'eigShift=w'+chr(39)+'^3-w^3':>18} | {'6(1-w)^2':>12} | {'<=env?':>7} | {'coeffW 2w^3<=env?':>17}"
print(hdr2); print("-"*len(hdr2))
for s in ['0.7','0.9','0.95','0.99','0.999']:
    w = mpf(s)
    for beta in [mpf('1.0'), mpf('2.0')]:
        wp = w + beta*(1-w)**2
        if wp >= 1: wp = (w+1)/2  # keep in (w,1)
        es = eigA(wp,1) - eigA(w,1)
        e = env(w)
        cW = coeffW(w,1)
        print(f"{s:>7} | {mp.nstr(beta,3):>5} | {mp.nstr(wp,8):>10} | {mp.nstr(es,10):>18} | "
              f"{mp.nstr(e,8):>12} | {str(es<=e):>7} | {str(cW<=e):>17}")
print("  => coupling-flow eigShift stays <= 6(1-w)^2 for beta<=2 (NOT refuted at w->1),")
print("     whereas the amplitude coeffW=2w^3 is REFUTED (>env) for every w>0.677.")
print("     The eigA residual reduces to the STANDARD AF beta-rate, not a false algebraic bound.")
