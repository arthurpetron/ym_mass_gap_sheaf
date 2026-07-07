"""
Field-space Balaban expansion — numeric validation.
mpmath dps 50, sympy exact. Validates:
  (1) g^2 = -log w bracket: (1-w) <= -log w <= (1-w)/w, and g^2 -> 0 as w->1.
  (2) field-space activity a_field(w)=1-w -> 0 as w->1  vs  character activity
      a_char(w)=2 w^3 -> 2 as w->1.  The INVERSION.
  (3) field cluster/polymer sum geomSum(mu*a) = sum_n (mu a)^n bounded by
      1/(1-mu a) for mu a < 1 (KP small activity), CONVERGES at weak coupling;
      character cluster sum sum_n (mu*2w^3)^n DIVERGES as w->1 (mu*2w^3 -> 2mu>1).
  (4) effect on gap = second cumulant delta_ren = 2(1-w)^2(2+w) <= 6(1-w)^2 = O(g^4);
      summable along AF w_k = 1 - 1/(k+1): sum 6/(k+1)^2 converges.
  (5) satisfiability at w=9/10 with realistic 4D connectivity mu=6.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 50

def rep(x): return mp.nstr(x, 30)

print("="*72)
print("(1) g^2 = -log w  bracket  (1-w) <= -log w <= (1-w)/w   (g^2->0 as w->1)")
print("="*72)
for w in [mp.mpf('0.1'), mp.mpf('0.5'), mp.mpf('0.8'), mp.mpf('0.9'),
          mp.mpf('0.99'), mp.mpf('0.999')]:
    t = -mp.log(w)
    lo = 1 - w
    hi = (1 - w)/w
    ok = (lo <= t <= hi)
    print(f"w={rep(w):>10}  1-w={rep(lo):>12}  g2=-logw={rep(t):>12}  "
          f"(1-w)/w={rep(hi):>12}  bracket_ok={ok}")

print()
print("="*72)
print("(2) INVERSION:  field activity 1-w -> 0   vs   char activity 2w^3 -> 2")
print("="*72)
for w in [mp.mpf('0.1'), mp.mpf('0.5'), mp.mpf('0.7937'), mp.mpf('0.9'),
          mp.mpf('0.99'), mp.mpf('0.999')]:
    af = 1 - w
    ac = 2*w**3
    print(f"w={rep(w):>10}  a_field=1-w={rep(af):>12}  a_char=2w^3={rep(ac):>12}  "
          f"field<char? {af < ac}")
# crossover a_field = a_char : 1-w = 2w^3
wc = sp.nsolve(sp.Eq(1 - sp.Symbol('w'), 2*sp.Symbol('w')**3), sp.Symbol('w'), 0.6)
print(f"\ncrossover 1-w = 2w^3 at w* = {wc}")
print("=> for w>w* character activity EXCEEDS field activity; at w->1 field->0, char->2.")

print()
print("="*72)
print("(3) CLUSTER SUM convergence.  KP geometric bound sum_n (mu a)^n = mu a/(1-mu a)")
print("    field: mu*(1-w) < 1  <=>  w > 1 - 1/mu   (weak coupling, deep UV)")
print("    char : mu*2w^3  < 1  <=>  w < (1/(2mu))^{1/3}  (strong coupling)")
print("="*72)
for mu in [1, 6]:
    thF = 1 - mp.mpf(1)/mu           # field converges for w > thF
    thC = (mp.mpf(1)/(2*mu))**(mp.mpf(1)/3)   # char converges for w < thC
    print(f"\n  mu={mu}: field converges w>{rep(thF)} ;  char converges w<{rep(thC)}")
    for w in [mp.mpf('0.5'), mp.mpf('0.9'), mp.mpf('0.99')]:
        aF = 1 - w; aC = 2*w**3
        muaF = mu*aF; muaC = mu*aC
        # partial geometric sum N=200
        N = 200
        sF = sum(muaF**n for n in range(1, N)) if muaF < 1 else mp.inf
        boundF = muaF/(1-muaF) if muaF < 1 else mp.inf
        sC = sum(muaC**n for n in range(1, N)) if muaC < 1 else mp.inf
        boundC = muaC/(1-muaC) if muaC < 1 else mp.inf
        print(f"    w={rep(w):>8}  field mu*a={rep(muaF):>10} sum~{rep(sF):>12} "
              f"[conv={muaF<1}] | char mu*a={rep(muaC):>10} [conv={muaC<1}]")

print()
print("="*72)
print("(4) EFFECT ON GAP = second cumulant delta_ren = 2(1-w)^2(2+w) <= 6(1-w)^2 = O(g^4)")
print("="*72)
w = sp.Symbol('w')
dren = 2*(1-w)**2*(2+w)
env = 6*(1-w)**2
diff = sp.expand(env - dren)
print(f"6(1-w)^2 - delta_ren = {sp.factor(diff)}  (>=0 for w<=1, =2(1-w)^3)")
print(f"delta_ren/(1-w)^2 = 2(2+w) -> 6 as w->1, so effect = O((1-w)^2) = O(g^4). OK")
# summability along AF w_k = 1 - 1/(k+1) => 1-w_k = 1/(k+1)
S = mp.nsum(lambda k: 6/(k+1)**2, [0, mp.inf])
print(f"\nsum_k 6*(1-w_k)^2 = sum_k 6/(k+1)^2 = 6*zeta(2) = {rep(S)} = pi^2 = {rep(mp.pi**2)}")
print("=> effect on gap is SUMMABLE along AF (~1/k^2), CONVERGES.")

print()
print("="*72)
print("(5) SATISFIABILITY at w=9/10, realistic 4D connectivity mu=6")
print("="*72)
w9 = mp.mpf('0.9'); mu = 6
aF = 1 - w9; aC = 2*w9**3
print(f"w=9/10: field a=1-w=1/10={rep(aF)}, mu*a=6/10={rep(mu*aF)} < 1  => field cluster")
print(f"        sum CONVERGES, bound 1/(1-6/10)=1/(4/10)=5/2={rep(1/(1-mu*aF))}")
print(f"        char  a=2w^3={rep(aC)} > 1  => even mu=1: 1-a={rep(1-aC)} < 0 => DIVERGES")
print("  => at the SAME weak point the FIELD gate holds while the CHARACTER gate fails.")

# exact rational checks for the Lean decide facts
print()
print("EXACT (sympy) facts for Lean:")
print(f"  fieldActivity(9/10) = 1 - 9/10 = {sp.Rational(1,10)}")
print(f"  6*fieldActivity(9/10) = 6/10 = {sp.Rational(6,10)} ; 1 - 6/10 = {sp.Rational(4,10)} > 0  (field gate mu=6 holds)")
print(f"  coeffW(9/10,1)=2*(9/10)^3 = {2*sp.Rational(9,10)**3} > 1  (char gate fails)")
print(f"  delta_ren(9/10) = 2*(1/10)^2*(2+9/10) = {2*sp.Rational(1,10)**2*(2+sp.Rational(9,10))} = 29/500")
print(f"  6*(1/10)^2 = 6/100 = 3/50 = {sp.Rational(6,100)} ; 29/500 <= 3/50 ? {sp.Rational(29,500) <= sp.Rational(3,50)}")
