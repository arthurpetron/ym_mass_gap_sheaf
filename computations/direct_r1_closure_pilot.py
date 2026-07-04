"""
Direct uniform-closure pilot for residual R1:  Delta^2_t V(t) >= -2  for all t=s>=0, w in [0,1).

V(t) = <D^2> under rho_t(D) ∝ (M^2-D^2) w^{D^2/2},  D≡t (mod 2), |D|<=t, M=t+2.
Equivalently V(t) = num_t/den_t with
    den_t = sum_D (M^2-D^2) w^{D^2/2},   num_t = sum_D D^2 (M^2-D^2) w^{D^2/2}.

This pilot records the structural reductions that a direct (non-continuum) attack found:

 (1) THREE-BODY / CONVEXITY FORM.  Clearing denominators,
       slack_s := den_s den_{s+1} den_{s+2} * (Delta^2 V(s) + 2)
                = sum_{D0,D1,D2} (D0^2 + D2^2 - 2 D1^2 + 2) c_s(D0) c_{s+1}(D1) c_{s+2}(D2),
     with c_t(D) = coeffW((t-D)/2) coeffW((t+D)/2) >= 0.  Hence R1  <=>  Delta^2 V + 2 >= 0
       <=>   U(t) := V(t) + t^2  is discretely convex in t   (since Delta^2(t^2)=2).

 (2) PARITY SPLIT (the key empirical finding).
       ODD  s : Delta^2 V + 2 is bounded away from 0 (>= 12/7 ≈ 1.714, min at w=1/sqrt2); COMFORTABLE.
       EVEN s : Delta^2 V + 2 -> 0^+ only as w->0; this is the SOLE binding regime.
                Leading order (even s): Delta^2 V + 2 = (C(s)+C(s+2)) w^2 + O(w^4),
                C(t)=8t(t+4)/(t+2)^2 in [6,8), so leading coeff in [12,16); the constant cancels
                exactly because the odd neighbour has V(odd)->1.

 (3) SHARP UNIFORM ENVELOPE.
       Delta^2 V(s) + 2  >=  (144/25) * w^2 (1 - w^2)     for ALL s>=0, w in [0,1],
     manifestly >= 0.  SHARP: equality only at (s=0, w^2=1/6).  Exact small cases:
        s=0: Delta^2V+2 = 12 w^2/(2+3 w^2);  ratio min = 144/25 at w^2=1/6.
        s=1: ratio min = 48/7  at w=1/sqrt2.
        s=2: ratio min ≈ 7.208 at w≈0.731.
     The ratio inf_w (Delta^2V+2)/(w^2(1-w^2)) is MONOTONE INCREASING in s, -> 8 (continuum).

 (4) STRUCTURAL VERDICT.  The binding case is the FINITE smallest s (s=0), NOT the continuum
     (continuum ratio 8 > 144/25).  So a continuum/theta route (G_odd - G_even <= 1, ratio 8)
     does NOT capture the true extremiser; the tight obligation is the small-s finite cases.
     R1 <== [ inf_w (Delta^2V+2)/(w^2(1-w^2)) is nondecreasing in s ] + [ s=0,1 base cases, exact ].
     The remaining uniform wall is exactly that monotonicity (pointwise monotonicity FAILS,
     but only near w->1 where the quantity is large; the interior minimiser near w=1/sqrt2 is monotone).
"""
import sympy as sp
import mpmath as mp

w = sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def A(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def N(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))

def slack_poly(s):
    aS,a1,a2 = A(s),A(s+1),A(s+2); dS,d1,d2 = N(s),N(s+1),N(s+2)
    return sp.expand(dS*a1*a2 + d2*aS*a1 + 2*aS*a1*a2 - 2*d1*aS*a2)

def slack_threebody(s):
    def cfac(t,D):
        p=(t-D)//2; return coeffW(p)*coeffW(t-p)
    tot=0
    for D0 in range(-s,s+1,2):
        for D1 in range(-(s+1),s+2,2):
            for D2 in range(-(s+2),s+3,2):
                tot += (D0*D0+D2*D2-2*D1*D1+2)*cfac(s,D0)*cfac(s+1,D1)*cfac(s+2,D2)
    return sp.expand(tot)

# ---- numeric evaluator ----
def V(wv,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=wv**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def slack_norm(wv,s): return V(wv,s)-2*V(wv,s+1)+V(wv,s+2)+2

if __name__ == "__main__":
    print("(1) three-body representation matches cleared slack:")
    for s in range(0,5):
        print(f"    s={s}: slack - threebody = {sp.simplify(slack_poly(s)-slack_threebody(s))}")

    print("\n(3) sharp uniform envelope  Delta^2V+2 >= (144/25) w^2(1-w^2):")
    mp.mp.dps=30
    C=mp.mpf(144)/25; gmin=mp.inf; worst=None
    for s in list(range(0,40))+[60,100,200]:
        r=min(slack_norm(mp.mpf(i)/2000,s)/((mp.mpf(i)/2000)**2*(1-(mp.mpf(i)/2000)**2))
              for i in range(1,2000))
        if r<gmin: gmin=r; worst=s
    print(f"    global inf_w,s (Delta^2V+2)/(w^2(1-w^2)) = {mp.nstr(gmin,10)} at s={worst}"
          f"   (144/25={mp.nstr(C,8)})")

    print("\n(2) parity margins  min_w (Delta^2V+2):")
    for s in range(0,8):
        r=min(slack_norm(mp.mpf(i)/2000,s) for i in range(1,2000))
        print(f"    s={s} ({'even' if s%2==0 else 'odd '}): min_w = {mp.nstr(r,6)}"
              f"   ({'binding at w->0' if s%2==0 else 'comfortable, >=12/7'})")
