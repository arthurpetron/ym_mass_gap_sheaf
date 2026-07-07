import mpmath as mp
import sympy as sp
mp.mp.dps = 50

# ---- codebase objects (exact) -----------------------------------------------
# dimQ(s)=s+1, C4(s)=s(s+2), coeffW(w,s)=dimQ(s)*w^{C4(s)}.
# Gap-channel (fundamental, s=1): coeffW(w,1)=2*w^3.  Vacuum s=0: coeffW=1.
# Two-plaquette connected Ursell (shared link, one common excited rep r>=1):
#   activity zeta2(w,r) = (coeffW w r)^2   [MayerTwoPlaquette.connectedActivity2_eqv]
#   Z2 - Z_disc  <->  sum_{r>=1} (coeffW w r)^2   (the INDUCED 2-plaquette coupling)
def dimQ(s): return s+1
def C4(s):   return s*(s+2)
def coeffW(w,s): return dimQ(s)*w**C4(s)

def cluster2(w,Rmax=200):
    # induced two-plaquette coupling = sum over common excited rep
    return sum(coeffW(w,r)**2 for r in range(1,Rmax+1))

print("### STRONG-COUPLING induced 2-plaquette coupling (connected Ursell) vs single term")
print(" w      1-w      coeffW1=2w^3   induced2=sum(coeffW_r)^2  induced2/single  KP:2w^3<1?")
for ws in ['0.1','0.3','0.5','0.6','0.7','0.7937','0.85','0.9','0.99']:
    w=mp.mpf(ws)
    single=coeffW(w,1)
    ind2=cluster2(w)
    ratio=ind2/single
    conv = single<1
    print(f" {ws:7} {mp.nstr(1-w,3):7} {mp.nstr(single,6):12} {mp.nstr(ind2,6):16} "
          f"{mp.nstr(ratio,6):12} conv={conv}")

# leading induced/single ratio is EXACTLY 2w^3 (sympy):
w=sp.symbols('w',positive=True)
single=2*w**3
lead=(2*w**3)**2   # (coeffW w 1)^2
print("\nsympy exact leading induced/single =", sp.simplify(lead/single), " -> equals coeffW(w,1)=2w^3")
print("cluster-expansion convergence radius w* : solve 2w^3=1 ->",
      sp.nsimplify(sp.Rational(1,2)**sp.Rational(1,3)), "=", mp.nstr((mp.mpf(1)/2)**(mp.mpf(1)/3),8))

# ---- The FULL activity sum, and the KP-style single-plaquette condition ------
# connectivity: a fixed plaquette in 4D borders many neighbours; connected animals
# of n plaquettes ~ mu^n.  Convergence needs mu*coeffW(w,1) < 1.  Report threshold.
for mu in [1,4,6]:
    wth = (mp.mpf(1)/(2*mu))**(mp.mpf(1)/3)
    print(f"KP threshold (connectivity mu={mu}):  2*mu*w^3<1  ->  w < {mp.nstr(wth,8)}")
