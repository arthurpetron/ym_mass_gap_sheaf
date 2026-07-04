from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 50
def Ds(t): return list(range(-t,t+1,2))
def theta(wf,t): return mp.fsum(wf**(mp.mpf(D*D)/2) for D in Ds(t))
def xi(wf,t): return mp.fsum(mp.mpf(D*D)*wf**(mp.mpf(D*D)/2) for D in Ds(t))
def den(wf,t):
    M=t+2; return mp.fsum((M*M-D*D)*wf**(mp.mpf(D*D)/2) for D in Ds(t))
def num(wf,t):
    M=t+2; return mp.fsum((D*D)*(M*M-D*D)*wf**(mp.mpf(D*D)/2) for D in Ds(t))
def V(wf,t): return num(wf,t)/den(wf,t)
def Gv(wf,t): return xi(wf,t)/theta(wf,t)
def slack(wf,s): return V(wf,s)+V(wf,s+2)-2*V(wf,s+1)+2
def Ge(wf):
    r=wf*wf; th=mp.fsum(r**(j*j) for j in range(-400,401)); xj=mp.fsum((2*j)**2*r**(j*j) for j in range(-400,401)); return xj/th
def Go(wf):
    r=wf*wf; th=mp.fsum(r**(mp.mpf((2*j+1)**2)/4) for j in range(-400,401)); xj=mp.fsum((2*j+1)**2*r**(mp.mpf((2*j+1)**2)/4) for j in range(-400,401)); return xj/th

print("Q1. inf over (s,w) of  slack / sectorflip   (sectorflip=2(1-(Go-Ge))=2*th4(w^2)^4>0)")
print("    if inf = delta > 0 uniformly, then R1 <= [slack >= delta*sectorflip], a clean")
print("    'the flip-slack is never fully eaten' statement.  else corr eats ALL the slack somewhere.")
worst=mp.inf; wa=None
for i in range(2,700):
    wf=mp.mpf(i)/700
    sf=2*(1-(Go(wf)-Ge(wf)))
    if sf<=0: continue
    for s in range(0,30):
        r=slack(wf,s)/sf
        if r<worst: worst=r; wa=(float(wf),s)
print(f"    inf slack/sectorflip = {float(worst):.6f}  at (w,s)={wa}")
print("    (>0 means the correction never eats the ENTIRE flip slack; the residual margin is this.)")

print("\nQ2. Pure-Gaussian (mass-factor-removed) floor:  does G(t)=xi/theta already obey")
print("    Delta^2_1 G(s) >= -2 ?  (G has NO (M^2-D^2) mass factor; isolates the coupling.)")
gw=True
for i in range(2,300):
    wf=mp.mpf(i)/300
    for s in range(0,26):
        if Gv(wf,s)+Gv(wf,s+2)-2*Gv(wf,s+1)+2 < -1e-12: gw=False
print(f"    Gaussian-variance floor Delta^2 G + 2 >= 0 for all tested (s,w): {gw}")

print("\nQ3. sector-flip ALONE as a lower bound: is  slack >= 0*  guaranteed by  sectorflip>=0")
print("    minus a bound on corr?  Report  min slack, min sectorflip, and confirm sign pattern.")
for wv in ['0.02','0.2079','0.4083','0.7071','0.95']:
    wf=mp.mpf(wv); sf=float(2*(1-(Go(wf)-Ge(wf))))
    ms=min(float(slack(wf,s)) for s in range(0,30))
    print(f"    w={wv:<7} sectorflip={sf:.5f}  min_s slack={ms:.5f}  slack/flip@min={ms/sf:.4f}")

print("\nQ4. 144/25 sharp envelope re-confirm & continuum monotonicity of ratio in s")
def ratio(wf,s):
    ww=wf*wf; return slack(wf,s)/(ww*(1-ww))
for s in [0,1,2,3,4,6,10]:
    grid=[mp.mpf(i)/3000 for i in range(1,3000)]
    m=min(ratio(wf,s) for wf in grid)
    print(f"    s={s:>2}: inf_w slack/(w^2(1-w^2)) = {float(m):.6f}")
print("    s=0 -> 144/25 = 5.76 (sharp); monotone up to 8 = continuum. binding = FINITE s=0.")
