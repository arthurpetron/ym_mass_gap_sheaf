import mpmath as mp
from fractions import Fraction as F
mp.mp.dps = 60

# m_phys = 1 - e^{-1/e}  (concreteTowerE seed w0_exp = e^{-1})
e = mp.e
m_phys = 1 - mp.e**(-1/e)
print("m_phys = 1 - e^{-1/e} =", mp.nstr(m_phys, 40))
print("  > 3/10 ?", m_phys > mp.mpf(3)/10, "  gap:", mp.nstr(m_phys-mp.mpf(3)/10,10))
print("  > 271/1000 ?", m_phys > mp.mpf(271)/1000)
# boosted seed w0_exp = 1 -> m_phys = 1 - e^{-1}
print("m_phys(seed=1) = 1 - e^{-1} =", mp.nstr(1-mp.e**(-1),20))

print("\n--- TELESCOPING eigenvalue-shift budget  Be = 1 - w0^3 ---")
for w0 in [F(9,10), F(11,12), F(14,15), F(19,20)]:
    Be = 1 - w0**3
    print(f"  w0={w0}={float(w0):.4f}  1-w0={float(1-w0):.4f}  Be=1-w0^3={Be}={float(Be):.5f}  "
          f"anchor-dom vs m_phys(0.3078): {'OK' if float(Be)<float(m_phys) else 'FAIL'}  margin={float(m_phys)-float(Be):.4f}")

print("\n--- verify telescoping identity: sum_{k<K}(w_{k+1}^3-w_k^3) = w_K^3 - w_0^3 ---")
# canonical AF trajectory w_k = 1 - 1/(k+1+cut), anchor cut=11 => w_0 = 11/12
cut = 11
def w(k): return F(1) - F(1, k+1+cut)   # w_0 = 1-1/12 = 11/12
w0 = w(0)
for K in [1,5,20,100,1000]:
    s = sum(w(k+1)**3 - w(k)**3 for k in range(K))
    lhs = w(K)**3 - w0**3
    assert s == lhs, (s, lhs)
    print(f"  K={K:5d}  tailSum={float(s):.6f}  w_K^3-w_0^3={float(lhs):.6f}  <= 1-w_0^3={float(1-w0**3):.6f}  eps_k>=0 telescopes exactly OK")

print("\n--- NAIVE non-anchored budget (canonical A=1,B=1 from k=0, w_0=0): Sum 6(1-w_k)^2 ---")
# w_k = 1-1/(k+1): 1-w_k = 1/(k+1); sum_{k>=0} 6/(k+1)^2 = 6*pi^2/6 = pi^2
naive = 6*mp.pi**2/6
print("  Sum_{k>=0} 6/(k+1)^2 = pi^2 =", mp.nstr(naive,8), "  >> m_phys => anchor-dom FAILS (bad news, honest)")

print("\n--- Route H squared-majorant budget with deep-UV anchor B (1-w_k=1/(k+B)) ---")
for B in [10,12,20,30,50]:
    trig = mp.zeta(2,B)  # sum_{n>=0} 1/(B+n)^2 = Hurwitz zeta(2,B)
    Bd = 6*trig
    print(f"  B={B:3d} (w_0=1-1/B={1-1/B:.3f})  Sum 6(1-w_k)^2 = 6*zeta(2,{B}) = {float(Bd):.5f}  "
          f"{'OK<m_phys' if float(Bd)<float(m_phys) else 'need bigger B'}")

print("\n--- compare eigShift(telescope) vs 6(1-w)^2 per-step at w_0=11/12 pair (sanity: eigShift <= delta_ren) ---")
w0=F(11,12); w1=F(12,13)
eig = float(w1**3 - w0**3)
dren = float(2*(1-w0)**2*(2+w0))   # bondMovingDeltaRen
env  = float(6*(1-w0)**2)
print(f"  eigShift(w0->w1)={eig:.6f}  delta_ren(w0)={dren:.6f}  6(1-w0)^2={env:.6f}   eigShift<=delta_ren<=env: {eig<=dren<=env}")
