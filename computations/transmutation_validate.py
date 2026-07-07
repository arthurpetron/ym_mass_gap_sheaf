from mpmath import mp, mpf, e, exp
mp.dps = 50

# concreteCRealFlowE, b=1 (b+1=2): exponent seed w0 = e^{-1}; w_k = e^{-1}/2^k
# separators sep_k = e^{-w_k};  geomSumC(x,2) = 1 + x
w0 = exp(-1)
def sep(k): return exp(-(w0/ mpf(2)**k))

# eroding lattice margin 1 - sep_N  and spacing rescaling prod_{j=1}^N (1+sep_j)
def prodTail(N):
    p = mpf(1)
    for j in range(1, N+1):
        p *= (1 + sep(j))
    return p

print("m_phys target = 1 - sep_0 =", 1 - sep(0))
print(f"{'N':>3} {'1-sepN(erode)':>18} {'prodTail(resc)':>18} {'dimMargin':>22} {'|dimMargin-(1-sep0)|':>22}")
target = 1 - sep(0)
for N in [0,1,2,4,8,16,32,64,128]:
    m = 1 - sep(N)
    pt = prodTail(N)
    dm = m*pt
    print(f"{N:>3} {mp.nstr(m,8):>18} {mp.nstr(pt,8):>18} {mp.nstr(dm,16):>22} {mp.nstr(abs(dm-target),4):>22}")

# self-similar flow law check: sep_k == (sep_{k+1})^2
print("\nflow-law sep_k = (sep_{k+1})^2 max err:",
      mp.nstr(max(abs(sep(k) - sep(k+1)**2) for k in range(40)), 5))

# ---- contrast: the NAIVE eroding eigenvalue margin 1-w^3 fails multiplicative ----
# canonical AF w_k = 1 - 1/(k+1); lattice gap 1-w_k^3 ~ 3/k -> 0 (power law)
def wAF(k): return 1 - mpf(1)/(k+1)
print("\n--- naive lattice eigenvalue margin 1-w_k^3 (canonical AF, power-law) ---")
for k in [10, 100, 1000, 10000]:
    m = 1 - wAF(k)**3
    print(f"k={k:>6}  1-w^3 = {mp.nstr(m,6):>12}   *2^k -> blows up;  ~3/k = {mp.nstr(3/mpf(k),6)}")
# The point: 1-w^3 ~ 3/k is POWER-LAW; *b^k (exp) diverges -> no transmutation.
# The genuine lattice gap is exp(-1/(2 beta0 g^2)) ~ b^{-k} (EXPONENTIAL): sep_k above.
