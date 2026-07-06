import mpmath as mp
mp.mp.dps=50
def Ucoup(m,Q):  # full antidiagonal, i+j=m, i,j>=1
    return mp.fsum([ i*(m-i)*mp.power(Q,i*(m-i)) for i in range(1,m) ])
def Wtrunc(s,S,Q):  # acN(s+1,S)/w^f = sum_{i=1}^{s+1} i(S+2-i) Q^{i(S+2-i)}
    return mp.fsum([ i*(S+2-i)*mp.power(Q,i*(S+2-i)) for i in range(1,s+2) ])
Q=mp.mpf(4)
print("(1) Is acN numerator truncated (Wtrunc(s+1,s+1) < Ucoup(s+3))?  and by t1=(s+2)Q^{s+2}?")
for s in [2,4,6]:
    W=Wtrunc(s,s+1,Q); U=Ucoup(s+3,Q); t1=(s+2)*mp.power(Q,s+2)
    print(f"  s={s}: Wtrunc(s+1)={float(W):.3e}  Ucoup(s+3)={float(U):.3e}  diff={float(U-W):.3e}  t1={float(t1):.3e}  match={abs((U-W)-t1)<1e-30}")
print("\n(2) Does the TRUNCATED (‡_trunc) hold uniform-in-s? 256 Wtrunc(s)Wtrunc(s+2) <= 225 Q Wtrunc(s+1)^2")
for Q in [mp.mpf(4),mp.mpf(5),mp.mpf(8)]:
    worst=mp.inf
    for s in list(range(0,60))+[100,200]:
        # Wtrunc for acN(s+1, S) with S=s, s+1, s+2
        W_s = Wtrunc(s,s,Q); W_s1=Wtrunc(s,s+1,Q); W_s2=Wtrunc(s,s+2,Q)
        ratio = 225*Q*W_s1**2/(256*W_s*W_s2)
        if ratio<worst: worst=ratio; ws=s
    print(f"  Q={float(Q)}: worst (‡_trunc) ratio (want>=1) = {float(worst):.4f} at s={ws}  HOLDS={worst>=1}")
print("\n(3) Does full-range (‡) IMPLY (‡_trunc)? Compare RHS: 225Q Ucoup(s+3)^2 vs 225Q Wtrunc(s+1)^2 (Wtrunc smaller => (‡) weaker on RHS)")
Q=mp.mpf(4)
for s in [4,20]:
    print(f"  s={s}: Ucoup(s+3)^2={float(Ucoup(s+3,Q)**2):.3e} > Wtrunc(s+1)^2={float(Wtrunc(s,s+1,Q)**2):.3e}  => (‡) does NOT bound the smaller trunc-RHS")
print("\n(4) FiniteSMargin floor 40000/22801=%.4f vs uturan 256/225=%.4f" % (40000/22801, 256/225))
