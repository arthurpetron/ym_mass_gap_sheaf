import mpmath as mp
mp.mp.dps=50
def Ucoup(m,Q): return mp.fsum([ i*(m-i)*mp.power(Q,i*(m-i)) for i in range(1,m) ])
def coeffW(w,s): return (s+1)*mp.power(w, s*(s+2))
def acN(w,n,S): return mp.fsum([ coeffW(w,p)*coeffW(w,S-p) for p in range(0,n) if S-p>=0 ])
print("(A) Even TIGHT upper majorant: U(2n)*(Q^3-1) <= n^2 * Q^{n^2} * (Q^3+2Q^2-1)  [Q>=4]")
bad=0
for Q in [mp.mpf(4),mp.mpf(5),mp.mpf(8),mp.mpf(16)]:
    for n in range(1,12):
        M=n*n
        lhs=Ucoup(2*n,Q)*(Q**3-1); rhs=M*mp.power(Q,M)*(Q**3+2*Q**2-1)
        if lhs>rhs: bad+=1; print(f"   VIOLATION Q={float(Q)} n={n}: lhs>rhs")
print(f"   even tight majorant: {bad} violations" + (" -> HOLDS" if bad==0 else " -> FAILS"))
print("(B) FINAL FiniteSMargin.margin on REAL acN: 40000*acN(s+1,s)*acN(s+1,s+2) <= 22801*acN(s+1,s+1)^2, 0<w<=1/2")
bad=0; worst=mp.inf
for w in [mp.mpf(1)/2, mp.mpf(2)/5, mp.mpf(1)/3, mp.mpf(1)/4]:
    for s in list(range(0,60))+[100,200,300]:
        A=acN(w,s+1,s)*acN(w,s+1,s+2); B=acN(w,s+1,s+1)**2
        if 40000*A > 22801*B: bad+=1; print(f"   VIOLATION w={float(w):.3f} s={s}")
        r=22801*B/(40000*A)
        if r<worst: worst=r
print(f"   FiniteSMargin.margin: {bad} violations, worst (22801 B)/(40000 A)={float(worst):.4f} (want>=1)" + (" -> HOLDS" if bad==0 else " -> FAILS"))
