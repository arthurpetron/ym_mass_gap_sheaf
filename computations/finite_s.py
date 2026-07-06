import mpmath as mp
mp.mp.dps=50
# real coeffW: dimQ(s)=s+1, c4(s)=s(s+2); coeffW = (s+1) w^{s(s+2)}
def coeffW(w,s): return (s+1)*mp.power(w, s*(s+2))
def acN(w,n,S):  # sum_{p<n} coeffW(p) coeffW(S-p)
    return mp.fsum([ coeffW(w,p)*coeffW(w,S-p) for p in range(0,n) if S-p>=0 ])
print("ACTUAL acN Turan ratio B/A = acN(s+1,s+1)^2 / (acN(s+1,s)*acN(s+1,s+2)), w=1/2")
print("  need: SymMinor 256/225=%.4f ; FiniteSMargin 40000/22801=%.4f" % (256/225, 40000/22801))
for w in [mp.mpf(1)/2, mp.mpf(1)/3, mp.mpf(1)/4]:
    worst=mp.inf; ws=None
    for s in list(range(0,80))+[100,150,200,300]:
        A = acN(w,s+1,s)*acN(w,s+1,s+2)
        B = acN(w,s+1,s+1)**2
        r = B/A
        if r<worst: worst=r; ws=s
    fin = 40000/22801
    print(f"  w={str(w)[:8]}: worst B/A = {float(worst):.5f} at s={ws}   FiniteSMargin({fin:.4f}) HOLDS={float(worst)>=fin}  margin={float(worst)/fin:.4f}x")
