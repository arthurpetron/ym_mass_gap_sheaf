from fractions import Fraction as F

def c4(s): return s*(s+2)
def dimQ(s): return s+1
def qpow(w,n): 
    r=F(1)
    for _ in range(n): r*=w
    return r
def coeffW(w,s): return F(dimQ(s))*qpow(w,c4(s))

def acN(w,n,t):
    return sum(coeffW(w,p)*coeffW(w,t-p) for p in range(n) if 0<=t-p)
def dmomN(w,n,t):
    tot=F(0)
    for p in range(n):
        if t-p<0: continue
        D=t-2*p
        tot+=F(D*D)*coeffW(w,p)*coeffW(w,t-p)
    return tot

def D2mean(w,s,t):   # ⟨D²⟩_t at cutoff s+1
    n=s+1
    a=acN(w,n,t)
    if a==0: return None
    return dmomN(w,n,t)/a

print("floor check  Δ²⟨D²⟩ ≥ -2  and effective 'K' after +t² spend (should be ~0, NOT 3/4)")
print(f"{'w':>6} {'s':>3} {'D2s':>10} {'D2s1':>10} {'D2s2':>10} {'Δ²⟨D²⟩':>10} {'Δ²(⟨D²⟩+t²)':>12}")
worst=F(10)
for wnum in [1,2,3,5,7,9,10,20,30,50,80,99]:
    w=F(wnum,100)
    for s in range(0,9):
        d0=D2mean(w,s,s); d1=D2mean(w,s,s+1); d2=D2mean(w,s,s+2)
        if None in (d0,d1,d2): continue
        d2var=d0+d2-2*d1           # Δ²⟨D²⟩
        conv=d2var+2               # Δ²(⟨D²⟩+t²), since Δ²(t²)=2
        worst=min(worst,d2var)
        if s in (0,2,4) and wnum in (2,10,50,99):
            print(f"{float(w):6.2f} {s:3d} {float(d0):10.4f} {float(d1):10.4f} {float(d2):10.4f} {float(d2var):10.5f} {float(conv):12.6f}")
print("worst-case Δ²⟨D²⟩ over grid =", float(worst), " (floor is -2; convexity residual = worst+2 =", float(worst+2),")")
