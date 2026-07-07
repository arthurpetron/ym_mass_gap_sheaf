import mpmath as mp
from mpmath import mpf, log
mp.mp.dps = 50

# SU(2) heat-kernel character coefficient (tree normalization): c_s = (s+1) w^{s(s+2)}
def c(w, s):
    return (s+1)*mp.power(w, s*(s+2))

# Fusion of TWO coefficient sequences a,b -> mode s:
#   (a*b)_s = sum_{i,j: |i-j|<=s<=i+j, i+j+s even} a_i b_j
def fuse(a, b, Smax):
    out = [mpf(0)]*(Smax+1)
    for i in range(len(a)):
        for j in range(len(b)):
            lo=abs(i-j); hi=i+j
            s=lo
            while s<=hi and s<=Smax:
                out[s]+=a[i]*b[j]
                s+=2
    return out

def pfold(w, p, Smax, trunc):
    # p-fold self-fusion of coeffW, keeping modes up to trunc at each step
    base=[c(w,s) for s in range(trunc+1)]
    cur=list(base)
    for _ in range(p-1):
        cur=fuse(cur, base, trunc)
    return cur[:Smax+1]

def ratio_fused(w,p,trunc):
    seq=pfold(w,p,max(2,trunc),trunc)
    return seq[1]/seq[0]

# --- The model quantities ---
def bound6p(w,p):        # 6 p (1-w)^2  (the transverse quadratic bound, dimQ1=2 => 6p)
    return 6*p*(1-w)**2
def delta_ren(w,p):      # bondMovingDeltaRen = p*2*(3(1-w)-(1-w^3)) = p*2*(1-w)^2(2+w)
    return p*2*(3*(1-w)-(1-w**3))

print("=== (1) RAW single-link (p=1) excited/vacuum ratio 2w^3 vs 6(1-w)^2 ===")
worst=None
for i in range(1,51):
    w=mpf(i)/100  # w in (0,0.5]
    if w>mpf('0.5'): break
    raw=2*w**3
    b=6*(1-w)**2
    r=raw/b
    if worst is None or r>worst[0]: worst=(r,w,raw,b)
print("  w in (0,0.5]: worst raw/bound =", mp.nstr(worst[0],6),"at w=",mp.nstr(worst[1],4),
      " raw=",mp.nstr(worst[2],6)," bound=",mp.nstr(worst[3],6))
# also near w->1
for w in [mpf('0.6'),mpf('0.8'),mpf('0.9'),mpf('0.99')]:
    raw=2*w**3; b=6*(1-w)**2
    print("  w=",float(w)," raw=",mp.nstr(raw,6)," 6(1-w)^2=",mp.nstr(b,6),
          " raw<=bound?", raw<=b)

print("\n=== (2) RENORMALIZED single-mode defect delta_ren=2(1-w)^2(2+w) vs 6(1-w)^2 (ALL w) ===")
worst=None
for i in range(1,100):
    w=mpf(i)/100
    d=delta_ren(w,1); b=bound6p(w,1)
    r=d/b if b>0 else mpf(0)
    if worst is None or r>worst[0]: worst=(r,w)
print("  worst delta_ren/bound over w in(0,1) =",mp.nstr(worst[0],8),"at w=",mp.nstr(worst[1],4),
      " (should be <=1, tight at w->0: (2+w)/3 -> 2/3? check)")
print("  delta_ren/bound at w=0.001:",mp.nstr(delta_ren(mpf('0.001'),1)/bound6p(mpf('0.001'),1),8))

print("\n=== (3) REAL FUSED p-fold excited/vacuum ratio vs 6p(1-w)^2, strong coupling w<=1/2 ===")
for p in [1,2,4,8]:
    worst=None
    for i in range(1,51):
        w=mpf(i)/100
        rf=ratio_fused(w,p,trunc=40)
        b=bound6p(w,p)
        r=rf/b
        if worst is None or r>worst[0]: worst=(r,w,rf,b)
    print(f"  p={p}: worst ratio_fused/6p(1-w)^2 =",mp.nstr(worst[0],6),
          "at w=",mp.nstr(worst[1],4)," fusedratio=",mp.nstr(worst[2],6)," bound=",mp.nstr(worst[3],6),
          " HOLDS?" ,worst[0]<=1)

print("\n=== (4) REAL FUSED p-fold ratio vs bound at w->1 (weak coupling: renormalization essential) ===")
for p in [1,8]:
    for w in [mpf('0.5'),mpf('0.7'),mpf('0.9'),mpf('0.99')]:
        rf=ratio_fused(w,p,trunc=60)
        b=bound6p(w,p)
        print(f"  p={p} w={float(w)}: fusedratio={mp.nstr(rf,6)} 6p(1-w)^2={mp.nstr(b,6)} raw<=bound? {rf<=b}")
