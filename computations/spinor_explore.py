import mpmath as mp
from mpmath import mpf, mp as MP
import sympy as sp
MP.dps = 50

# Dictionary: weight over pairs (n,m), n+m=N=t+2, n,m>=1, weight = n*m*w^(n^2+m^2)
# D = m-n = N-2n. V(t)=<D^2>.
def V(t, w):
    w = mpf(w); N = t+2
    num = mpf(0); den = mpf(0)
    for n in range(1, N):
        m = N-n
        wt = n*m*w**(n*n+m*m)
        D = m-n
        den += wt
        num += D*D*wt
    return num/den

# check known values
w = mpf('0.3')
print("V(0)=",V(0,w),"(exp 0)")
print("V(1)=",V(1,w),"(exp 1)")
print("V(2)=",V(2,w),"exp:",12*w*w/(2+3*w*w))

# Second difference of V, and R1: Delta^2 V >= -2
print("\n R1 check: Delta^2 V(t) = V(t+2)-2V(t+1)+V(t), should be >= -2")
for wv in ['0.1','0.3','0.5','0.7','0.9','0.99']:
    wm=mpf(wv)
    mins=[]
    for t in range(0,40):
        d2 = V(t+2,wm)-2*V(t+1,wm)+V(t,wm)
        mins.append(d2)
    print(f"w={wv}: min Delta^2 V over t=0..39 = {min(mins)}  (>= -2 ?)")

# Equivalent: convexity of V(t)+t^2  (Delta^2(t^2)=2)
print("\n Convexity of V(t)+t^2 (Delta^2 >= 0):")
for wv in ['0.1','0.3','0.5','0.7','0.9','0.99']:
    wm=mpf(wv)
    mins=[]
    for t in range(0,40):
        f=lambda tt: V(tt,wm)+mpf(tt)**2
        d2=f(t+2)-2*f(t+1)+f(t)
        mins.append(d2)
    print(f"w={wv}: min Delta^2 (V+t^2) = {min(mins)}")
