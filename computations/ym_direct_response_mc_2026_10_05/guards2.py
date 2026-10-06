import math
def ratio(n,x,N=4000):
    # I_{n+1}(x)/I_n(x) via backward continued fraction
    r=0.0
    for m in range(N,n,-1):
        r=1.0/(2*m/x + r)
    return r  # r = I_{n+1}/I_n after loop ends at m=n+1
def w_of(beta): return ratio(1,beta)**(1/3)
for b in [2.4,10]:
    print("check I2/I1",b,ratio(1,b))
def solve(pred):
    lo,hi=1.0,1e5
    for _ in range(100):
        mid=(lo+hi)/2
        if pred(mid): hi=mid
        else: lo=mid
    return hi
print(" s   k>=0(exact)   alpha>0 window    proven k-window")
for s in [1,2,4,8,16]:
    bk=solve(lambda b: 2*w_of(b)**(12*s)-1-w_of(b)**(32*s)>=0)
    ba=solve(lambda b: (1-w_of(b))*4*s<=0.4)
    bp=solve(lambda b: (1-w_of(b))*128*s<=1)
    print(f"{s:2d}   {bk:9.2f}      {ba:8.2f}      {bp:9.2f}")
