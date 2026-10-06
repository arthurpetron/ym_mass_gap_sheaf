import math
def I(n,x,terms=80):
    s=0.0
    for k in range(terms):
        s+= math.exp((2*k+n)*math.log(x/2)-math.lgamma(k+1)-math.lgamma(k+n+1))
    return s
print("beta  w^3=I2/I1   w      1-w    max side with k>=0 (w^{4s}>=0.8790)   alpha>0 needs (1-w)*4s<=2/5 -> s<=   proven k-window (1-w)128s<=1 -> s<=")
for beta in [2.0,2.2,2.3,2.4,2.5,2.6,2.7,2.85,3.0,4.0,6.0,10.0]:
    r=I(2,beta)/I(1,beta); w=r**(1/3)
    # k = 2x^3-1-x^8, x=w^{4s}; find largest s with k>=0
    smax=0
    s=1
    while True:
        x=w**(4*s); k=2*x**3-1-x**8
        if k<0: break
        smax=s; s+=1
        if s>10000: break
    sa=0.4/(4*(1-w)); sk=1/(128*(1-w))
    print(f"{beta:4.2f}  {r:.5f}  {w:.5f}  {1-w:.5f}   {smax:5d}    {sa:7.3f}    {sk:7.3f}")
# also: sides needed for loop of fixed physical size: sqrt(sigma) a values (SU(2), standard lattice results; approx)

def w_of(beta): return (I(2,beta)/I(1,beta))**(1/3)
def solve(pred):
    lo,hi=1.0,2000.0
    for _ in range(80):
        mid=(lo+hi)/2
        if pred(mid): hi=mid
        else: lo=mid
    return hi
print("\nminimal Wilson beta (matched nome w^3=I2/I1) for each guard at side s")
print(" s   k>=0(exact)   alpha>0 window (1-w)4s<=2/5   proven k-window (1-w)128s<=1")
for s in [1,2,4,8,16]:
    bk=solve(lambda b: 2*w_of(b)**(12*s)-1-w_of(b)**(32*s)>=0)
    ba=solve(lambda b: (1-w_of(b))*4*s<=0.4)
    bp=solve(lambda b: (1-w_of(b))*128*s<=1)
    print(f"{s:2d}   {bk:8.2f}      {ba:8.2f}      {bp:8.2f}")
# AF estimate: two-loop SU(2) a*Lambda ~ (b0 g^2)^(-b1/(2 b0^2)) exp(-1/(2 b0 g^2)), g^2=4/beta
import math
b0=11*2/(3*16*math.pi**2); b1=34*4/(3*(16*math.pi**2)**2)
def aL(beta):
    g2=4/beta
    return (b0*g2)**(-b1/(2*b0**2))*math.exp(-1/(2*b0*g2))
print("\nAF two-loop a*Lambda ratio a(beta)/a(2.5) (rough, Wilson):")
for beta in [2.5,3.0,4.0,16.3,31.8]:
    print(beta, aL(beta)/aL(2.5))
