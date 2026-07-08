import mpmath as mp
mp.mp.dps=40
# Verify the theta-constant identity as a formal power series:
#   q dlog(theta2/theta3)/dq = (1/4) theta4^4
# Build power series in q to high order via mpmath taylor of numeric funcs is hard;
# instead compare Lambert series numerically at several q, AND extract series coeffs by finite differences.

def th2(q,N=400): return 2*sum(mp.power(q,(n+mp.mpf(1)/2)**2) for n in range(0,N))
def th3(q,N=400): return 1+2*sum(mp.power(q,n*n) for n in range(1,N))
def th4(q,N=400): return 1+2*sum((-1)**n*mp.power(q,n*n) for n in range(1,N))

def qdlog_ratio(q):
    h=mp.mpf(10)**(-25)
    f=lambda x: mp.log(th2(x)/th3(x))
    # q d/dq = derivative wrt log q
    return mp.diff(lambda u: f(mp.e**u), mp.log(q))

for qexp in ['0.1','0.3','0.5','0.7']:
    q=mp.mpf(qexp)
    lhs=qdlog_ratio(q)
    rhs=th4(q)**4/4
    print(f"q={qexp}: qdlog(th2/th3)={mp.nstr(lhs,25)}  (1/4)th4^4={mp.nstr(rhs,25)}  diff={mp.nstr(lhs-rhs,5)}")

# Also extract Lambert series: claim (1/4)(theta4^4 -1) = 2*sum_{n>=1}[2n q^{2n}/(1+q^{2n}) - (2n-1)q^{2n-1}/(1+q^{2n-1})]
def lambert_side(q,N=2000):
    s=mp.mpf(0)
    for n in range(1,N):
        s+= 2*n*mp.power(q,2*n)/(1+mp.power(q,2*n)) - (2*n-1)*mp.power(q,2*n-1)/(1+mp.power(q,2*n-1))
    return 2*s
print("\nLambert vs (1/4)(th4^4-1):")
for qexp in ['0.1','0.3','0.5','0.7']:
    q=mp.mpf(qexp)
    L=lambert_side(q); R=(th4(q)**4-1)/4
    print(f"q={qexp}: L={mp.nstr(L,22)} R={mp.nstr(R,22)} diff={mp.nstr(L-R,5)}")
