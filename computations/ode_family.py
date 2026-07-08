import mpmath as mp
mp.mp.dps=35
def th2(q,N=400): return 2*sum(mp.power(q,(n+mp.mpf(1)/2)**2) for n in range(0,N))
def th3(q,N=400): return 1+2*sum(mp.power(q,n*n) for n in range(1,N))
def th4(q,N=400): return 1+2*sum((-1)**n*mp.power(q,n*n) for n in range(1,N))
def dlog(f,q): return mp.diff(lambda u: mp.log(f(mp.e**u)), mp.log(q))
for qexp in ['0.2','0.5']:
    q=mp.mpf(qexp)
    print(f"q={qexp}")
    print("  dlog(th2/th3)=(1/4)th4^4 ? ", mp.nstr(dlog(th2,q)-dlog(th3,q),8),"vs",mp.nstr(th4(q)**4/4,8))
    print("  dlog(th3/th4)=(1/4)th2^4 ? ", mp.nstr(dlog(th3,q)-dlog(th4,q),8),"vs",mp.nstr(th2(q)**4/4,8))
    print("  dlog(th2/th4)=(1/4)th3^4 ? ", mp.nstr(dlog(th2,q)-dlog(th4,q),8),"vs",mp.nstr(th3(q)**4/4,8))
    print("  Jacobi th3^4=th2^4+th4^4 ? ", mp.nstr(th3(q)**4-th2(q)**4-th4(q)**4,5))
