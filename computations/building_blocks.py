import mpmath as mp
mp.mp.dps=40
def th4(r,N=800): return 1+2*sum((-1)**n*mp.power(r,n*n) for n in range(1,N))
def th4_prod(r,N=4000):
    p=mp.mpf(1)
    for n in range(1,N):
        p*=(1-mp.power(r,2*n))*(1-mp.power(r,2*n-1))**2
    return p
def divisor_sum_4(n):
    return sum(d for d in range(1,n+1) if n%d==0 and d%4!=0)
def th4_4_lambert(r,N=400):
    return 1+8*sum(((-1)**n)*divisor_sum_4(n)*mp.power(r,n) for n in range(1,N))

print("theta4 series vs product (positivity form):")
for rexp in ['0.1','0.5','0.9']:
    r=mp.mpf(rexp)
    print(f"  r={rexp}: series={mp.nstr(th4(r),18)} product={mp.nstr(th4_prod(r),18)} in(0,1)? {0<th4(r)<1}")
print("\ntheta4^4 vs divisor-Lambert 1+8*sum(-1)^n sigma*(n) q^n:")
for rexp in ['0.05','0.1','0.3','0.5']:
    r=mp.mpf(rexp)
    print(f"  r={rexp}: th4^4={mp.nstr(th4(r)**4,20)} lambert={mp.nstr(th4_4_lambert(r),20)} diff={mp.nstr(th4(r)**4-th4_4_lambert(r),5)}")
print("\nth4^4 first coeffs (should be 1,-8,24,-32,24,-48,...):", [((-1)**n)*8*divisor_sum_4(n) for n in range(1,7)])
