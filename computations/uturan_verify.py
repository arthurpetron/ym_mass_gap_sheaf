import mpmath as mp
mp.mp.dps=60
def U(m,Q):
    # U(m) = sum_{i+j=m, i,j>=1} i*j*Q^{i*j}
    return mp.fsum([ i*(m-i)*mp.power(Q, i*(m-i)) for i in range(1,m) ])
print("Decisive: does U(s+3)^2 / (U(s+2)U(s+4)) >= 256/(225 Q) hold UNIFORM in s (incl. LARGE s)?")
for Q in [mp.mpf(4), mp.mpf('4.5'), mp.mpf(5), mp.mpf(8), mp.mpf(16), mp.mpf(64)]:
    need = mp.mpf(256)/(225*Q)
    worst = mp.inf; worst_s=None
    for s in list(range(0,60))+[100,200,400,800]:
        r = U(s+3,Q)**2/(U(s+2,Q)*U(s+4,Q))
        if r < worst: worst=r; worst_s=s
    lead = 1/mp.sqrt(Q)
    print(f"  Q={float(Q):>5}: need>={float(need):.5f}  worst ratio={float(worst):.5f} at s={worst_s}  (leading 1/sqrtQ={float(lead):.5f})  HOLDS={worst>=need}  margin={float(worst/need):.3f}x")
print("\nCheck the reduced rational Q-inequalities (agent's claim):")
for Q in [mp.mpf(4), mp.mpf('4.5'), mp.mpf(5), mp.mpf(8)]:
    even = 900 >= 256*(1+2/(Q-1))**2
    odd = 225*(1+3/(2*Q))**2*Q >= 256*(2*Q*Q/(Q*Q-1))**2
    print(f"  Q={float(Q)}: even(900>=256(1+2/(Q-1))^2)={even}  odd(225(1+3/2Q)^2 Q>=256(2Q^2/(Q^2-1))^2)={odd}")
print("\n even reduces to Q>=23/7=%.4f; odd P(Q)>=0" % (23/7))
