import mpmath as mp, sympy as sp
mp.mp.dps = 50

print("="*70)
print("SU(2) heat-kernel: coeffW(t,s) = dim(s)*exp(-t*C2(s)), C2(s)=s(s+2)/4")
print("fundamental s=1: dim=2, C2=3/4. Avg plaquette P(t)=<1/2 chi_{1/2}> = e^{-3t/4}")
print("g^2 = t.  fieldActivity(w)=1-w with w=e^{-t}=e^{-g^2}.")
print("="*70)

# ---- ENTIRE check: coeffW is entire in t (radius of conv of e^{-3t/4}) ----
t = sp.symbols('t')
ser = sp.series(1 - sp.exp(-sp.Rational(3,4)*t), t, 0, 8).removeO()
print("\n[ENTIRE] char MOMENT activity 1-e^{-3t/4} Taylor (t=g^2):")
print("  ", ser)
coeffs = [sp.nsimplify(ser.coeff(t,k)) for k in range(1,8)]
print("   coeffs:", coeffs, " -> leading 3/4 = C2(fund). Series converges (entire).")

# ---- (A) char MOMENT activity <= g^2 ? ----
print("\n[A] char MOMENT activity 1-e^{-3t/4}  vs  g^2=t  and  fieldActivity=1-e^{-t}")
def moment(tt): return 1 - mp.e**(-mp.mpf(3)/4*tt)
def fieldact(tt): return 1 - mp.e**(-tt)
worst_ratio_g2 = mp.mpf(0); worst_over_field = mp.mpf('-1e9')
viol_g2=0; viol_field=0
for i in range(1,200001):
    tt = mp.mpf(i)/20000   # t in (0,10]
    m = moment(tt)
    if m > tt: viol_g2+=1
    r = m/tt
    if r>worst_ratio_g2: worst_ratio_g2=r
    d = m - fieldact(tt)
    if d>1e-40: viol_field+=1
    if d>worst_over_field: worst_over_field=d
print(f"   moment<=g^2 violations over t in (0,10]: {viol_g2}   worst ratio moment/g^2 -> {mp.nstr(worst_ratio_g2,8)}")
print(f"   moment<=fieldActivity(1-w) violations: {viol_field}   worst (moment-fieldact)= {mp.nstr(worst_over_field,6)} (<=0 means always below)")

# ---- (B) strong-coupling POLYMER activity a_{1/2}=e^{-3t/4} vs g^2 ----
print("\n[B] strong-coupling POLYMER activity a_{1/2}=e^{-3t/4}  vs  g^2=t")
def polymer(tt): return mp.e**(-mp.mpf(3)/4*tt)
below=[]; 
for tt in [mp.mpf('0.01'),mp.mpf('0.1'),mp.mpf('0.3'),mp.mpf('4')/7,mp.mpf('0.6'),mp.mpf('1'),mp.mpf('2'),mp.mpf('4')]:
    print(f"   t={mp.nstr(tt,4):>8}: e^(-3t/4)={mp.nstr(polymer(tt),8):>12}  g^2={mp.nstr(tt,6):>10}  activity<=g^2? {polymer(tt)<=tt}")
# threshold where e^{-3t/4}=t
f = lambda x: mp.e**(-mp.mpf(3)/4*x)-x
root = mp.findroot(f, 0.7)
print(f"   crossover e^(-3t/4)=t at t={mp.nstr(root,10)}  (below this weak-coupling regime the polymer activity EXCEEDS g^2)")
print(f"   lower bound check: 1-3t/4 > t  <=> t<4/7={mp.nstr(mp.mpf(4)/7,8)}; e^(-3t/4)>=1-3t/4 always -> exceeds g^2 for t<4/7")

# ---- field-space single-mode Gaussian z1 = 1-e^{-t}(1-2t), g^2=4t ----
print("\n[FIELD-SPACE] single-mode Gaussian z1=1-e^{-t}(1-2t), g^2=4t (t=g^2/4)")
tau = sp.symbols('tau')
zf = sp.series(1 - sp.exp(-tau)*(1-2*tau), tau, 0, 6).removeO()
print("   z1(t) =", zf, "  leading 3t = (3/4)g^2 since g^2=4t")

# compare the two entire objects: char moment (g^2=t) vs field single-mode (g^2=4t)
print("\n[DICHOTOMY] both entire, leading (3/4)g^2, but DIFFER at O(g^4):")
g = sp.symbols('g2')  # g^2
char_in_g2 = sp.series(1-sp.exp(-sp.Rational(3,4)*g), g,0,4).removeO()
field_in_g2 = sp.series((1 - sp.exp(-g/4)*(1-2*(g/4))), g,0,4).removeO()
print("   char moment  (t=g^2)    :", sp.expand(char_in_g2))
print("   field single (t=g^2/4)  :", sp.expand(field_in_g2))
print("   difference              :", sp.expand(char_in_g2-field_in_g2), " -> NOT the same object")

# ---- one-point moment vs connected z1: Ursell/sign check leading vs subleading ----
print("\n[SURROGATE] moment <1-1/2 chi> = z1 + sum_{n>=2}(alternating Ursell); equal only at leading order")
print("   -> character moment is a SURROGATE for connected z1 (agree at (3/4)g^2, differ beyond)")
