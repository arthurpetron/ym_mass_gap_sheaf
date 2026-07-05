import mpmath as mp, json, math
mp.mp.dps=30

# ---------- measure family mu_t(D) ∝ (n²−D²) w^{D²/2}, converge to Gaussian ----------
def measure(t,w):
    n=t+2; Ds=list(range(-t,t+1,2))
    wt=[float((n*n-D*D))*float(w)**(D*D/2.0) for D in Ds]
    Z=sum(wt); p=[x/Z for x in wt]
    mean=sum(D*pi for D,pi in zip(Ds,p))
    var=sum((D-mean)**2*pi for D,pi in zip(Ds,p))
    sd=var**0.5
    return Ds,p,sd
conv=[]
for (t,w,lab) in [(16,0.85,"t=16, w=.85"),(30,0.92,"t=30, w=.92"),(60,0.97,"t=60, w=.97")]:
    Ds,p,sd=measure(t,w)
    # rescale: x=D/sd, density*sd (so area under standardized ~1 per unit x, comparable to N(0,1))
    pts=[[D/sd, pi*sd/ (2.0)] for D,pi in zip(Ds,p)]  # /2: spacing between D is 2, so density = p/2
    conv.append({"label":lab,"pts":pts})
# standard gaussian
xg=[i/40.0 for i in range(-140,141)]
gauss=[[x, math.exp(-x*x/2)/math.sqrt(2*math.pi)] for x in xg]

# ---------- M1 / M2 envelopes over u ----------
def theta_even(u,K=200):
    A=B=C=mp.mpf(0)
    for k in range(-K,K+1):
        tk=u**(k*k); A+=tk; B+=4*k*k*tk; C+=16*k**4*tk
    return A,B,C
def theta_odd(u,K=200):
    a=b=c=mp.mpf(0)
    for k in range(0,K):
        tk=u**(k*(k+1)); a+=tk; b+=(2*k+1)**2*tk; c+=(2*k+1)**4*tk
    return a,b,c
us=[mp.mpf(x)/1000 for x in range(250,999,6)]
M1e=[];M1o=[];M2e=[];M2o=[]
for u in us:
    A,B,C=theta_even(u); a,b,c=theta_odd(u)
    Ve=B/A; Vo=b/a; Vare=(A*C-B*B)/(A*A); Varo=(a*c-b*b)/(a*a)
    uf=float(u)
    M1e.append([uf,float(Ve*(1-u))]); M1o.append([uf,float(Vo*(1-u))])
    M2e.append([uf,float(Vare*(1-u)**2)]); M2o.append([uf,float(Varo*(1-u)**2)])

# ---------- modular dual: terms-to-converge, q-series vs Poisson dual ----------
def qterms(u,tol=1e-9):
    eps=-math.log(u); s=1.0; k=1
    while True:
        term=2*math.exp(-eps*k*k); s+=term
        if term<tol*s: return k
        k+=1
def dualterms(u,tol=1e-9):
    eps=-math.log(u); pref=math.sqrt(math.pi/eps); s=1.0; m=1
    while True:
        term=2*math.exp(-math.pi*math.pi*m*m/eps); s+=term
        if term<tol*s: return m
        m+=1
umod=[0.5+0.499*i/120 for i in range(0,121)]
modq=[[u,qterms(u)] for u in umod]
modd=[[u,dualterms(u)] for u in umod]

# ---------- Lemma C: Δ²Var_q(s) vs q, max at q=1 = Δ²Var_par ----------
def Varq_par(q,t):  # variance of D^2 under (n²−D²) q^{D²}, |D|<=t, D≡t(2)
    n=t+2; Ds=list(range(-t,t+1,2))
    wt=[float(n*n-D*D)*q**(D*D) for D in Ds]
    Z=sum(wt); m2=sum(D*D*wi for D,wi in zip(Ds,wt))/Z; m4=sum(D**4*wi for D,wi in zip(Ds,wt))/Z
    return m4-m2*m2
def d2Varq(q,s): return Varq_par(q,s)-2*Varq_par(q,s+1)+Varq_par(q,s+2)
lemC=[]
for s in [7,9,11]:
    par=96*(s*s+6*s+7)/175.0
    qs=[0.02+0.98*i/120 for i in range(0,121)]
    lemC.append({"s":s,"par":par,"pts":[[q, d2Varq(q,s)] for q in qs]})

json.dump({"conv":conv,"gauss":gauss,"M1e":M1e,"M1o":M1o,"M2e":M2e,"M2o":M2o,
           "modq":modq,"modd":modd,"lemC":lemC},
          open("viz.json","w"))
print("wrote viz.json; conv sd example, M1 ends:", M1e[0], M1e[-1], "M2 ends:", M2e[0], M2e[-1])
print("mod at u=.98: q-terms", qterms(0.98), "dual-terms", dualterms(0.98))
print("lemC s=7 par", 96*(49+42+7)/175.0, "d2Varq(1,7)", d2Varq(1.0,7))
