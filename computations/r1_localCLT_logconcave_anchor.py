import sympy as sp, mpmath as mp
mp.mp.dps=40
n,D,q=sp.symbols('n D q',positive=True)
# (1) LOG-CONCAVITY of the tilted fusion weight c_D=(n^2-D^2)q^{D^2} on the lattice D->D+2.
# c_D^2 - c_{D-2} c_{D+2} : q-part = q^{2D^2} vs q^{(D-2)^2+(D+2)^2}=q^{2D^2+8} (ratio q^{-8}>=1);
# parabola part identity:
lhs=(n**2-D**2)**2
rhs=(n**2-(D-2)**2)*(n**2-(D+2)**2)
gap=sp.expand(lhs-rhs)
print("parabola log-concavity gap (n²−D²)² − (n²−(D−2)²)(n²−(D+2)²) =", gap, " = 8(n²+D²−2):", sp.simplify(gap-8*(n**2+D**2-2))==0)
print("  => c_D log-concave: (parabola LC, ≥0) × (q^{2D²} ≥ q^{2D²+8} since q≤1). ELEMENTARY & CONSTRUCTIVE.\n")

# (2) Probe Lemma C structurally. Var_q(t)=Var(D^2). Is there a clean monotonicity making
#     the tilt (q->1) the maximizer of the s-curvature? Look at Var_q(t) shape in t at fixed q,
#     and whether Δ²Var_q(s) has a sign-structure vs a "free" comparison.
def Varq(qv,t):
    N=t+2; Ds=list(range(-t,t+1,2))
    w=[float(N*N-Dd*Dd)*float(qv)**(Dd*Dd) for Dd in Ds]; Z=sum(w)
    m2=sum(Dd*Dd*wi for Dd,wi in zip(Ds,w))/Z; m4=sum(Dd**4*wi for Dd,wi in zip(Ds,w))/Z
    return m4-m2*m2
# key structural question: is Var_q(t) as a function of t "linear-plus-tilt-correction" so Δ² is clean?
# free: Var_par(t)=8t(t-1)(t+4)(t+5)/175 (quartic). Δ²(quartic)=quadratic. 
# tilt correction e(t):=Var_par(t)-Var_q(t). Is e(t) CONVEX in t (so Δ²e>=0 => Δ²Var_q<=Δ²Var_par)?
print("Lemma C as convexity of the tilt-deficit e(t)=Var_par(t)−Var_q(t):  Δ²e(s)=Δ²Var_par−Δ²Var_q ≥0 ?")
def Varpar(t): return 8*t*(t-1)*(t+4)*(t+5)/175.0
for qv in [0.5,0.8,0.95,0.99]:
    ok=True; mn=9e9
    for s in range(7,60):
        d2e=(Varpar(s)-Varq(qv,s))-2*(Varpar(s+1)-Varq(qv,s+1))+(Varpar(s+2)-Varq(qv,s+2))
        mn=min(mn,d2e)
        if d2e<-1e-6: ok=False
    print(f"  q={qv}: min Δ²e over s=7..59 = {mn:.4f}   e convex (Δ²e≥0): {ok}")
