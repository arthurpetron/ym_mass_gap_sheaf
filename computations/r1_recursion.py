import sympy as sp
w=sp.symbols('w')
def thmom(t,j): return sum((t-2*p)**(2*j)*w**sp.Rational((t-2*p)**2,2) for p in range(t+1))
def den(t):  # M^2 theta - xi,  M=t+2
    M=t+2; return sp.expand(M**2*thmom(t,0)-thmom(t,1))
def num(t):  # M^2 xi - zeta
    M=t+2; return sp.expand(M**2*thmom(t,1)-thmom(t,2))
def V(t): return sp.cancel(num(t)/den(t))

print("=== recursion den_{t+2} - den_t  =?= 4(t+3) theta_{t+2} ===")
for t in range(0,6):
    lhs=sp.expand(den(t+2)-den(t)); rhs=sp.expand(4*(t+3)*thmom(t+2,0))
    print(f" t={t}: {sp.simplify(lhs-rhs)==0}")

print("\n=== recursion num_{t+2} - num_t  =?=  (find the clean form) ===")
for t in range(0,5):
    diff=sp.expand(num(t+2)-num(t))
    # guess: num_{t+2}-num_t = 4(t+3) xi_{t+2} + (t+2)^2*2*... ; fit against theta-moments
    m=t+2
    # candidate: 4(t+3) xi_{t+2}? 
    cand=sp.expand(4*(t+3)*thmom(t+2,1))
    print(f" t={t}: num diff - 4(t+3)xi_(t+2) = {sp.simplify(diff-cand)}")

print("\n=== so V(t) via V(t) = M^2 - Q_t/den_t,  Q_t = sum (M^2-D^2)^2 w^{D^2/2} >=0 ===")
for t in range(1,5):
    M=t+2; Q=sp.expand(sum(((M**2-(t-2*p)**2)**2)*w**sp.Rational((t-2*p)**2,2) for p in range(t+1)))
    check=sp.simplify(V(t)-(M**2 - sp.cancel(Q/den(t))))
    print(f" t={t}: V = M^2 - Q/den  holds: {check==0}")
