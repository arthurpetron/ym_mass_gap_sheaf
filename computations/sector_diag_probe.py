"""MEASUREMENT MODULE for work_plan §17h supplement: the two regimes of
the middle-regime rate loss.

Runs, in exact arithmetic:

  (a) the CONDITIONAL diagonal bound under the measured-but-unproved
      lemma  0 <= N(n,n,sigma,a,a) <= 1  (the multiplicity-free vertex
      statement; the standing coupled-simplification audit binds it to
      the SU(2) worst-case reduction and the Z_t(G) <= Z_t(SU(2))
      character-tail input, so it is NOT asserted here) — the incumbent
      4-cycle transfer re-run with LINEAR dim weights, worth 10-13
      orders against the crude |N| <= prod(dim) domination;

  (b) the family-adaptation comparison det_S(cap<=2)/det_S(cap<=1),
      which shows the cap<=1 family SATURATING at moderate coupling and
      STARVING as s -> 1.

Nothing here is a certified claim: (a) is conditional and (b) is a
measurement.  The certified statements live in
computations/sector_sos.py (the sign) and computations/sector_floor.py
(the unconditional floor).

Run:  python -m computations.sector_diag_probe
"""
import sys, math, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as F
from computations.su2_minf_windows import DomTransfer, cas4, dim, triad
from computations.sector_sos import sector_kernels, assemble, det_poly, pev
from computations.sector_floor import lam_min, diagonal_upper

def s1_tail(K,s):
    r=2*s**(2*K+3); assert r<1
    return F(K+2)*s**cas4(K+1)/(1-r)
def s1(K,s):
    return sum((F(k+1)*s**cas4(k) for k in range(K+1)),F(0))+s1_tail(K,s)
def s2q_tail(K,s):
    r=4*s**(2*(2*K+3)); assert r<1
    return F((K+2)**2)*s**(2*cas4(K+1))/(1-r)
def s2q(K,s):
    return sum((F((k+1)**2)*s**(2*cas4(k)) for k in range(K+1)),F(0))+s2q_tail(K,s)

class DiagTransfer(DomTransfer):
    """Same 4-cycle transfer, LINEAR dim weights: valid under N_diag <= 1."""
    def node_w(self, st):
        a,b,q=st; s=self.s
        return (F(dim(a))*s**cas4(a) * F(dim(b))*s**cas4(b)
                * F(dim(q)**2)*s**(2*cas4(q)))
    def edge_w(self, st1, st2, wcap, parity):
        a1,b1,_=st1; a2,b2,_=st2; tot=F(0)
        for w in range(parity,wcap+1,2):
            if triad(a1,a2,w) and triad(b1,b2,w):
                tot+=F(dim(w))*self.s**cas4(w)
        return tot
    def lam_slop(self):
        s=self.s; lam=self.lam
        S1=s1(lam,s); S2=s2q(lam,s)
        node_sum=S1*S1*S2
        node_tail=2*s1_tail(lam,s)*S1*S2 + S1*S1*s2q_tail(lam,s)
        w_all=S1; w_tail=s1_tail(lam,s)
        slop=(4*node_tail*node_sum**3*w_all**4 + 4*w_tail*w_all**3*node_sum**4)
        return slop          # no d_n d_m prefactor: |N_diag| <= 1

def lam_min_diag(s,cap=400):
    lam=1
    while lam<=cap:
        try:
            s1_tail(lam,s); s2q_tail(lam,s); return lam
        except AssertionError: lam+=1
    raise ValueError

T=assemble(sector_kernels(1,2)); det=det_poly(T)
for s in [F(4,5),F(9,10),F(24,25)]:
    t0=time.time()
    lam=lam_min_diag(s)+2
    hi={}
    for n in (0,1):
        dt=DiagTransfer(n,n,s,lam)
        hi[n]=dt.dominated_trace(lam)/F(dim(n)*dim(n))+dt.lam_slop()
    dS=pev(det,s)
    floor=dS/(hi[0]*hi[1])
    ref=dS/(pev(T[(0,0)],s)*pev(T[(1,1)],s))
    old_lam=lam_min(s)+2
    old=dS/(diagonal_upper(0,s,old_lam)*diagonal_upper(1,s,old_lam))
    print(f's={s} lam={lam}  T00_hi={float(hi[0]):.4e} T11_hi={float(hi[1]):.4e}')
    print(f'   CONDITIONAL floor (N_diag<=1) = {float(floor):.4e}   '
          f'vs certified-crude {float(old):.4e}  -> gain {float(floor/old):.3e}x')
    print(f'   reference ratio {float(ref):.4e}; remaining slack {float(ref/floor):.4e}x  [{time.time()-t0:.1f}s]', flush=True)
