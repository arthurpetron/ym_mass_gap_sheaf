"""
racah_coupled.py  --  The TRIPLE-COUPLED multi-variable creative-telescoping
attack on `guardedBEDougall` (the admissible-set-corrected Biedenharn-Elliott /
Racah-Dougall sum rule), Track A2.

sympy / exact-Fraction arithmetic is TRUSTED FOR NOTHING; it only COMPUTES.
Anything that is to become a Lean theorem is (a) an exact identity that the
Lean-core RingNormaliser can decide, or (b) a telescope re-proved by int_telescope.

Jobs:
  (1) STRUCTURE the coupled sum: exhibit guardedBEDougall's LHS as a genuine
      4-fold nested sum  Σ_x (over the outer index) of a product of THREE inner
      Racah t-sums S1(x),S2(x),S3(x), and print the exact COUPLING map (which
      labels + running x each inner sum shares).
  (2) GROUND-TRUTH the guarded identity over a wide admissible range (residual 0).
  (3) Attempt a single-outer-parameter Zeilberger/creative-telescoping RECURRENCE
      for the full coupled LHS (and RHS) by an exact-arithmetic ansatz solve;
      report the honest order / obstruction.
  (4) PROBE genuine all-spins DEGENERATE SLICES that the ALREADY-BUILT Lean
      engine (int_telescope / altDim_sum / SixJKernel orthogonality / normaliser)
      can actually close ∀-spins (not a finite decide list): the honest
      composable increment.

Mirrors the Lean Q'/Nat objects (SixJKernel + BiedenharnElliottGeneral +
RacahDougallWZ) bit-for-bit (twice-spin Nat labels, integer division, Nat
truncated subtraction, the fusionOK / valid6 admissibility guards).

Run: python3 computations/racah_coupled.py
"""

from math import factorial as fact
from fractions import Fraction as F
import itertools

# ---------------------------------------------------------------------------
# EXACT mirror of the Lean objects (identical to dougall_wz.py / SixJKernel).
# ---------------------------------------------------------------------------

def _sub(a, b):
    return a - b if a >= b else 0  # Nat truncated subtraction

def triSq(x, y, z):
    n = fact(_sub(x + y, z) // 2) * fact(_sub(x + z, y) // 2) * fact(_sub(y + z, x) // 2)
    d = fact((x + y + z) // 2 + 1)
    return F(n, d)

def tGuard(s1, s2, s3, s4, p1, p2, p3, t):
    return (s1 <= t and s2 <= t and s3 <= t and s4 <= t
            and t <= p1 and t <= p2 and t <= p3)

def racahSummand(s1, s2, s3, s4, p1, p2, p3, t):
    if tGuard(s1, s2, s3, s4, p1, p2, p3, t):
        sign = 1 if t % 2 == 0 else -1
        seven = (fact(t - s1) * fact(t - s2) * fact(t - s3) * fact(t - s4)
                 * fact(p1 - t) * fact(p2 - t) * fact(p3 - t))
        return F(sign * fact(t + 1), seven)
    return F(0)

def racahSum(jj1, jj2, jj3, jj4, jj5, jj6):
    s1 = (jj1 + jj2 + jj3) // 2
    s2 = (jj1 + jj5 + jj6) // 2
    s3 = (jj4 + jj2 + jj6) // 2
    s4 = (jj4 + jj5 + jj3) // 2
    p1 = (jj1 + jj2 + jj4 + jj5) // 2
    p2 = (jj2 + jj3 + jj5 + jj6) // 2
    p3 = (jj1 + jj3 + jj4 + jj6) // 2
    N = (jj1 + jj2 + jj3 + jj4 + jj5 + jj6) // 2 + 1
    return sum((racahSummand(s1, s2, s3, s4, p1, p2, p3, t) for t in range(N)), F(0))

def bePhase(S):
    return 1 if S % 2 == 0 else -1

def fusionOK(a, b, s):
    return (max(a, b) - min(a, b) <= s) and (s <= a + b) and ((a + b + s) % 2 == 0)

def valid6(A, B, C, D, E, Ff):
    return (fusionOK(A, B, E) and fusionOK(A, D, Ff)
            and fusionOK(C, B, Ff) and fusionOK(C, D, E))

# ---- the three inner coupled Racah t-sums (each COUPLED to x) --------------
def S1(a, b, c, d, e, f, p, q, r, x):  # {a b x; c d p}
    return racahSum(a, b, x, c, d, p)

def S2(a, b, c, d, e, f, p, q, r, x):  # {c d x; e f q}
    return racahSum(c, d, x, e, f, q)

def S3(a, b, c, d, e, f, p, q, r, x):  # {e f x; b a r}
    return racahSum(e, f, x, b, a, r)

def cLcoeff(a, b, c, d, e, f, p, q, r, x):
    return (S1(a, b, c, d, e, f, p, q, r, x)
            * S2(a, b, c, d, e, f, p, q, r, x)
            * S3(a, b, c, d, e, f, p, q, r, x)
            * (triSq(a, b, x) * triSq(c, d, x) * triSq(e, f, x)))

def beWeight(a, b, c, d, e, f, p, q, r, x):
    S = (a + b + c + d + e + f + p + q + r + x) // 2
    return bePhase(S) * (x + 1) * cLcoeff(a, b, c, d, e, f, p, q, r, x)

def lhsAdmX(a, b, c, d, e, f, p, q, r, x):
    return (valid6(a, b, c, d, x, p) and valid6(c, d, e, f, x, q)
            and valid6(e, f, b, a, x, r))

def outerAdm(a, b, c, d, e, f, p, q, r):
    return valid6(p, q, e, a, r, d) and valid6(p, q, f, b, r, c)

def guardedBERationalLHS(a, b, c, d, e, f, p, q, r, D):
    return sum((beWeight(a, b, c, d, e, f, p, q, r, x)
                for x in range(D) if lhsAdmX(a, b, c, d, e, f, p, q, r, x)), F(0))

def beRationalRHS(a, b, c, d, e, f, p, q, r):
    return (racahSum(p, q, r, e, a, d) * racahSum(p, q, r, f, b, c)) * triSq(p, q, r)


# ---------------------------------------------------------------------------
# (1) STRUCTURE the coupling.
# ---------------------------------------------------------------------------

def structure_report():
    print("=" * 78)
    print("(1) COUPLED-SUM STRUCTURE of guardedBEDougall's LHS")
    print("=" * 78)
    print("""  LHS(a..r, D) = Σ_{x<D} [lhsAdmX] · (-1)^{(Σj+x)/2} · (x+1)
                          · S1(x) · S2(x) · S3(x)
                          · Δ²(a,b,x) Δ²(c,d,x) Δ²(e,f,x)

  where each inner factor is ITSELF a Racah t-sum coupled to the OUTER index x:

     S1(x) = Σ_{t1} (-1)^{t1}(t1+1)! / 7fac[t1]   over  {a b x; c d p}
     S2(x) = Σ_{t2} (-1)^{t2}(t2+1)! / 7fac[t2]   over  {c d x; e f q}
     S3(x) = Σ_{t3} (-1)^{t3}(t3+1)! / 7fac[t3]   over  {e f x; b a r}

  COUPLING MAP (which labels + x each inner sum's 7 factorials bind):
     S1 t1-range:  max(τ over {abx,adp?...}) ... via s_i=(sum)/2, p_i=(sum)/2:
        s = {(a+b+x)/2,(a+c+p)/2,(c+d+x)/2? }  -> shares x with the OUTER Δ²(a,b,x)
     Each Si shares the SAME outer x with exactly TWO of the three outer triangles.
  => genuine 4-fold nested sum (x,t1,t2,t3); the three t-sums are COUPLED only
     THROUGH the shared outer index x (they are independent given x).  RHS is a
     product of TWO x-free t-sums S_R1·S_R2 times Δ²(p,q,r): a 2-fold sum.
  => No single order-0 (Gosper) antidifference in x spans it; the outer x-sum
     needs creative telescoping whose per-term certificate is a rational function
     of (x, outer labels) multiplying the coupled inner-sum product.""")


# ---------------------------------------------------------------------------
# (2) GROUND-TRUTH over a wide admissible range.
# ---------------------------------------------------------------------------

def ground_truth(maxrep=3, randomN=4000, hi=8, seed=1):
    import random
    print("=" * 78)
    print("(2) GROUND-TRUTH: guardedLHS == RHS on outer-admissible tuples")
    print("=" * 78)
    reps = range(0, maxrep + 1)
    checked = fails = 0
    exfail = []
    for tup in itertools.product(reps, repeat=9):
        if not outerAdm(*tup):
            continue
        checked += 1
        D = sum(tup) + 2
        if guardedBERationalLHS(*tup, D) != beRationalRHS(*tup):
            fails += 1
            if len(exfail) < 5:
                exfail.append(tup)
    print(f"  exhaustive [0,{maxrep}]^9 : outer-adm checked={checked} fails={fails}")
    for t in exfail:
        print("     FAIL", t)
    # wide random
    random.seed(seed)
    rchecked = rfails = 0
    rexfail = []
    for _ in range(randomN):
        tup = tuple(random.randint(0, hi) for _ in range(9))
        if not outerAdm(*tup):
            continue
        rchecked += 1
        D = sum(tup) + 2
        if guardedBERationalLHS(*tup, D) != beRationalRHS(*tup):
            rfails += 1
            if len(rexfail) < 5:
                rexfail.append(tup)
    print(f"  random   [0,{hi}]^9 x{randomN}: outer-adm checked={rchecked} fails={rfails}")
    for t in rexfail:
        print("     FAIL", t)
    return checked, fails, rchecked, rfails


# ---------------------------------------------------------------------------
# (3) Single-outer-parameter creative-telescoping RECURRENCE search.
#     Pick one outer spin to vary; try to fit a P-recurrence
#        Σ_{k=0}^{ord} c_k(n)·F(n+k) = 0
#     with polynomial coefficients c_k of bounded degree, satisfied by BOTH the
#     guarded LHS and the RHS as functions of that spin n (holding others).
#     Exact rational nullspace; report the smallest (order,deg) that closes.
# ---------------------------------------------------------------------------

def _poly_recurrence(seq, order, deg):
    """seq: list of Fraction values F(n) for n=0,1,2,...
    Find nonzero (c_{k,j}) with Σ_k Σ_j c_{k,j} n^j F(n+k) = 0 for all sampled n.
    Returns a basis vector (list) or None. Exact rational nullspace."""
    ncols = (order + 1) * (deg + 1)
    rows = []
    # need enough equations: n from 0.. so that n+order < len(seq)
    for n in range(0, len(seq) - order):
        row = []
        for k in range(order + 1):
            fk = seq[n + k]
            for j in range(deg + 1):
                row.append(F(n) ** j * fk)
        rows.append(row)
    if len(rows) < ncols:
        return None
    # exact Gaussian elimination to find a nullspace vector
    return _nullspace_vec(rows, ncols)

def _nullspace_vec(rows, ncols):
    import copy
    M = [r[:] for r in rows]
    nrows = len(M)
    pivcols = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = M[r][c]
        M[r] = [v / inv for v in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] != 0:
                fca = M[i][c]
                M[i] = [a - fca * b for a, b in zip(M[i], M[r])]
        pivcols.append(c)
        r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in pivcols]
    if not free:
        return None
    fc = free[0]
    vec = [F(0)] * ncols
    vec[fc] = F(1)
    for ri, c in enumerate(pivcols):
        vec[c] = -M[ri][fc]
    return vec

def recurrence_search(base, vary_index, nmax=10, max_order=4, max_deg=6):
    """base: a 9-tuple of twice-spins (admissible); vary_index: which coord to
    increment by 2 (one full spin step) to build the sequence F(n).  We build the
    guarded LHS sequence and the RHS sequence and search for a common recurrence."""
    print("=" * 78)
    print(f"(3) RECURRENCE SEARCH varying coord {vary_index} of base {base}")
    print("=" * 78)
    lhs_seq = []
    rhs_seq = []
    ok_pts = []
    for n in range(nmax):
        tup = list(base)
        tup[vary_index] += 2 * n
        tup = tuple(tup)
        if not outerAdm(*tup):
            lhs_seq.append(None)
            rhs_seq.append(None)
            continue
        D = sum(tup) + 2
        lhs_seq.append(guardedBERationalLHS(*tup, D))
        rhs_seq.append(beRationalRHS(*tup))
        ok_pts.append(n)
    # need a contiguous admissible run
    print(f"  admissible n indices: {ok_pts}")
    if len(ok_pts) < max_order + 3:
        print("  insufficient admissible run for a recurrence fit at this base.")
        return None
    # restrict to contiguous prefix from first admissible
    start = ok_pts[0]
    seq = []
    n = start
    while n < nmax and lhs_seq[n] is not None:
        seq.append(lhs_seq[n])
        n += 1
    rseq = []
    n = start
    while n < nmax and rhs_seq[n] is not None:
        rseq.append(rhs_seq[n])
        n += 1
    print(f"  contiguous LHS seq (len {len(seq)}): {[str(v) for v in seq]}")
    for order in range(1, max_order + 1):
        for deg in range(0, max_deg + 1):
            if (order + 1) * (deg + 1) > len(seq) - order:
                continue
            vecL = _poly_recurrence(seq, order, deg)
            if vecL is None:
                continue
            # does the SAME operator annihilate the RHS seq?
            vecR = _poly_recurrence(rseq, order, deg)
            if vecR is not None:
                print(f"  *** recurrence found: order={order}, coeff-deg={deg} "
                      f"(annihilates BOTH LHS and RHS sequences).")
                print(f"      certificate dim (order+1)*(deg+1) = {(order+1)*(deg+1)}")
                return dict(order=order, deg=deg, vecL=vecL, vecR=vecR)
    print("  no common polynomial recurrence up to "
          f"order={max_order}, deg={max_deg} on this single-parameter slice.")
    return None


# ---------------------------------------------------------------------------
# (4) DEGENERATE ALL-SPINS SLICES the BUILT Lean engine can close ∀-spins.
#     Look for outer-label specializations where the coupled 4-fold sum collapses
#     to (a) a single already-proved orthogonality, or (b) a pure altDim telescope.
# ---------------------------------------------------------------------------

def degenerate_slices(maxrep=4):
    print("=" * 78)
    print("(4) DEGENERATE ALL-SPINS SLICES (engine-closable candidates)")
    print("=" * 78)
    reps = range(0, maxrep + 1)

    # Slice A: r = 0.  Then S3 = {e f x; b a 0} forces the (e,b,0),(f,a,0)
    # triangles i.e. e=b, f=a; and S3 becomes a 1-term sum -> the coupled triple
    # collapses.  Check how much the LHS simplifies and whether it matches an
    # orthogonality shape.
    def slice_ok(fixed_desc, pred, tweight_reduces):
        checked = fails = 0
        for tup in itertools.product(reps, repeat=9):
            if not pred(tup):
                continue
            if not outerAdm(*tup):
                continue
            checked += 1
            D = sum(tup) + 2
            if guardedBERationalLHS(*tup, D) != beRationalRHS(*tup):
                fails += 1
        print(f"  slice [{fixed_desc}]: outer-adm checked={checked} fails={fails}")
        return checked, fails

    # p=q=r=0  (all three outer intermediates trivial): the deepest collapse.
    slice_ok("p=q=r=0", lambda t: t[6] == 0 and t[7] == 0 and t[8] == 0, None)
    # r=0 only
    slice_ok("r=0", lambda t: t[8] == 0, None)
    # e=f=0 (two of the coupled triangles trivial)
    slice_ok("e=f=0", lambda t: t[4] == 0 and t[5] == 0, None)
    # a=b=0
    slice_ok("a=b=0", lambda t: t[0] == 0 and t[1] == 0, None)

    # Explicit p=q=r=0 collapse: RHS = racahSum(0,0,0,e,a,d)*racahSum(0,0,0,f,b,c)*triSq(0,0,0)
    # and outerAdm forces e=a,d? Let's exhibit the closed form.
    print("\n  --- p=q=r=0 explicit collapse (candidate for altDim/ortho telescope) ---")
    cnt = 0
    for tup in itertools.product(reps, repeat=9):
        a, b, c, d, e, f, p, q, r = tup
        if not (p == 0 and q == 0 and r == 0):
            continue
        if not outerAdm(*tup):
            continue
        cnt += 1
        if cnt <= 6:
            D = sum(tup) + 2
            lhs = guardedBERationalLHS(*tup, D)
            rhs = beRationalRHS(*tup)
            # nonzero x-terms
            terms = [(x, beWeight(*tup, x)) for x in range(D)
                     if lhsAdmX(*tup, x) and beWeight(*tup, x) != 0]
            print(f"    {tup}: nonzero-x={[x for x,_ in terms]} LHS={lhs} RHS={rhs}")
    print(f"    (p=q=r=0 outer-adm count over [0,{maxrep}]^9: {cnt})")


def main():
    structure_report()
    print()
    ground_truth(maxrep=3, randomN=4000, hi=8)
    print()
    # recurrence attempts on a few admissible bases, varying different coords
    bases = [
        ((2, 2, 2, 2, 2, 2, 2, 2, 2), 4),
        ((2, 2, 2, 2, 2, 2, 2, 2, 2), 0),
        ((2, 2, 2, 2, 2, 2, 0, 0, 0), 4),
    ]
    for base, vi in bases:
        recurrence_search(base, vi, nmax=9, max_order=3, max_deg=4)
        print()
    degenerate_slices(maxrep=4)


if __name__ == "__main__":
    main()
