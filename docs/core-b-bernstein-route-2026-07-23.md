# Core-B physical Bernstein route (2026-07-23)

## Result of the new exact scout

Write

\[
u=4w^2.
\]

On the physical interval \(0\le w\le w_H=1/2\), this is exactly
\(0\le u\le1\), and \(w_H^2=1/4\).  For every canonical cell

\[
(s,r)=(t+1,n-1-t),\qquad 0\le t<n,
\]

`computations/core_b_bernstein_scout.py` expands the actual eleven-family
quotient `boundaryResidualSquareGapQuotient wH w s r` from the bounded
monomial normal form.  It does not use the transcribed low-gap mass
polynomials.

For every cell through \(n=8\), exact rational power-to-Bernstein conversion
gives

\[
Q_{n,t}(u)=u^{L_{n,t}}
  \sum_{j=0}^{D_{n,t}} b_{n,t,j}
  {D_{n,t}\choose j}u^j(1-u)^{D_{n,t}-j},
\]

with every \(b_{n,t,j}>0\).  Reconstruction is checked exactly.  Thus every
tested cell is nonnegative on the whole physical interval before diagonal
summation.  The cumulative quotient is consequently positive on the same
grid as well.

The same cleared integer row has a second, direct implementation: it sums the
degree-elevated contribution of each actual bounded atom tuple without first
forming a symbolic polynomial.  This direct row agrees exactly with the
independent SymPy conversion through \(n=8\), and its strictly positive
falsification grid extends through every cell of \(n=15\).  The regression
suite retains the extended direct grid through \(n=12\) to control runtime.

This is stronger evidence than point sampling, and structurally stronger
than the current adverse-mass budget: it suggests that Core B may close
termwise on the canonical diagonal.

## Exact degree geometry

The scout exposes simple all-index degree formulas already supported by the
kernel-checked centered-shell arithmetic.

The common top \(u\)-degree is

\[
H_n=(n+2)(n+4).
\]

The lowest power is the canonical content divided by two, plus the exact
early-cell content shift:

- if \(n=2k\),
  \[
  L_{n,t}=2(k+1)(k+3)+2d^2,
  \qquad d=\max(k-(t+1),0);
  \]
- if \(n=2k+1\),
  \[
  L_{n,t}=2k^2+10k+11+2d(d+1),
  \qquad d=\max(k-(t+1),0).
  \]

Therefore \(D_{n,t}=H_n-L_{n,t}\).  At and after the center this becomes

\[
D_{2k,t}=2(k+1)^2,\qquad
D_{2k+1,t}=2(k+1)(k+2).
\]

The exact endpoint/physical-square denominators are cleared uniformly by
\(4^{2H_n}\).  After also passing from normalized to unnormalized Bernstein
coordinates, the integer carrier is

\[
B_{n,t,j}
  =4^{2H_n}{D_{n,t}\choose j}b_{n,t,j}.
\]

Every \(B_{n,t,j}\) tested by independent reconstruction through \(n=8\), and
by the direct actual-atom formula through \(n=15\), is a strictly positive
integer.
This is the natural Lean target: no rational division remains in the sign
statement.

## Why this can bypass the tail budget

The atom-debt route separates favorable and adverse oriented homogeneous
chains and then pays the adverse mass with a canonical reserve plus a
Gaussian/geometric tail.  That remains a valid route, and its low-gap and
tail infrastructure is reusable.

The Bernstein route instead collects the complete cell quotient first.
Degree elevation turns every monomial into one common positive basis on
\([0,1]\).  Favorable and adverse atoms cancel at the integer coefficient
level.  If

\[
\forall n,t,j,\quad 0\le B_{n,t,j},
\]

then the existing Bernstein reconstruction and nonnegative-basis machinery
proves every canonical cell quotient nonnegative directly.  Summing the cells
inhabits the row-one-origin quotient certificate without a separate
all-gap numerical budget.

The routes are complementary.  The actual bounded selector/classifier now
being formalized should be shared: its atom coefficient, exponent, and
orientation data feed both the gap ledger and \(B_{n,t,j}\).

## Lean theorem order

1. **Actual selector seam.** Define the bounded canonical tuple
   \((t,i,j,p,q,u,v)\), its two actual atoms, coefficient product, exponent
   halves, orientation, and endpoint gap.  Prove the first complete
   specialization (odd gap \(2\)).
2. **Degree bounds.** Prove the formulas for \(H_n,L_{n,t},D_{n,t}\) from
   `CoreBAtomwiseGapBounds` and `CoreBCanonicalSquareShell`.
3. **Integer Bernstein row.** Define \(B_{n,t,j}\) as the finite signed sum of
   elevated monomial coefficients, with the factor \(4^{2H_n-E}\) attached
   to an atom term of total squared degree \(E\).
4. **Reconstruction.** Reuse
   `BernsteinMonomialReconstruction.elevatedMonoEval_eqv_pow` and the finite
   sum congruence lemmas to prove that the actual cell quotient equals
   \(u^{L_{n,t}}\) times the Bernstein evaluation, up to the positive common
   clearing factor.
5. **Coefficient recurrence.** Prove the Pascal-unimodal adjacent-step
   recurrence described below.  It reduces the interior coefficient array
   to two boundary-row sign theorems.
6. **Physical consumer.** Convert coefficient nonnegativity to canonical-cell
   quotient nonnegativity, sum over \(t<n\), construct
   `PhysicalRowOneOriginSquareGapQuotientNonnegative`, and apply the already
   closed Core-B consumer.

Step 4's generic finite-sum algebra is now closed:
`Continuum/BernsteinSignedMonomialReconstruction.lean` defines the computable
row compiler

`finiteSignedMonomialBernsteinRow D weight exponent N`

and proves that its single common degree-\(D\) Bernstein evaluation is exactly
the first \(N\) signed monomials whenever every exponent is at most \(D\).
Integer signs are unrestricted.  The theorem is constructive and depends
only on `[propext, Quot.sound]`.  The remaining reconstruction work is no
longer generic basis algebra: it is the Core-B-specific enumeration of the
actual oriented-chain monomials and identification of their compiled row with
\(B_{n,t,j}\).

That Core-B-specific compilation seam is now closed as well.
`Continuum/CoreBActualBernsteinRow.lean` constructs
`actualCanonicalCellBernsteinRow n t` directly from the eleven actual bounded
families, including the actual coefficient products, orientation signs, chain
lengths, and physical-square exponents.  Its common degree is a computable
maximum over the selector ledger, rather than a conjectured closed formula.
The module proves that denominator-clearing subtraction cannot truncate and
that the full row reconstructs the exact eleven-family signed monomial
ledger.

The adapter
`physicalCanonicalCellBernsteinCertificateOfActualRow` reduces a physical
cell certificate to precisely two Core-B-specific inputs:

1. coefficientwise nonnegativity of the computed actual row; and
2. the rational scaling identity identifying the cleared physical quotient
   with the actual ledger evaluated at \(u=4w^2\).

Thus selector enumeration, common-degree fitting, finite signed
reconstruction, and certificate packaging are no longer open.

## Pascal-unimodal step recurrence

There is one exact basis identity and one strong all-index conjecture.
For any unnormalised degree-\(D\) Bernstein row \(R\), its degree
\(D+m\) elevation is exactly

\[
  (E_mR)_j=\sum_q {m\choose q}R_{j-q}.
\]

This is simply multiplication of the reconstructed polynomial by
\((u+(1-u))^m=1\), so unlike the sign pattern below it is an all-index
algebraic identity.

Put \(s=t+1\) and \(d=\max(k-s,0)\).  The degree formulas imply the exact
adjacent elevation sizes:

- for \(n=2k\), \(D_{n,t}=2(k+1)^2-2d^2\), and an early transition with
  \(d>0\) has \(D_{n,t+1}-D_{n,t}=4d-2\);
- for \(n=2k+1\),
  \(D_{n,t}=2(k+1)(k+2)-2d(d+1)\), and an early transition with \(d>0\)
  has \(D_{n,t+1}-D_{n,t}=4d\);
- all later transitions have elevation size zero.

The direct actual-atom integer rows satisfy the following strict sign pattern
on every tested coefficient through every cell of \(n=15\):

\[
\begin{array}{ll}
n=2k:
& B_{n,t+1}-E_\delta B_{n,t}>0 \quad(t<k-1),\\
& E_\delta B_{n,t}-B_{n,t+1}>0 \quad(t\ge k-1);\\[2mm]
n=2k+1:
& B_{n,t+1}-E_\delta B_{n,t}>0 \quad(t<k),\\
& E_\delta B_{n,t}-B_{n,t+1}>0 \quad(t\ge k).
\end{array}
\]

Thus the rows are coefficientwise Pascal-unimodal in the cell step, with
peak \(t=k-1\) for even length and \(t=k\) for odd length.  The test suite
retains an exact regression grid through \(n=10\).

If this signed adjacent-difference statement is proved in Lean, positivity
of all cells reduces to positivity of the two outer boundary rows:
degree elevation preserves coefficientwise nonnegativity, the increasing
half propagates from \(t=0\), and the decreasing half propagates backward
from \(t=n-1\).  This is currently the sharpest induction target.

Several simpler candidate recurrences were falsified exactly:

- the signed adjacent differences have mixed power-basis coefficients, so
  ordinary monomial positivity does not prove the pattern;
- they are not scalar multiples or Pascal elevations of the
  \((n-2,t-1)\) row;
- the two outer rows are not scalar or reversal mates;
- after the natural \(4^{2(H_{n+1}-H_n)}\) rescaling and degree elevation,
  neither outer row is equal to its successor in \(n\).  On the tested grid
  both instead decrease coefficientwise, which does not by itself provide a
  forward positivity induction.

Only the degree formulas and the generic elevation identity in this section
are proved identities.  Pascal unimodality is exact finite evidence through
\(n=15\), not an all-index theorem.

## Claim boundary

The grid through \(n=8\) is exact finite evidence only.  It does not prove the
all-index coefficient theorem, does not inhabit the physical quotient
certificate, and does not close Core B.  Its significance is that it replaces
an apparently analytic tail problem by a concrete integer Pascal/Bernstein
sign problem tied directly to the actual quotient.
