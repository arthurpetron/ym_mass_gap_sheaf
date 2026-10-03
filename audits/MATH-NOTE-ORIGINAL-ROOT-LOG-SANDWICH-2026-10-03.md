# Original root/log comparison: a finite constructive proof target

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN.

This note records a mathematical argument whose finite COMPONENTS are now
checked; the complete sandwich and operator identification are NOT proved.
It compares two EXISTING original-carrier maps and supplies no changing-family
signed estimate or physical calibration. Component evidence:
`audits/AUDIT-ORIGINAL-ROOT-LOG-PRODUCERS-2026-10-03.md`.

## Exact finite scalar target

For integers N,M>=1 and rational 0<=u<=1 put

    h=1-u, D=1-u^N,
    L_M(x)=sum_(k=1..M) (1-x)^k/k,
    p_M(x)=x*L_M(x), Q_N(u)=N*u^N*(1-u).

The target is the uniform finite sandwich

    Q_N(u)-1/(M+1) <= p_M(u^N) <= Q_N(u)+1/(N+1).

The endpoint u=0 is included. No inverse spectral floor is needed.

## Positive finite primitives, rather than a spectral theorem

Set S(h)=N*L_(N*M)(u)-L_M(u^N). Its formal derivative satisfies

    u*S'(h)=N*(D^M-h^(N*M)).

This is not a division by a possibly zero u: factor

    D-h^N=sum_(j=1..N-1) binom(N,j)*u^j*h^(N-j),
    D^M-h^(N*M)=(D-h^N)*sum_(i=0..M-1) D^(M-1-i)*h^(N*i).

Every displayed term of the first factor contains u. Cancelling that
polynomial factor gives S' an explicit nonnegative u/h-monomial expansion,
including at u=0. Since S(0)=0, a finite positive primitive proves S>=0.

For F(h)=D^(M+1)/(M+1)-u^N*S(h), the second exact identity is

    F'(h)=N*u^(N-1)*(S(h)+h^(N*M)), F(0)=0.

The SAME primitive construction would prove F>=0. Thus

    0<=u^N*S(h)<=D^(M+1)/(M+1)<=1/(M+1).

The remaining root-series tail is finite. Its coefficients 1/k, k>=2,
are at most 1/2; the finite geometric sum gives

    0<=N*u^N*(L_(N*M)(u)-h)<=(N/2)*u^(N-1)*h^2.

The binomial expansion of (u+h)^(N+1)=1 retains the nonnegative term
binom(N+1,2)*u^(N-1)*h^2, so the last bound is <=1/(N+1).
These two bounds give the target sandwich.

One explicit primitive of u^a*h^b is

    I_(a,b)(h)=sum_(j=0..a) c_j*u^(a-j)*h^(b+j+1),
    c_0=1/(b+1), c_(j+1)=c_j*(a-j)/(b+j+2).

Its coefficients are nonnegative and I(0)=0. Formal differentiation
telescopes to u^a*h^b: successive terms cancel by the recurrence, and
the last negative term has factor a-j=0. This is finite rational data;
no real integration, mean-value theorem, witness choice or oracle is needed.
The generic primitive IS NOW kernel-checked in
`lean/YMGap/Constructive/QPolyPositivePrimitive.lean:158`,
`primitive_derivative`, with actual coefficient data, endpoint positivity
and zero initial value. Its :320, `derivative_initial_unique`, pins any
matching derivative/initial-value polynomial to the computed one.
The ORIGINAL S/F identities and the sandwich are NOT yet kernel-checked.

### A binomial-free first factor (now checked)

The shorter finite telescope

    1-u^N-h^N=u*h*sum_(k=0..N-2)(u^k+h^k)

is now proved at `lean/YMGap/Continuum/RootLogFiniteTail.lean:100`,
`complementary_power_defect`, with its computed nonnegative row and empty
N=1 case. Thus the FIRST factor of the proposed S' expansion needs no
binomial middle row. With P_N=sum_(k=0..N-2)(u^k+h^k), the shorter target is

    S'=N*h*P_N*sum_(i=0..M-1)D^(M-1-i)*h^(N*i).

Replacing D by h*sum_(j=0..N-1)u^j exposes a finite nonnegative u/h row.
The ORIGINAL S coefficient identity, termwise positive primitive join,
F identity and original-root transport are still NOT checked here.
Independent Sol review confirmed this simplification; review is not proof.

## Consumer on the SAME existing completion

Use N=2^depth and u the literal original positive root R_depth.
The following existing declarations have prefix `lean/YMGap/Continuum/`:

- `BF4WilsonAllNomeDyadicDerivative.lean:58`, `differenceQuotient`, is
  N*(I-R_depth)*T(1); :260, `derivative_bound`, controls its limit.
- `BF4WilsonAllNomeLogPartial.lean:114`, `logPartial`, is p_M(T(1)).
- `BF4WilsonAllNomeDyadicEnergy.lean:170`, `full_mesh_time`, pins
  R_depth^N to the ORIGINAL T(1).
- `BF4WilsonAllNomeDyadicDefectDecay.lean:181`, `moment_nonnegative`,
  supplies positive original root/defect monomials.
- `BernsteinRationalPositiveRow.lean:83`, `unnormalizedRow_reconstruction`,
  and :264, `unnormalizedRow_nonnegative`, supply finite positive rows.
- `BF4WilsonAllNomeLogSeries.lean:180`, `regularizedLog_approximation`,
  controls the other existing limit.

After the finite scalar proof, its actual positive-polynomial operator lift
must also be proved, not assumed. The resulting norm comparison and existing
moduli would identify `derivativeAction` with `regularizedLog` on this SAME
carrier, preserving its boundary kernel. Neither equality is claimed here.

### Shorter sufficient original-operator route (checked components)

The sharp scalar binomial ceiling is NOT required to identify the limits.
For depth=d+2 and N=2^(d+2),
`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogTail.lean:76`,
`root_quadratic_tail_bound`, proves the ACTUAL positive-moment tail is at
most (8/N)*B(x,x), where 8/N=2*half^d is explicit rational data.
`RootLogFiniteTail.lean:57`, `partial_retained_tail`, proves the scalar
finite tail used above (same directory).

With the STILL-MISSING ORIGINAL S/F positive expansions and root transport,
the two-sided form error 8/N+invSucc(M) is sufficient.
`BF4WilsonAllNomeSymmetricFormNorm.lean:127`, `symmetric_form_norm_bound`,
now proves those diagonal bounds yield the squared norm error by rational
polarization on the SAME completion. It does not construct the diagonal
bounds for the actual root/log difference. No legacy functional calculus,
arbitrary real inverse, spectral theorem or boundary injectivity is needed.

## Exploration boundary

Lightweight exact-rational exploration checked both derivative polynomial
identities for N,M=1..8 (128 identities), and the sandwich and retained
remainder on 1,088 rational interval samples, including both endpoints.
These are debugging checks, NOT a Lean certificate or a proof for all N,M.
Independent Sol mathematical review confirmed the finite argument and the
shorter original moment route; reviews do not replace kernel verification.
The root/log producer is an independent
structural target, not a replacement for the original action-dependent
relative estimate, continuum survival, calibration, QFT axioms or every-group
construction.
