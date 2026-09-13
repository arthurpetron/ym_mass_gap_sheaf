# JTP closure progress — Wall 2 (differentiated Jacobi-triple-product residual)

Companion to `docs/jtp-convergence-notes.md`.  Records what the Lean module
`lean/YMGap/Continuum/JTPIdentity.lean` closed, the explicit modulus used, and
the honest residual.

## 2026-09-12: finite Jacobi approximants have a strict original-Haar floor

`JacobiShiftedPositiveCoefficients` writes every full factor in t=1+x as

    (1-q^(2k+2)) * [(1-q^(2k+1))^2 + 2*q^(2k+1)*t].

Its product and formal Leibniz derivative therefore have nonnegative
rational coefficient lists, with exact evaluation pins to the existing
Ppart/fullProdDx. The normalized heat approximant is fullProdDx/(2*q).
At t=0 (x=-1), `floor_le_heat_constant` retains the previous strict
floor c(q)=E_q(L(q))^2/16>0 at EVERY N>=1.

`QuaternionHaarUnitScalarSquare` certifies 1+a for the actual ordered
plaquette holonomy (a,b,c,d) using

    2*(1+a) = (1+a)^2 + b^2 + c^2 + d^2

under EVERY original Haar insertion. This uses the proved unit-norm relation,
not a pointwise-box assumption. `QuaternionHaarSquareCertificate` proves
product closure by expanding supported squares; `QPolyHaarPositiveSubstitution`
compiles the nonnegative coefficient lists and retains their constant
coefficient with any certified positive insertion. Consequently
`BF4ExactSlabJacobiHaarFloor.productFloor_le_haar` proves

    original Haar(product over F actual faces of JacobiApprox_N) >= c(q)^F > 0.

The link variables remain shared. The bound is uniform in N>=1 for each
supplied q and finite face list, NOT in coupling, volume or spacing.

Remaining: a coefficient-level pin to WEIGHTED original character polynomials
and explicit Haar-limit passage to the original heat action. JacobiApprox_N
is not the original unweighted heat cutoff. Thus this is a strict finite
integrated floor, not yet an original action-limit floor, non-null full
unit, stationary physical vacuum/transfer/gap or continuum result.
Five focused checks: 51 gates within `{propext, Quot.sound}`, no new holes,
final error/warning free. No full-tree build/audit/guard run.

## 2026-09-12: strict original heat floor, with a constructive finite cutoff

`EulerProductStrictFloor` computes L(q) from an explicit geometric half-budget
and proves `E_q(N)>=E_q(L(q))/2>0` for every N, at every rational 0<q<1.
`ThetaProductStrictFloor.euler_square_le_Ppart` then gives

    Ppart(q,x,N) >= E_q(2N)^2 >= E_q(L(q))^2/4.

The first logarithmic-derivative term gives `S_N(q,x)>=q/2` for N>=1.
`SU2PointwiseHeatStrictFloor.pointwiseHeatCReal_geRat_floor` combines these
bounds with the PROVED DiffJTP and original inverse-nome identity:

    original completed K_q(x) >= c(q) = E_q(L(q))^2/16 > 0.

The estimate is uniform in rational x in [-1,1], endpoints included, NOT
uniform in q approaching one. `finiteCutoff q` is explicitly
`max 1 (derivativeCutoff q (q*c(q)/2))`; every original character prefix
at a later label count is >= c(q)/2. It is not extracted from a geRat proof.

`BF4ExactSlabHeatPointwiseFloor` pins these prefixes to the original face
polynomials with their K+1 convention, and proves their shared-link product
is >= `(c(q)/2)^F` under the explicit scalar-box hypotheses. Passing through
the original Haar functional remains open: the existing positivity theorem
is for polynomial squares. No positive original action limit, physical
stationary vacuum/transfer/gap or continuum closure follows yet.

Four new modules, 30 focused gates within `{propext, Quot.sound}`, current
outputs, final error/warning free. No new sorry, analytic premise, oracle,
canonical frontier change, raised proof limits or full build/audit/guard run.
This supersedes the strict pointwise heat-positivity residue below, not the
original interacting-action/Haar residue.

## 2026-09-12: differentiated JTP proved, original heat nonnegativity obtained

`JacobiDifferentiatedIdentityOnBox.diffJTP` now proves the unchanged named
obligation for every rational 0<q<1 and -1<=x<=1, including both endpoints:

    dSeriesCReal = Rhalf = (1/2) * Theta * S.

The proof does not differentiate an infinite limit or assume a common F.
`FiniteSymmetricChebyshevDerivative.dsum_step_with_boundary` is the finite
Leibniz companion of the original coefficient rule, with both endpoint terms.
`FiniteJacobiDerivativeIdentity.fullProdDx_eq_two_weighted_dPartial`
identifies the EXISTING full finite derivative with twice the dTerm partial
sum carrying the actual normalized Jacobi weights.

`FiniteJacobiDerivativeComparison.shiftedGaussian_le` bounds
`(r+1)^2 q^(r*r) <= D(q) q^r`, with
`D(q)=1+4*JTPIdentity.Cmaj(q)/q`. Gaussian absorption of the weight deficit
then gives the whole derivative comparison:

    abs(fullProdDx_N - 2*dPartial_N) <= C_d(q) q^(2N+1),
    C_d(q) = 2*lossScale(q*q)*D(q)/(1-q).

`derivativeCutoff q epsilon` computes
`powBaseCutoff q (epsilon/(C_d(q)+1))`. The limit equality retains this
modulus in `Rhalf_sub_dSeries_close` and explicitly checks the factor half.
All q-dependence is exposed; uniformity is over x in the stated interval,
not q approaching one. The legacy all-Q totalizer is not needed for this
finite-derivative-comparison route and is not asserted to be inhabited.

The corollary `pointwiseHeatCReal_geRat_zero` applies the EXISTING exact
nome/offset bridge to the original completed SU(2) character series. The
result is nonnegativity, NOT a strictly positive heat/action floor. The
original interacting-action floor and physical vacuum/transfer/gap/continuum
construction remain open. Prior OPEN entries for DiffJTP below are historical
and superseded by this closure; its type is unchanged.

Four new proof modules: 36 focused gates within `{propext, Quot.sound}`,
current `.olean` outputs, final error/warning free. Two documentation-only
dependency modules were refreshed separately: 26 gates pass; `JTPIdentity`
retains two pre-existing unused-variable warnings. No new sorry, analytic premise,
numerical oracle, canonical frontier change, raised proof limits or full
build/audit/guard/progress run.

## 2026-09-12: original product and full theta series limits agree on [-1,1]

`FiniteJacobiSeriesComparison.coefficientError_succ_le_gaussian` uses

    q^((r+1)^2) (q*q)^(N-r) = q^(2N+1) q^(r*r),  r+1<=N,

to absorb the moving coefficient deficit. The central coefficient is
bounded separately. Together with `|T_j(x)|<=1` and a geometric sum, this
gives `Ppart_sub_bareTheta_le`:

    abs(Ppart q x N - bareTheta q x N) <= C(q) q^(2N+1),
    C(q) = (2/(1-q*q)) (1+2/(1-q)),  0<q<1, -1<=x<=1.

The error is for the entire finite polynomial, not merely a coefficient
band. `comparisonCutoff q epsilon` computes
`powBaseCutoff q (epsilon/(C(q)+1))`; `Ppart_sub_bareTheta_close` proves
the tolerance bound for every later N, uniformly over the named interval
in x. C(q) is explicitly q-dependent and unbounded as q approaches one.

`JacobiTripleProductOnBox.bareTheta_eq_one_add_two_chebTTrunc` pins the
normalization, and `thetaProduct_eq_fullThetaSeries` proves

    thetaConvCRealGen = 1 + 2 * chebTConvPt(onBoxPtMajorant)

as `CReal.Equiv`, with the actual approximation comparison and its computed
cutoff. Both limit constructions already existed; their equality is now
proved on the interval with no identity premise or extra analytic input.

Still OPEN: differentiated JTP, with `Rhalf=(1/2)*Theta*S`; domain/endpoint
control for differentiation (the legacy all-Q interfaces are not supplied
by this on-box theorem); heat/action positivity and the physical gap/continuum
target. This is not `DiffJTP`, and does not equate the full product with the
nonconstant half-series alone.

Two focused monitored one-worker 20 GiB checks: 22 gates within
`{propext, Quot.sound}`, current `.olean` outputs, final error/warning free.
No new sorry, named analytic input, numerical oracle, canonical frontier
change, or full build/audit/guard/progress run.

## 2026-09-12: normalized coefficients have a computed convergence modulus

`FiniteJacobiWeightBounds.centeredWeight_eq_segments` proves the exact
finite-product cancellation, for `0<Q<1`, j<=N:

    W(Q,N,j) = product_{k=N-j+1..N} (1-Q^k)
                * product_{k=N+j+1..2N} (1-Q^k).

The empty products are one. `centeredWeight_bounds` proves 0<=W<=1 for
ALL indices (the original out-of-range q-binomial is zero).
`FiniteEulerSegment` supplies the Weierstrass/geometric loss estimates;
`FiniteJacobiWeightConvergence.centeredWeight_abs_loss` proves

    abs(W(Q,N,j)-1) <= 2 Q^(N-j+1)/(1-Q),  j<=N.

`centeredCutoff Q J epsilon` computes
`J + HKConvGen.powBaseCutoff Q (epsilon/(2/(1-Q)+1))`.
`centeredWeight_abs_close` proves abs(W-1)<=epsilon for every later N and
j<=J. The finite band and base are explicit; no convergence uniformly over
all j or all Q is asserted. No infinite-product denominator or Prop-level
existential index is assumed/extracted.

Next: combine the coefficient estimates with Gaussian/Chebyshev tails to
compare the ORIGINAL finite product and bare theta series; then pass to
the correctly half-normalized derivative identity. Neither `DiffJTP` nor
heat/action positivity is closed by the coefficient estimate alone.

Three focused monitored one-worker 20 GiB checks: 25 gates within
`{propext, Quot.sound}`, current `.olean` outputs, final error/warning free.
No new sorry, analytic premise, numerical oracle, canonical frontier change,
or full build/audit/guard/progress run.

## 2026-09-12: finite symmetric Jacobi identity proved

`FiniteJacobiIdentity.factorProd_eq_gaussianPartial` now proves, for every
rational `0<q<1`, rational x and finite N,

    RealTheta.factorProd q x N
      = [2N choose N]_(q*q)
        + 2 sum_{j=1..N} q^(j*j) [2N choose N+j]_(q*q) T_j(x).

`Ppart_eq_finiteJacobi` includes the actual Euler product and identifies
`ThetaConv.Ppart` with the finite series whose j-th Gaussian coefficient is
`q^(j*j) * centeredWeight (q*q) N j`. These are setoid equalities of actual
rational data. Neither identity is a supplied field.

The proof combines `GaussQBinomSymmetricStep.qbin_two_sided_step` (one Pascal
step in each orientation) with `FiniteSymmetricChebyshev.sum_step` (finite
quadratic multiplication with proved-zero endpoints). The concrete bridge
`FiniteJacobiCoefficients.coeff_step` checks center, interior, and outer
coefficients; the central factor two is explicit. No complex variable,
negative natural exponent or assumed coefficient limit is used.

Finite-band weight convergence is now proved above. Still OPEN: the
Gaussian/Chebyshev tail comparison and correctly half-normalized differentiated
limit identity. Finite JTP does not itself inhabit `DiffJTP` or supply heat
or original-action positivity. The older finite-normalization residue below
is superseded only for the symmetric finite identity, not for these limits.

Four focused monitored one-worker 20 GiB checks: 31 gates within
`{propext, Quot.sound}`, current `.olean` outputs, final error/warning free.
No new sorry, named analytic input, numerical oracle or canonical frontier
change. No full build/audit/guard/progress run.

## 2026-09-12: exact finite q-binomial normalization, preparatory increment

`GaussQBinomEulerNormalization.qbin_mul_euler` now derives the exact Euler
formula from the original recursive q-Pascal definition:

    [N choose k]_Q E(Q,k) E(Q,N-k) = E(Q,N),  k <= N,
    E(Q,n) = product_{j=1..n} (1-Q^j).

It is denominator-cleared and valid for every rational Q. The two induction
branches combine using `(1-a)+a*(1-b)=1-a*b`; no vanishing factor is cancelled.
`GaussQBinomEulerQuotient.qbin_eq_euler_quotient` supplies the computable
quotient when `0<Q<1`, using proved finite denominator positivity.
`qbin_complement` gives the complementary-index symmetry and
`euler_square_eq_theta` identifies E(a*a,N) with the ORIGINAL
`RealTheta.eulerProd a N`. `centeredWeight_eq_quotient` gives

    E(Q,N) [2N choose N+j]_Q
      = E(Q,N) E(Q,2N) / (E(Q,N+j) E(Q,N-j)),  j <= N.

These equalities are rational setoid equalities in Lean. They do not yet
prove the symmetric finite Jacobi identity, a quantitative limit of these
weights, or differentiated JTP. In particular, neither product regrouping
nor the one-sided `gauss_qbinom_creal_equiv` supplies the missing identity.
The existing `Rhalf = (1/2)*Theta*S` normalization remains unchanged.

Two focused monitored one-worker 20 GiB checks: 13 gates inside
`{propext, Quot.sound}`, current `.olean` outputs, final error/warning free.
No new sorry, analytic premise, numerical oracle, or canonical frontier
change. No full build/audit/guard/progress run.

## What closed (new, axiom-clean Lean content)

1. **The quadratic–geometric majorant for the `K_t` series.**  The heat-kernel
   Chebyshev series `K_t(x) = a^{-1} Σ_{n≥1} n·a^{n²}·U_{n-1}(x)` has term
   magnitude `|(n+1)·a^{(n+1)²}·U_n(x)| ≤ (n+1)²·a^{(n+1)²}` (via the closed
   Chebyshev bound `|U_n|≤n+1`, `ChebU.absU_le`).  The polynomial factor
   `(n+1)²` is absorbed into the super-geometric Gaussian decay `a^{(n+1)²}` by
   **squaring** the existing multiplicative Bernoulli bound
   `HKConvGen.bernoulli_pow`:

   - `n_pow_le_invG` : `ofNat n · aⁿ ≤ 1/(1−a)`  (linear Bernoulli, divided by `1−a`).
   - `nsq_aa_pow_le` : `(ofNat n · ofNat n)·(a·a)ⁿ ≤ (1/(1−a))²`  (square of the above).
   - `gauss_le_geo`  : `a^{(n+1)²} ≤ a^{(n+1)}·(a·a)ⁿ`  (exponent split
     `(n+1)² = (n+1) + (n+1)·n`, with `(n+1)·n ≥ 2n` ⟹ `a^{(n+1)·n} ≤ (a·a)ⁿ`).
   - `dTermMaj_le`   : the assembled geometric majorant
     **`(ofNat(n+1)·ofNat(n+1))·a^{(n+1)²} ≤ Cmaj a · aⁿ`** at base `a < 1`,
     constant `Cmaj a = (a·(1/(1−a))²)·(1/(a·a))`.

   This is the genuine new mathematics: the repo previously had only the
   *linear* Bernoulli cancellation (`bernoulli_pow`); the squaring gives the
   `n²·rⁿ` polynomial×geometric summability the Gaussian-weight `K_t` series
   needs, with no new quadratic-Bernoulli engine.

2. **`K_t`-side partial sums as a convergent `CReal`** for ALL `a ∈ (0,1)`,
   `−1 ≤ x ≤ 1`:

   - `dTerm a x n = ofNat(n+1)·a^{(n+1)²}·U_n(x)`, `dPartial = finSum (dTerm …)`.
   - `dTerm_le` / `neg_dTerm_le` : the two-sided single-step increment bound
     `|dTerm l| ≤ Cmaj a · aˡ` (via `Q'.mul_le_of_bounds` + `ChebU.absU_le`).
   - `dSeriesCReal` : the partial sums fed to the general-base geometric engine
     `HKConvGen.crealOfGeoIncrementBase` at base `r = a`, constant `Cmaj a`.
     This is the genuine constructive realisation of `K_t·a` (the heat-kernel
     series, modulo the rational prefactor `a^{-1}`), `approx N = dPartial a x N`.

3. **The conditional closure `DiffJTP → K_t ≥ 0`** (`Kt_geRat_zero_of_diff`):
   given the residual identity `(DIFF)`, `K_t = dSeriesCReal ≥ 0` follows by
   feeding `dSeriesCReal`, the product object `R = ϑ₃·S`
   (`Rproduct`, with `R_geRat_zero_gen`-style approximation nonnegativity from
   `Rproduct_approx_nonneg`), and the residual into
   `UTelescope.Kt_nonneg_of_residual`.

## The explicit modulus used

- **`K_t`-side (closed here).**  Geometric base `r = a`, constant `Cmaj a`.
  Cauchy modulus `N(ε) = powBaseCutoff a δ(ε)` with
  `δ(ε) = ε / (Cmaj a · 1/(1−a))`, inherited from `crealOfGeoIncrementBase` /
  `HKConvGen.pow_base_le`.  (The Gaussian decay `a^{(n+1)²}` is *faster* than
  this geometric rate; the geometric rate is what the engine discharges and it
  suffices.)
- **Residual log-derivative modulus (NOT discharged).**  A constructive proof of
  `DiffJTP` would carry the `O((a·a)ᵏ)` log-derivative modulus of
  `jtp-convergence-notes.md §2.3`.

## NEW: the finite-difference Leibniz engine (`DiffProduct.lean`)

A new module `lean/YMGap/Continuum/DiffProduct.lean` closes the **finite
algebraic skeleton** of the differentiation — the genuine pure-`Q'` core that any
constructive product-differentiation engine must rest on:

- `pre f L = ∏_{k<L} f k`, `sufLen g m d = ∏_{m≤k<m+d} g k` — general (no
  positivity) finite products over arbitrary `Q'`-factor sequences.
- `sufLen_append`, `pre_split` — the prefix/suffix split identities.
- `split_core` — the pure ring identity `Pf − Qg ≈ (P−Q)g + P(f−g)`.
- `leib_sum_extend` — appending a factor `g L` extends every suffix product;
  `finSum (leibTerm f g (L+1)) L ≈ (finSum (leibTerm f g L) L)·g L`.
- **`leibniz` (CLOSED, all `L`)** — the discrete product rule / finite-difference
  Leibniz identity:
  `∏_{k<L} f k − ∏_{k<L} g k ≈ Σ_{j<L} (∏_{k<j} f k)·(f j − g j)·(∏_{j<k<L} g k)`,
  by induction on `L`, pure `Q'.eqv` algebra, NO smallness/positivity hypotheses.

With `f k = factor(c_k)(θ+h)`, `g k = factor(c_k)(θ)`, dividing `leibniz` by `h`
is exactly the finite-difference Leibniz expansion of `(∏(θ+h) − ∏(θ))/h` — the
term-by-term product derivative whose `L→∞` then `h→0` limit is the log-derivative
series.  `leibniz` is that interchange's *finite skeleton*; it introduces no new
positivity content.  The remaining analytic step (the uniform double-limit) is
exposed as the named `Prop` `DiffProduct.ProductDerivativeLimit`, and
`JTPIdentity.DiffJTP` is identified with it definitionally
(`DiffJTP_eq_productDerivativeLimit`), with the conditional closure re-exposed as
`Kt_geRat_zero_of_productDerivativeLimit`.

All of `DiffProduct.lean` and the new `JTPIdentity` bridges are axiom-clean
(`[propext]` / `[propext, Quot.sound]`; no `Classical.*`, no `native_decide`, no
`sorry`).

## FACTOR-`1/2` CORRECTION (soundness fix, 2026-06-12)

The residual was previously stated as `DiffJTP = CReal.Equiv (dSeriesCReal) (Rproduct)`
with `Rproduct = ϑ₃·S` (NO `1/2`).  **That statement is numerically false.**
At every `a ∈ (0,1)`, `θ ∈ (0,π)`, the bare product equals TWICE the series:

    ϑ₃(θ)·S(cos θ)  =  2 · dSeriesCReal      (ratio = 2.0, verified to 40 digits
                                              at a = 0.2, 0.3, 0.5, 0.8).

The correct differentiated-JTP identity is `§2.1(C)` of the convergence notes,
`K_t = ϑ₃·S/(2a)`, i.e. in the `U`-grading carried by `dSeriesCReal`
(`= Σ_{n≥1} n a^{n²} U_{n−1}(x) = D(θ)/sin θ`):

    dSeriesCReal  ≈  (1/2)·(ϑ₃·S)  =  Rhalf.                                  (DIFF)

The previous round dropped the `1/2`.  Closing the un-halved version would have
closed a FALSE `CReal.Equiv`; since the obligation was never discharged this did
not propagate (the conditional `K_t ≥ 0` never fired), but the *named obligation
itself was wrong*.  Fixed in `JTPIdentity.lean`:

- new `Rhalf := CReal.mul (ofQ' half) Rproduct` and `Rhalf_approx_nonneg`,
- `DiffJTP` now `:= CReal.Equiv (dSeriesCReal) (Rhalf)` (the TRUE identity),
- `Kt_geRat_zero_of_diff` / `Kt_geRat_zero_of_productDerivativeLimit` /
  `DiffJTP_eq_productDerivativeLimit` all re-oriented through `Rhalf`.

All axiom-clean (`[propext]`/`[propext, Quot.sound]`); build green.

## The honest residual

`DiffJTP` (`= CReal.Equiv (dSeriesCReal …) (Rhalf …)`, with the corrected `1/2`)
is the single remaining analytic obligation — the differentiated
Jacobi-triple-product identity `Σ n a^{n²} sin nθ = (sin θ/2)·ϑ₃·S`, equivalently
`Rtrunc M ≈ R` of `UTelescope.Kt_nonneg_of_residual`.  It is **NOT** discharged
and is **NOT** a `sorry`: it is exposed as a named `Prop` hypothesis, and only the
conditional `DiffJTP → K_t ≥ 0` is proved.

### Why the matched-truncation strategy does NOT close it (sharp finding, 2026-06-12)

The proposed closure route — find finite truncations `seriesTrunc M ≈ productTrunc M`
matched at each level `M` — **cannot succeed**, and the obstruction is now pinned
down exactly.  Reindex `dSeriesCReal`'s partial sum as `dPartial M`.  Then
(verified to 40 digits):

1. `dPartial M = D_M/sin θ` **exactly**, where `D_M = −½·d/dθ(th3series_M)` and
   `th3series_M(θ) = 1 + 2Σ_{n≤M} a^{n²} cos nθ` is the finite theta-**series**
   truncation.  (So the series side IS the differentiated finite theta-series.)
2. The finite log-derivative `d/dθ(th3prod_M) = −sin θ·th3prod_M·Spart_M` holds
   **exactly** (pure product rule — this is what `DiffProduct.leibniz` captures).
   So `(1/2)·Ppart_M·Spart_M` is the differentiated finite theta-**product**.
3. BUT `th3series_M ≠ th3prod_M` at every finite `M`: the finite Gauss identity
   `gauss_qbinom_all` (`qProd = gaussSum`) equates the product and the Gaussian
   sum only for the FULL coefficient sum / `N → ∞`; truncating the series at `M`
   terms and truncating the product at `M` factors give **different** finite
   numbers (differences `~ (a·a)^M`, e.g. `0.18, 0.028, 0.0059, 0.0015, …` at
   `a = 0.5`).
4. Consequently `dPartial M` (super-geometric, `~ a^{(M+1)²}`: at `a=0.5` already
   `10^{−11}` from its limit by `M=5`) and `(1/2)·Ppart_M·Spart_M` (geometric,
   `~ (a·a)^M`: only `10^{−3}` by `M=5`) converge to the SAME limit at
   **different rates**.  There is **no** finite `M` at which they are equal, so
   no finite equal-at-each-level identity exists.

The two truncation families are genuinely distinct finite objects coinciding
only in the limit; `CReal.Equiv` between them therefore reduces to *the two
limits being equal*, which is precisely the differentiation–limit interchange
and is NOT a finite algebraic identity.  `DiffProduct.leibniz` supplies the
finite product rule (step 2) but cannot bridge the series↔product truncation gap
(step 3) — that bridge is the `M → ∞` limit of Gauss's identity differentiated,
i.e. the missing engine.

It is genuinely hard: a term-by-term differentiation of a convergent product (a
double-limit interchange `lim_h lim_L = lim_L lim_h`), NOT a finite identity.  It
introduces **no new positivity content** (positivity is already closed in
`ThetaConvGen.R_geRat_zero_gen`); it is purely an analysis engine (commuting
`d/dθ` with the limit).  The repo does not contain a constructive
`HasDerivAt`-of-`tsum` engine with explicit modulus, and that — specialised to
the geometric log-derivative modulus — is the sole outstanding Wall-2 lemma.

## NEW: the generic C¹-uniform-limit engine (`TsumDeriv.lean`)

The genuine remaining analytic engine — *the uniform limit of derivatives is the
derivative of the limit* (Bishop's constructive C¹-limit theorem) — is now BUILT,
in a new module `lean/YMGap/Continuum/TsumDeriv.lean`, axiom-clean (`[propext]`
only), with all moduli carried as `Type`-level data (AGENTS.md Rule 8):

- **`FDDerivData f d θ`** — the data-carrying Bishop finite-difference derivative:
  a modulus `δ : Q' → Q'` with the cleared (division-free) bound
  `|f(θ+h) − f(θ) − d·h| ≤ ε·|h|` for `0 < |h| ≤ δ ε`.
- **`PtwiseConvAt` / `UnifDerivConvAt`** — pointwise / uniform convergence with
  their moduli as data.
- **`C1Inputs f f' F g θ`** — the bundled hypotheses (pointwise convergence at the
  base and perturbed points, uniform derivative convergence, and the family's
  common finite-difference modulus = equicontinuity at `θ`).
- **`fdDeriv_of_unif` (CLOSED)** — the theorem: from `C1Inputs`, the pointwise
  limit `F` has finite-difference derivative `g θ` at `θ`, with explicit assembled
  modulus `δ ε := delStar (ε/4)`.  The proof is the genuine **four-piece triangle
  estimate** (pointwise tail at `θ+h` + the M-th finite-difference derivative +
  pointwise tail at `θ` + uniform derivative convergence), each piece `≤ (ε/4)·|h|`,
  assembled at the `Q'` increment level via the new `Q'` toolkit
  (`abs_eqv_congr`, `abs_neg`, `abs_sub_comm`, `abs_mul_le`, `abs_four_le`,
  `telescope6` — a pure six-atom abelian-group telescoping identity — and
  `four_q_eqv`).  No `CReal` division, no `Mathlib ℝ`, no `sorry`.

This is the reusable engine the convergence notes §2.3 named as the sole missing
piece.  It is generic (arbitrary `Q'`-valued function families) and carries no
positivity content.

### Bridge to the residual (`DiffProduct.lean`, `JTPIdentity.lean`)

The engine is specialised to the heat-kernel / Jacobi factors through ONE named
`Σ`-obligation (NOT discharged), isolating the instantiation residual precisely:

- **`DiffProduct.C1ToEquiv Dseries Rproduct`** (`Type`-valued) — carries the finite
  theta-product truncations `f`, their `leibniz`-derivatives `f'`, the limit
  `F = ϑ₃` and log-derivative `g = −sinθ·ϑ₃·S`, the working point `θ`, the
  `C1Inputs` modulus data for that family (the `O((a·a)^k)` geometric content), and
  the `bridge` identifying the engine's derivative value with the two CReal
  representations.
- **`DiffProduct.productDerivativeLimit_of_c1`** (axiom-free) —
  `C1ToEquiv → ProductDerivativeLimit`.
- **`DiffProduct.fdDerivData_of_c1`** — extracts the `FDDerivData` from the
  obligation's data, making explicit that `fdDeriv_of_unif` (the real engine, not a
  black box) consumes it.
- **`JTPIdentity.DiffJTP_of_c1`** — `C1ToEquiv (dSeriesCReal) (Rhalf) → DiffJTP`.
- **`JTPIdentity.Kt_geRat_zero_of_c1`** — the engine-routed closure
  `C1ToEquiv → K_t ≥ 0`.

**Is `K_t ≥ 0` unconditional?**  Not yet: it is now reduced to the SINGLE named
`Σ`-obligation `C1ToEquiv` (equivalently its `C1Inputs` field — the theta-product
differentiation modulus data for the specific Jacobi factors).  The generic
C¹-limit theorem that consumes it is fully discharged; what remains is the
*instantiation* — supplying the pointwise/uniform/equicontinuity moduli for the
concrete theta-product family (the `leibniz` finite-product-rule derivative plus
the geometric `O((a·a)^k)` log-derivative tail).  This is a genuine, bounded
modulus-construction task, no longer an open analysis theorem.

Modules build via
`cd lean && lake build YMGap.Continuum.TsumDeriv YMGap.Continuum.DiffProduct
YMGap.Continuum.JTPIdentity`; all new declarations axiom-clean.

## NEW: DERIVATIVE UNIQUENESS (Route A — the CoRN `Derivative_I_unique` analogue)

The structural reason `C1ToEquiv` stalled is that its `bridge` field was a *raw
assumed* `CReal.Equiv Dseries Rproduct` (the differentiated identity), and the
engine output `FDDerivData` was computed then DISCARDED.  The constructive fix
(CoRN `ftc/Derivative.v` `Derivative_I_unique`): two finite-difference derivatives
of the SAME function `F` at the SAME point are EQUAL — so do not compare the two
truncation sequences (incompatible rates `a^{(M+1)²}` vs `(a·a)^M`), compare the
two derivative VALUES instead.

LANDED, axiom-clean (`[propext, Quot.sound]`), in `TsumDeriv.lean`:

- `Q'.le_of_mul_le_mul_left`, `Q'.le_zero_of_le_all_pos` (constructive Archimedean
  over `Q'`, via decidable `Int`-num trichotomy), `Q'.eqv_zero_of_abs_le_all_pos`,
  `Q'.abs_of_nonneg`, `Q'.min_le_left'/right'`, `Q'.lt_min'` — the small `Q'`
  toolkit the uniqueness estimate needs (the import chain does not reach
  `Sqrt.lean`, so these are local).
- `sub_rem_alg` / `fdRem_sub` — the two cleared remainders differ by exactly
  `(d₁ − d₂)·h` (the common `F(θ+h) − F θ` telescopes away).
- **`fdDeriv_unique` (CLOSED)** — `FDDerivData F d₁ θ → FDDerivData F d₂ θ →
  d₁ ≃ d₂`.  Per-`θ`, NO uniformity required: pick `ε`, pick `h = min(δ₁ ε', δ₂ ε')`
  past both moduli; `|(d₁−d₂)·h| ≤ |fdRem F d₂| + |fdRem F d₁| ≤ ε·|h|`; cancel the
  positive `|h|` ⇒ `|d₁−d₂| ≤ ε` for all `ε` ⇒ `d₁ ≃ d₂` (Archimedean).  Genuinely
  independent inputs (`D₁`, `D₂` are separate) — not circular.

In `DiffProduct.lean`: `deriv_values_eq_of_common_limit` (re-export of the engine),
and the SHARPENED residual `C1UniqInputs` + `productDerivativeLimit_of_uniq`
(closes `ProductDerivativeLimit` from two common-`F` `FDDerivData` + a realisation,
the engine output now CONSUMED not discarded).  In `JTPIdentity.lean`:
`DiffJTP_of_uniq`, `Kt_geRat_zero_of_uniq`.  In `JTPInstance.lean`:
`ThetaUniqAssembly`, `Kt_geRat_zero_of_uniq_assembly`.

### Honest verdict — is `K_t ≥ 0` now unconditional?

**No** — but the blocker is genuinely RELOCATED, and the reusable uniqueness lemma
is in hand.  Route A reduces the *differentiated* double-limit interchange to:

1. the UNDIFFERENTIATED limit-level Jacobi identity `ϑ₃^{ser} = ϑ₃^{prod}` as
   functions (the `N → ∞` limit of the proven finite `GaussQBinom.gauss_qbinom_all`)
   — this is what makes the SERIES-side `FDDerivData` live over the SAME `F` as the
   product side, and
2. a rational→real realisation (`C1UniqInputs.realise`): the `Q'`-valued
   `fdDeriv_unique` equates RATIONAL derivative values, whereas the actual
   derivative (the limit of `Dseries`) is a genuine `CReal`.  A fully unconditional
   close would need a `CReal`-valued `fdDeriv_unique` (CReal abs / CReal Archimedean
   / cancellation-by-a-positive-CReal — none of which currently exist in the repo).

Both (1) and (2) are strictly more elementary than the differentiated interchange
`ThetaFamilyAssembly` previously asked for: (1) is an *undifferentiated* identity
whose finite core is already proved, (2) is a packaging concern.  The genuine
analysis engine (uniqueness) is fully discharged.

## NEW: the CReal-VALUED derivative-uniqueness port (Route A, unconditional layer)

The `Q'`-valued `fdDeriv_unique` equated RATIONAL derivative values, leaving a
`Q'→CReal` realisation/infinitesimal lift for the user (Route A's `realise`, Route
B's `infinitesimal`).  That lift is now CLOSED at the `CReal` level — the genuine
CReal upgrade of the uniqueness engine, landed axiom-clean
(`[propext, Quot.sound]`) in `TsumDeriv.lean`:

- **`FDDerivDataC F d θ`** — the `CReal`-VALUED data-carrying finite-difference
  derivative: `F : Q' → CReal`, derivative value `d : CReal`, modulus `δ`, and the
  cleared bound `CReal.leRat (CReal.abs (fdRemC F d θ h)) (ε·|h|)`.  The increment
  `h` stays RATIONAL (the natural setting: `θ, h, ε` rational, only VALUES are
  `CReal`s).
- **`fdRemC` / `fdRemC_approx` / `fdRemC_sub_approx`** — the `CReal` remainder (all
  ops index-wise, so its `approx n` is the `Q'`-level `fdRem`); the two-remainder
  difference telescopes to `(d₁−d₂)·h` at every index (the same `sub_rem_alg`).
- **`abs_mul_nonneg_right`** — `|c·h| ≈ |c|·h` for `h ≥ 0` (sign-cased; avoids the
  general multiplicative `|c·h| = |c|·|h|` the `Q'` substrate lacks).
- **`fdDeriv_uniqueC` (CLOSED)** — `FDDerivDataC F d₁ θ → FDDerivDataC F d₂ θ →
  CReal.Equiv d₁ d₂`.  Proof shape unchanged from the `Q'` version
  (`|(d₁−d₂)·h| ≤ |fdRem d₂|+|fdRem d₁| ≤ ε|h|`), cancelling the positive RATIONAL
  `h` per-approximation (`Q'.le_of_mul_le_mul_left`), then the CReal infinitesimal
  cancellation `CReal.Equiv_of_abs_sub_le_all_pos` (CoRN `AbsIR_approach_zero`).
  Genuinely independent inputs (`D₁`, `D₂` separate `FDDerivDataC` — no assumed
  `Equiv`); NOT circular.

Wired downstream (axiom-clean): `DiffProduct.C1UniqInputsCRealDeriv` (carries ONLY
the two common-`F` `FDDerivDataC`, NO `realise`/`infinitesimal` field) +
`productDerivativeLimit_of_uniq_creal_deriv`; `JTPIdentity.DiffJTP_of_uniq_creal_deriv`
+ `Kt_geRat_zero_of_uniq_creal_deriv`.  This is the strongest available routing: the
WHOLE remaining input is two `CReal` finite-difference derivatives (series side +
product side) of the ONE limit `ϑ₃` at `θ` — the `Equiv` is produced by the engine,
not assumed.

### The parametrisation match (Task A): BLOCKED, residual pinned (`ThetaParam.lean`)

The clean single-substitution `(z, q)` match `gauss_qbinom_creal_equiv` hoped for is
GENUINELY BLOCKED by the complex-vs-real / two-sided structure of the real theta
factor: `HKPos.factor c x = 1 + 2cx + c² = (1 + cz)(1 + cz⁻¹)` with `z = e^{iθ}`
COMPLEX, whereas a single `GaussQBinom.qProd z a N` is ONE-sided.  The repo's product
side `thetaConvCRealGen` has `approx N = Ppart a x N`, the TWO-SIDED real product
`∏(1−a^{2k+1})·(1+2a^{2k+1}x+a^{4k+2})`, which is NOT a single `qProd z a N` and so
is NOT in the image of `gauss_qbinom_creal_equiv`.  `ThetaParam.lean` records this
honestly (does NOT fake a match) and supplies the genuine reusable REAL bridge
`theta_common_F_of_approx_equal` (common-`F` from per-`N` real equality, via the
`CRealAbs` limit-of-equal-sequences engine) + the sharp named residual
`RealThetaPerN` (the per-`N` REAL diagonal collapse of the two-sided Gauss product).

### Honest verdict — is `K_t ≥ 0` unconditional?

**Still not unconditional**, but the residual is RELOCATED to its most elementary
form and the analysis engines are ALL discharged.  Both the `Q'`-uniqueness
(`fdDeriv_unique`) AND the `CReal`-uniqueness (`fdDeriv_uniqueC`) engines are closed;
the CReal port removes the prior rational→real lift entirely.  What remains is purely
the INSTANTIATION: exhibit `dSeriesCReal` and `Rhalf` as `FDDerivDataC` of one common
`CReal` limit `F = ϑ₃` at `θ` (the two derivative-modulus data + the per-`N` real
common-`F` identity `RealThetaPerN`, the two-sided Gauss diagonal).  No open ANALYSIS
theorem remains on this layer — only the concrete modulus/identity construction.

## Axiom status

All load-bearing declarations report `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`.  The new
`TsumDeriv.lean` engine and the `CReal` `fdDeriv_uniqueC` port are axiom-clean;
`ThetaParam.lean` is `[propext]`-only.

## Build / wiring

- Modules: `lean/YMGap/Continuum/DiffProduct.lean` (the finite Leibniz engine)
  and `lean/YMGap/Continuum/JTPIdentity.lean` (imports `DiffProduct`); both build
  green via `cd lean && lake build YMGap.Continuum.DiffProduct
  YMGap.Continuum.JTPIdentity`.
- To include in the default build, add to `lean/YMGap.lean` (after the
  `UTelescope` / `ThetaConvGen` imports):
  `import YMGap.Continuum.DiffProduct`
  `import YMGap.Continuum.JTPIdentity`.
