# Categorical structure versus physical spectral scale

## Purpose

The categorical and sheaf-theoretic architecture fixes admissible composition,
descent, gluing, and proof dependencies.  It does not by itself determine a
dimensionful mass scale.  Physical mass requires analytic enrichment: lattice
spacing, action and coupling, a physical separator or transfer operator, a
normed comparison, an RG trajectory, and a same-object continuum realization.

This boundary is already respected by `PhysicalSeparator.lean`,
`TrueMarginRecursionPhysical.lean`, `AdditiveErosionAdequacy.lean`, and
`UniformCorrelationDecay.lean`.  The new mass-normalized persistence module
makes the intervening RG algebra explicit without claiming the missing analytic
producer.

## Exact rate and the scaling test

For a physical separator `q(a)` with `0 < q(a) < 1`, the exact lattice decay
rate in physical units is

\[
M(a) = -\frac{\log q(a)}{a}.
\]

A fixed inequality `q(a) < 1` is not enough.  The possibilities
`q(a) = exp(-m_0 a)`, `q(a) = exp(-a^2)`, and `q(a) = q_0 < 1` respectively
give a finite positive limit, a vanishing limit, and a divergent rate.  Hence a
bare heat-kernel separator, such as `q_HK = w^3`, becomes physically relevant
only after a quantitative comparison with the separator of the plaquette-
coupled Gibbs law.

## Mass-normalized blocking law

For `a_{k+1} = b_k a_k`, suppose an analytic argument supplies

\[
q_{k+1} \le q_k^{b_k} e^{\delta_k}.
\]

Then

\[
M_{k+1} \ge M_k - \frac{\delta_k}{a_{k+1}},
\qquad
M_N \ge M_0 - \sum_{k<N}\frac{\delta_k}{a_{k+1}}.
\]

`MassNormalizedGapPersistence.lean` formalizes the rational lower-certificate
version of the second implication.  Its input is a per-scale mass certificate,
the normalized one-step inequality, a constructive `SummableDistortion` budget,
and strict anchor dominance.  Its output is the canonical `QFloor` plus an
explicit dyadic tail modulus.

`PhysicalSeparatorLogRate.lean` supplies the direct-artanh rate layer, and
`PhysicalSeparatorFullLogRate.lean` extends it constructively to every positive
rational separator below one by computing a binary range reduction.  The full
layer defines `-log(q_j)/a_j` and proves per-scale strict positivity without a
supplied logarithm-window witness.  On the direct half-window the quantitative
sandwich is

\[
\frac{1-q_j}{a_j}
\;\le\;
\frac{-\log q_j}{a_j}
\;\le\;
\frac{9}{4}\frac{1-q_j}{a_j}.
\]

The lower comparison extends to the full range.  A finite-prefix ceiling is
computed directly from the binary reduction; an eventual same-object estimate
`1-q_j <= M*a_j`, together with `a_j -> 0`, puts the tail in the half-window and
produces the global upper ceiling.  Thus the margin is not identified with the
exact rate: it is a certified rational comparison coordinate.

The remaining upper comparison is precisely that linear same-object margin
estimate.  No categorical witness count, fixed-cutoff heat-kernel gap, or bare
combinatorial multiplicity is used as a source of physical mass.

The heat-kernel comparison audit sharpens this boundary.  The original
`HKPhysicalComparison` assumes two-sided additive `O(a)` closeness between the
bare and physical margins.  `HKPhysicalLinearMarginTail.lean` proves that under
this assumption a finite physical margin rate exists exactly when the bare
margin rate is finite (up to changed constants), and gives a conditional no-go
when the bare rate escapes every linear ceiling.  Thus an additive residual
cannot itself perform nonperturbative mass renormalization.

`RenormalizedHKPhysicalComparison.lean` supplies the corrected interface

\[
  1-q_{\mathrm{phys},j}
  \le Z_j\bigl(1-w_j^3\bigr)+\delta_j,
  \qquad \delta_j\le C_\delta a_j\Lambda.
\]

The missing RG input is now explicit: prove
`Z_j(1-w_j^3) <= C_Z a_j` on the same Gibbs/transfer object.  This and the
residual produce the required physical `LinearMarginTail`, and the checked
BF4/Faraut adapter then yields the full exact physical-rate band.  No `Z_j` or
comparison inhabitant is supplied by the reduction.

`FixedDistancePhysicalSeparator.lean` now isolates the correct dimensionful
producer theorem.  If the same physical separator satisfies

\[
q_j^{n_j}\le\rho<1,\qquad n_j a_j\le L,
\]

then constructively

\[
\frac{1-\rho}{L}\le\frac{1-q_j}{a_j}
\le\frac{-\log q_j}{a_j}.
\]

`BF4PhysicalSeparatorProducer.lean` wires the exact BF4 quarter certificate to
this theorem without identifying the macro rate `1/4` with a one-step
separator.  `BF4FarautPhysicalSeparatorProducer.lean` goes one step further:
the macro depth is definitionally the exact Perron depth `46*bits+3`; the
growing core length is derived from the existing AF/Faraut `O(1/t)` budget,
and the quadratic spacing envelope derives a uniform ceiling for the three
fixed endpoints.  `BF4AFPhysicalSpacingToZero.lean` derives the physical
spacing-to-zero modulus from exact AF-trajectory identification and the
corrected AF cutoff.  `BF4FarautFullLogPrefixTailCertificate.lean` then shows
that one `LinearMarginTail` produces the full exact rate band.
Neither record is inhabited.  Their explicit `groupedPhysicalSameObject`
field is the remaining theorem that must identify the BF4 macro contraction
with powers of the actual correlator separator.

## Staged frontier

1. **M1 — mass-normalized persistence algebra [closed].**  The telescoping
   floor and constructive tail modulus from explicit normalized losses are
   kernel-checked.  The preferred direction-neutral core proves that no exact
   block/refinement factor is needed by the persistence algebra; both geometric
   conventions have checked forgetful adapters.
2. **M2a — exact physical log-rate reduction [closed].**  Exact full-range
   binary logarithm, positivity, unconditional proxy-to-log lower transfer,
   computed finite-prefix ceilings, and prefix/tail gluing are kernel-checked.
3. **M2b — physical separator producer [reduced, analytic core open].**  The
   fixed-distance implication, exact BF4 quarter adapter, AF/Faraut depth, and
   physical-length calculation are kernel-checked.  AF identification also
   yields `a_k -> 0`, with no separate spacing limit or endpoint ceiling.
   Still define `q_phys(k)` from the actual plaquette-coupled Gibbs/transfer
   object and prove its gauge-invariant correlator control, exact same-action
   data, same-object grouped-power bound, and either the linear margin
   `1-q_phys(k) <= M*a_k` directly or its renormalized sufficient inputs
   `Z_k(1-w_k^3) = O(a_k)` and `delta_k = O(a_k)`.
4. **M3 — BF4 comparison producer [spectral-input reduction closed; analytic
   inhabitation open].**  The refinement wrapper states the AF orientation literally,
   while `MassNormalizedLossPersistence.lean` isolates the factor-free
   normalized-loss core.  `ExactLogMassNormalizedLossPersistence.lean`
   identifies that rational core pointwise with one exact physical log-rate
   family, and `BF4FarautExactLossPersistence.lean` combines its floor with the
   renormalized upper ceiling on that same family.
   `SpectralLocalizedPhysicalMarginLoss.lean` supplies the unit-correct bridge
   from multiplicative localization to additive mass loss:
   `rateLoss_k = d_k*M_k <= M_ceiling*d_k`.
   `SpectralMarginInputMassNormalizedLoss.lean` applies this to the already
   stated `SpectralMarginInput`, uses its tail identification at the shifted
   inverse-square offset `fmCutoff+2`, and constructs the full loss budget.
   `BF4FarautSpectralMarginInputExactCertificate.lean` then yields the exact
   same-family band once the BF4/Faraut and spectral inputs are inhabited.
   Still prove from corrected-slab data the localization and bridge fields,
   physical ceiling, anchor dominance, exact spacing identification, and
   rational-to-exact mass certificate.  No indexing reversal or exact integer
   spacing ratio remains in the preferred interface.  The direct unscaled
   defect adapter is only a stronger normalized special case.
5. **M4 — same-object continuum bridge [active contract phase].**  Carry the
   physical rate floor through cutoff and thermodynamic removal, constructive
   OS reconstruction, transfer-semigroup identification, and generator-gap
   identification with explicit moduli.  These realization data are not
   consequences of the finite-scale exact band.

M1, M2a, and the fixed-distance/AF-length/spacing-limit parts of M2b are reusable
reductions.  The same-object inhabitant and linear margin of M2b and all of
M3–M4 contain the genuinely analytic and continuum-facing obligations.  M3's
consumer chain is now explicit, but its structures remain uninhabited; M4
remains open until the same continuum object and its constructive data are
built.
