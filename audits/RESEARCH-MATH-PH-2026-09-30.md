# Math-ph listing refresh: constructive Yang--Mills relevance

## Scan record

- Listing scanned: [arXiv math-ph new](https://arxiv.org/list/math-ph/new), which reported **Wednesday, 30 September 2026**; 81 entries total (13 new submissions, 45 cross-lists, 23 replacements).
- Completed scan: **2026-09-30 03:38 UTC**.
- Earliest next routine refresh: **2026-09-30 15:38 UTC**.
- This is a bounded relevance screen of the current listing, not verification of complete papers. Three closest analogues were inspected at abstract level; two pages could not be fetched directly by the browser, so their listing abstracts are the evidence used below.

## Result for the live project

The abstract screen identified no direct producer for the original-action signed-neighbor estimate. This does not establish that the complete papers contain no useful argument.

### Three closest analogues

1. [On the Spectrum of Some Temperley-Lieb Spin Chains](https://arxiv.org/abs/2609.38074): structured one-dimensional spin-chain gap estimates. Analogy only; no identification with the original Wilson operator was found.

2. [Improved estimate of local Markovianity for quantum Gibbs states](https://arxiv.org/abs/2609.38007): conditional-mutual-information decay with boundary-size dependence. A bridge to the project's signed covariance is not supplied by this screen.

3. [Is rapid mixing stable?](https://arxiv.org/abs/2609.36016): instability examples and sufficient stability conditions for Lindbladian dynamics. This is not the project's OS transfer.

## Use and limits

No theorem or hypothesis was imported. No numerical computation or Lean build ran. These cached findings are scope-limited research notes, not proof progress.

## Requested seven-paper review (2026-10-01 22:41 UTC)

Latest record verification: **2026-10-02 03:58:07 UTC**, by the parallel Sol
reviewer; all seven records still list only v1. The following theorem screen
is cached, not a new full-paper review. A further source-applicability pass
against `DisjointFaceJointMargin.joint_margin_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:476`)
and `corrected_joint_margin_square_bound` (same file, line 495) found no paper
supplying the retained signed heat/debt estimate or scaling-uniform residual
control. The current proof and its separate focused verification are recorded
in `audits/AUDIT-DISJOINT-FACE-JOINT-MARGIN-2026-10-02.md`.

Most directly useful methods remain [38220, section 7 and appendix B.3](https://arxiv.org/html/2609.38220v1)
for rigorous certificate validation, [40171, equations (8)--(10), (14)--(16)
and theorems 1--2](https://arxiv.org/html/2609.40171v1) for retaining joint
unnormalized information before cancellation, and [39802, section 2.1,
theorem 1](https://arxiv.org/html/2609.39802v1) for conditional Schur-loss gap
assembly on the SAME operator. Their hierarchical recursion, fixed-regulator
ladder hypotheses and positive-operator interface inputs, respectively, are
not proved identifications or estimates for the original Wilson family.
The cached different-model, opposite-inequality and qualified-duality limits
of the other four papers remain unchanged. No external premise is imported.

This targeted review was requested by the user and performed by a parallel Sol
reviewer, with primary-source record checks by the main agent. All seven v1
records resolve. It is NOT a routine listing refresh; the scan record above
is unchanged. Abstract summaries below are paraphrases. Applicability labels
are our assessment, not a claim that the papers identify the repo's theory.
Theorem screening does not constitute independent verification of full proofs.

Latest requested delta review: **2026-10-02 02:23 UTC**. The main agent checked
all seven primary abstract records; all still list only v1. A parallel Sol
reviewer reused this cached theorem screen against the current original joint
evaluator. No additional paper argument supplying source-specific centered
Gram coercivity, signed-remainder control or a useful positive scaling margin
was identified. Gcd reduction changes stored arithmetic, not those estimates.
The current consumer is still
`BF4ExactSlabFixedSpatialCollectedFamilyMargin.finite_margin_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:316`),
with `check_correct` (line 350) and `certify` (line 366); a useful accepted
input remains missing. No full-paper reread, routine listing scan, Lean build
or proof-status change occurred. The assessments below are reused, not new
mathematical progress.

### 2609.40171 — boundary reconstruction

[Information-preserving boundary reconstruction for center-flux energetics in a regulated SU(3) gauge ladder](https://arxiv.org/html/2609.40171v1), Hongyu Ma.
The abstract's construction retains unnormalized conditional interior matrices,
including weights and within-branch coherence; path probabilities alone fail
its matched magnetic-observable test. Matched bulk terms cancel, leaving a
length-independent boundary energy cost. Theorems 1–2 (section 6), under H1–H4,
give finite sector/line-energy densities and open/periodic comparison at six
fixed cutoffs. Equations (8)–(10) and (15)–(16) expose the retained information
and cancellation. Spacing, width, coupling and cutoff stay fixed.

Assessment: the closest methodological match for source-preserving boundary
comparisons. Investigate the exact matrix-preservation argument before any
cross-volume energy comparison. No original Wilson norm/covariance estimate,
cutoff removal, transverse limit or continuum mass input is supplied.

### 2609.39802 — quantum sampler localization

[Double Localization for Quantum Gibbs Sampler Gaps: From an Abstract Framework to Finite-Group Models](https://arxiv.org/pdf/2609.39802), Ryu Hayakawa et al.
The abstract separates local quantum updates from a global observable interface.
Theorem 1 (PDF pp. 8–9) combines interface and local bounds under quantitative
assembly conditions. Theorem 2 (pp. 10–11) treats specified Davies dynamics for
vertex-only finite-group quantum-double models, WITHOUT plaquette terms, on
three-regular graphs of girth at least six. Its graph-size-independent gap
requires beta*J < log(5/3); the S3 specialization extends uniformity to
0 <= beta*J <= log(3). Equation (34) records finite assembly counts.

Assessment: local/global assembly method only. The bounded operator is a
thermal sampler generator, not our original OS transfer or physical Hamiltonian.
No identification bridge for this repo is supplied.

### 2609.39475 — blockade Hamiltonian gap

[Excitation gap of a blockade structure with Z2 topological order](https://arxiv.org/html/2609.39475v1), Simon Fell et al.
Theorem 1 and equation (6) establish a size-uniform gap and fourfold ground-state
degeneracy for a two-dimensional blockade Hamiltonian at sufficiently small
Omega and sufficiently large size. The argument uses gap stability and local
symmetry; the paper also discusses extensions to other quantum-double
structures and non-Abelian sector issues.

Assessment: a different interacting Hamiltonian, dimension and perturbative
regime. No original Wilson transfer, scaling, continuum survival or physical
mass input was identified.

### 2609.39780 — obstruction to plaquette-only shortcuts

[No-go theorems for dual Hamiltonians of Non-Abelian Lattice Gauge Theories](https://arxiv.org/html/2609.39780v1), Marco Garofalo et al.
Theorem 1 and Corollary III.2 give a linear-size tree-distance obstruction for
the specified static-constraint dualization, with the additional-link bound
Omega(ell/(K+1)^(1/d)). Theorem 2 shows that the specified dynamic helper-link
plaquette constraint overconstrains the non-Abelian system. These are qualified
duality obstructions, not a no-go theorem for Yang–Mills itself.

Assessment: actionable warning against assuming a plaquette-only rewrite
preserves locality. Retain the original link action and require a proved
operator/locality identification for any proposed dual replacement. The
original-link Wilson/OS path is not refuted by these theorems.

### 2609.38220 — exact hierarchical recursion and certificates

[Positive-temperature spin-glass order on the three-dimensional Migdal–Kadanoff lattice](https://arxiv.org/html/2609.38220v1), Yan Ru Pei.
Theorems A–B establish low-temperature order on a hierarchical Ising spin-glass
lattice using its exact recursion (equation (1.1)). Its effective dimension
1+log2(n) is not a cubic three-dimensional lattice. The Gaussian case includes
computer-assisted rational/interval certificates and associated code.

Assessment: a finite-certificate workflow analogy, not an original Wilson
renormalization law. External computation is not a proof oracle here; any
adapted Rust-produced certificate still needs independent Lean checking.

### 2609.39959 — Davies rapid mixing

[Haah's 3D cubic code thermalizes rapidly](https://arxiv.org/html/2609.39959v1), Sebastian Stengele, Libor Caha, Ángela Capel and Simone Warzel.
The abstract turns a spatial correlation-decay condition into a modified
log-Sobolev inequality for the Davies generator. Theorems 1.1/2.1 yield
fixed-positive-temperature rapid mixing for the cubic stabilizer code, with
the specified bath-rate and correlation assumptions.

Assessment: open-system thermal dynamics, not our original gauge-theory
Hamiltonian. Its mixing estimate cannot be substituted for an OS transfer or
physical mass gap without a same-theory bridge.

### 2609.38295 — unconditional log-concave variance bound

[A dimension-free bound for isoperimetry of unconditional log-concave measures](https://arxiv.org/html/2609.38295v1), Dan Mikulincer and Ilias Zadik.
Theorem 1.1, equation (1.2), bounds the Poincare constant independently of
dimension for isotropic, unconditional, log-concave probability laws on R^n.
The proof transforms the measure and analyzes an associated Dunkl–Langevin
operator; these hypotheses are essential to the stated theorem.

Assessment: relevant variance-bound methodology, but no proof identifies our
compact-group Wilson measure with this hypothesis class. No SAME interacting
variance estimate follows merely from its dimension independence.

## Consequence for the live frontier

No reviewed result supplies the missing original Wilson signed-cost/SAME-variance
estimate on a justified four-dimensional scaling family, nonzero continuum
excitation, physical spacing/mass calibration or every-group realization.
The two prioritized lessons are exact conditional-matrix preservation before
boundary cancellation (40171), and proof of locality before dual substitution
(39780). No theorem was imported as a Lean premise; these notes close no proof
node. Routine literature polling remains at most once per twelve hours.

## Focused applicability second pass (2026-10-01 23:19 UTC)

The user requested these same seven IDs again. The main agent refreshed their
primary records: all remain v1. A parallel Sol reviewer inspected the strongest
arguments against the current source frontier. This was a targeted second pass,
NOT another math-ph listing scan. No Lean premise, proof status or goal changed;
no build or heavy computation ran.

### Preserve the information that makes cancellation exact

[2609.40171, equations (8)--(10), (14)--(16), theorems 1--2 and appendix 9.1](https://arxiv.org/html/2609.40171v1)
preserves unnormalized conditional interior matrices, not just branch
probabilities. Matched interior terms therefore cancel before the boundary
estimate. Its length-uniform cost is at fixed spacing, transverse width,
coupling and cutoff, under H1--H4; it is not a spacing-small variance-relative
temporal cost.

Our existing one-slice pins already preserve original mass and moments:
`BF4ExactSlabFixedSpatialFamilyVarianceWard.marginalMass_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:48`) and
`BF4ExactSlabFixedSpatialProjectedSourceEnergy.oddMoment_projected_source`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:117`).
The latter requires supported, fringe-independent tests. These are not
cross-width or changing-family maps. A proposed comparison must retain the
original joint pairings and signed insertions, not just their scalar mass.

### Lower-gap assembly is not automatic from local gaps

[2609.39802, section 2.1, theorem 1](https://arxiv.org/html/2609.39802v1)
is abstract finite-dimensional positive-operator algebra, not restricted to
Davies dynamics. It requires a positive local decomposition of the SAME
operator, an orthogonal interface projection, local gaps, local shorted-form
(Schur-complement) lower bounds, and coverage/overlap/assembly conditions G1--G3.
The resulting lower bound is
`(1 - sqrt(1 - eta)) * min(a, tau)` with the stated assembly constants.
The Schur-loss condition explicitly controls coupling to complementary
directions; separate local gaps do not replace it. This is a potential
lower-gap method only after those original-operator inputs are proved, not a
replacement for the current upper-energy survival estimate. The finite-group
Davies application still does not identify the Wilson OS transfer.

### Keep the direction and operator of the variance inequality

[2609.38295, equation (1.1), theorem 1.1 and lemma 2.4](https://arxiv.org/html/2609.38295v1)
provides `Var <= C * gradientEnergy` and Lipschitz pushforward transfer
`C_P(T#nu) <= L^2 * C_P(nu)`. This is a LOWER gradient-energy estimate;
it does not provide the desired UPPER temporal-energy estimate
`E_j <= C * a_j * OWNVar_j`. Its main theorem requires isotropic,
unconditional log-concavity. No original Wilson identification with that
measure class was supplied by this review.

The actual current recipient remains
`BF4ExactSlabFixedSpatialFamilyVarianceTaylor.padded_family_energy_variance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`):
`E = 12*(1-w)*OWNVar + varianceRemainder`, on its stated original padded
family. The complete signed remainder, physical spacing join and justified
changing family still need their own estimates.

### Certificates and qualified obstructions

[2609.38220, section 7 and appendix B](https://arxiv.org/html/2609.38220v1)
separates a frozen finite bridge from a proved invariant all-level family.
Its one-sided rounding preserves the comparison order; integer/rational and
rigorous interval checks verify the finite conditions. This is a useful
certificate design pattern only after proving a corresponding ORIGINAL
Wilson recursion and preserved order. The hierarchical spin-glass recursion
is not such a law, and its external checker is not a Lean proof oracle.

[2609.39780, theorem 1, corollary III.2 and theorem 2](https://arxiv.org/html/2609.39780v1)
rules out the specified local static/dynamic plaquette dualizations, not our
original-link route. The blockade result (39475) and cubic-code Davies result
(39959) remain different-model estimates as recorded above. None of the seven
supplies the missing original Wilson scaling producer or closes a Clay node.

### Terminal-source obstruction follow-up (2026-10-01 23:38 UTC)

A further requested parallel Sol check found no additional original-source
producer in these seven papers; the cached priorities and scope remain
unchanged. The new checked generic model in
`audits/AUDIT-POSITIVE-SOURCE-HEAT-MODE-SCALING-2026-10-01.md` rules out filling
their missing Wilson comparison/interface inputs using only positive heat,
source positivity and a bare low-mode pin. Transferring either method still
requires control of the actual terminal `q*(f-ownmean)` on the SAME `q*P(q)`
law, not replacement by a truncated bare mode. No literature-derived module
or assumed analytic input was added; no routine listing scan was performed.

## Applicability after the reference-depth and moment proofs (2026-10-02 UTC)

The user requested a parallel review of the same seven papers. A Sol reviewer
reused the cached theorem screen and checked its applicability against the new
original-source declarations; the main agent checked the targeted primary v1
texts. This was NOT a routine listing scan. No Lean source, axiom, hypothesis
or proof status changed; no build or heavy computation ran.

The current one-plaquette reference obligation is
`4*(1-w)*(3-m2)+R <= c*(1+m2-m1*m1)`, using the COMPLETE original marginal,
its OWN mean and the signed Taylor remainder. The two sides are identified by
`BF4ExactSlabFixedSpatialPlaquetteWardMoments.plaquette_variance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:145`)
and `padded_plaquette_energy` (same module, line 250). No reviewed paper supplies
this estimate with a useful rate on the required changing family.

The certificate pattern in [2609.38220, section 7 and appendix B](https://arxiv.org/html/2609.38220v1)
now has a more precise possible application: test ONE finite signed margin at
the actual reference depth, with a rigorously computed cutoff-tail allowance.
`BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.windowCutoffCauchy`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:36`)
already constructs fixed-depth cutoff moduli for original window insertions.
`BF4WilsonAllNomeTemporalEnergyLimit.finiteEnergy_half_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:124`),
`BF4WilsonAllNomeMarginalVarianceLimit.finiteVariance_budget_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:119`) and
`BF4WilsonAllNomeCenteredTransferBondLimit.finiteScalar_connected_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredTransferBondLimit.lean:177`)
pin the energy and OWN variance to the original squared increment and connected
moments, including BOTH finite endpoint means.

Proposed certificate condition, NOT a newly checked theorem: with cutoff
errors bounded by epsilonE and epsilonV, a verified pivot p beyond their
explicit moduli satisfying `E_p+epsilonE <= c*(OWNVar_p-epsilonV)`, with c>=0,
would imply the all-late-cutoff reference inequality. Its actual recipient is
`BF4WilsonAllNomeTerminalReferenceEnergyRatio.completed_reference_ratio`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`),
which propagates the supplied reference coefficient to `c*(1+comparisonEta)^2`.
No finite positive margin or useful changing-family coefficient was produced
by this review. The hierarchical recursion of 38220 is NOT a Wilson law;
external arithmetic still requires independent Lean checking.

The other cached assessments remain unchanged: 40171 teaches preservation of
the original operator pairings before boundary cancellation; 39802 and 38295
are lower-energy methods, not the upper temporal-energy estimate above; 39780
constrains the specified dual replacements; 39475 and 39959 concern different
Hamiltonian/dynamics models. No same-theory scaling or Clay obligation closed.

## Applicability after collected finite evaluation (2026-10-02 02:04 UTC)

The user's renewed seven-ID request was handled by a parallel Sol reviewer
using the cached theorem screen and current source. The main agent inspected
the primary v1 HTML for 40171, 39802, 38220 and 38295 and checked the current
evaluator declarations. The other three assessments reuse the cached review;
their records were not fetched again. No routine listing scan or Lean build
ran, and no external theorem was introduced as a premise.

The precise change since the preceding pass is computational, not an imported
estimate. `BF4ExactSlabFixedSpatialCollectedFamilyMargin.finite_margin_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:298`)
identifies the collected evaluation with the ORIGINAL finite margin.
`check_correct` (same file, line 332) preserves its full acceptance conditions;
`certify` (same file, line 348) returns the EXISTING original certificate on
success. No useful successful input has been produced.

[38220, section 7 and appendix B.3](https://arxiv.org/html/2609.38220v1)
separates search choices from exact rational/one-sided interval validation.
This is the closest workflow match to the existing checker, not a Wilson
estimate: its hierarchical recursion and preserved comparison order have no
proved identification with our changing four-dimensional family. Its
polynomial-product acceleration is likewise not a checked implementation here.
The collector bounds stored lengths, not coefficient bits, intermediate work
or practical runtime; see
`audits/AUDIT-COLLECTED-FAMILY-MARGIN-2026-10-02.md`.

[40171, sections 4--6](https://arxiv.org/html/2609.40171v1)
reinforces preservation of unnormalized joint information before cancellation.
Our `pairing_pin` (collected evaluator, line 250) already preserves the original
two-endpoint joint pairing. That identity does not supply a signed-margin
bound, and the paper's boundary budget fixes the regulator parameters.

[39802, theorem 1](https://arxiv.org/html/2609.39802v1) remains a conditional
lower-gap assembly theorem requiring the SAME positive-operator decomposition,
interface, Schur-loss and coverage estimates. [38295, theorem 1.1 and equation
(1.1)](https://arxiv.org/html/2609.38295v1) bounds variance ABOVE by gradient
energy under isotropic, unconditional log-concavity. Neither gives the UPPER
temporal-energy bound needed by the current survival margin. The cached
different-model assessments of 39475/39959 and qualified dualization warning
of 39780 are unchanged.

Result: no new paper-derived mathematical input, positive accepted margin,
justified changing-family rate or physical/continuum proof node. The actual
next consumer remains the original checker: produce useful positive signed
slack with its exact cutoff modulus, padding, OWN means and full jump intact.
