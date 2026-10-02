# Requested arXiv papers and Yang Mills applicability

Completed targeted review: **2026-10-02 16:30 UTC**. All fifteen unique
primary abstract records resolve and list only **v1**. The repeated
2610.00453 was reviewed once. This is an explicit paper review, not a listing
scan; the last routine scan remains 2026-09-30 03:38 UTC, with earliest next
routine refresh 2026-09-30 15:38 UTC, as recorded in
`RESEARCH-MATH-PH-2026-09-30.md`. No compiler, external checker, installation,
heavy computation, Lean edit, or commit was performed by this reviewer.

The new papers add potentially transferable norm-loss, moment-bootstrap,
certificate, and algebra-construction methods. No inspected result supplies
the missing useful estimate for the original interacting Wilson family.
Applicability statements below are this reviewer's inferences, not paper
theorems about the repository. Screening statements and selected arguments
does not independently verify the complete paper proofs.

## Current mathematical consumer

The current task is to compare active third-Casimir source moments and the
complete signed curvature, Ward, centering and remainder costs, retaining the
negative observable square or projection gain, with the **OWN interacting
variance** on a physically justified changing family. Physical spacing,
nonzero continuum survival, same-theory QFT reconstruction, positive physical
mass and realization for every compact simple group remain open.

The live proof campaign has now passed the generic active-channel Sobolev
check and the actual family consumer's focused check. Evidence is recorded in
`AUDIT-ACTIVE-CUBIC-CHANNEL-NORMS-2026-10-02.md`.
Source recipients inspected here are
`SU2QuaternionPassiveChannelSobolevError.channelSource_sobolevError_sum_le_active`
and
`BF4ExactSlabFixedSpatialFamilyChannelSobolev.padded_family_energy_le_activeSobolevChannelVariance`.
These are repository work, not an estimate imported from this literature
review. This reviewer did not run or independently audit their compilation.
Even a checked active-footprint budget needs a useful variance-relative
changing-family estimate; localization alone does not give that estimate.

## Seven previously reviewed papers

The cached detailed screen was read before fetching. Each primary record was
verified again; selected full-text statements were inspected to confirm the
scope and inequality direction. No changed version was found.

| Primary record and verified title | Inspected result and applicability |
| --- | --- |
| [2609.40171](https://arxiv.org/abs/2609.40171), Information-preserving boundary reconstruction for center-flux energetics in a regulated SU(3) gauge ladder | [Section 6, Theorems 1–2; Appendix 9.1](https://arxiv.org/html/2609.40171v1) establish sector densities and a length-independent boundary comparison under H1–H4, with spacing, transverse width, coupling and one of six cutoffs fixed. Preserve unnormalized conditional matrices before matched-interior cancellation. No cutoff/spacing/width-uniform source-to-variance estimate follows. |
| [2609.39802](https://arxiv.org/abs/2609.39802), Double Localization for Quantum Gibbs Sampler Gaps: From an Abstract Framework to Finite-Group Models | [Section 2.1, Theorem 1, equation (1)](https://arxiv.org/html/2609.39802v1) gives `(1-sqrt(1-eta))*min(a,tau)` for the same positive operator, requiring interface and local gaps, local shorted-form bounds, coverage, overlap and assembly estimates. Its vertex-only finite-group Davies application has graph-size uniformity for fixed `beta*J<log(5/3)`, or S3 through `log(3)`. A sampler is not the Wilson OS transfer. The HTML stops after Theorem 1; the versioned PDF fetch returned an internal error, so later application details here use the verified abstract and cached screen. |
| [2609.39475](https://arxiv.org/abs/2609.39475), Excitation gap of a blockade structure with Z2 topological order | [Theorem 1 and its proof](https://arxiv.org/html/2609.39475v1) concern a two-dimensional blockade Hamiltonian at small positive drive and sufficiently large size. A four-state low-energy band has vanishing finite-size splitting; this is not four exactly degenerate finite-volume ground states. Different Hamiltonian and perturbative regime; no Wilson scaling producer. |
| [2609.39780](https://arxiv.org/abs/2609.39780), No-go theorems for dual Hamiltonians of Non-Abelian Lattice Gauge Theories | [Corollary III.2, equation (30), and Theorem 2](https://arxiv.org/html/2609.39780v1) give tree-distance growth `Omega(ell/(K+1)^(1/d))` and inconsistency of the specified dynamic helper-link constraint. Require locality and operator identity before a dual substitution. This qualified obstruction does not refute the original-link Wilson route or Yang–Mills existence. |
| [2609.38220](https://arxiv.org/abs/2609.38220), Positive-temperature spin-glass order on the three-dimensional Migdal-Kadanoff lattice | [Section 7; Appendix B.3](https://arxiv.org/html/2609.38220v1) separate exact rational checks, directed transcendental enclosures and proved analytic recurrence inputs. Useful certificate design, conditional on a proved original-model recursion and preserved comparison order. The hierarchical Ising recursion is not a four-dimensional Wilson blocking law. |
| [2609.39959](https://arxiv.org/abs/2609.39959), Haah's 3D cubic code thermalizes rapidly | [Theorem 1.1](https://arxiv.org/html/2609.39959v1) provides a size-independent modified log-Sobolev constant at each fixed positive temperature for the specified cubic-code Davies dynamics. Correlation-to-mixing methodology; no beta-uniform physical Hamiltonian or OS-transfer gap is identified. |
| [2609.38295](https://arxiv.org/abs/2609.38295), A dimension-free bound for isoperimetry of unconditional log-concave measures | [Theorem 1.1, equations (1.1)–(1.2)](https://arxiv.org/html/2609.38295v1) give `Var <= C*gradientEnergy` for isotropic unconditional log-concave laws on Euclidean space. This is the opposite direction from the present upper temporal-energy survival estimate. The text gives a naive constant near `10^12`; `C<=8` is only a proposed improvement. No original Wilson hypothesis-class identification is supplied. |

## Newly requested papers

### Scalar ultraviolet construction

[2610.00453](https://arxiv.org/abs/2610.00453), Samuel Frank,
*Constructive Neural Network Field Theory: φ₂⁴ in Finite Volume*.
The [full text](https://arxiv.org/html/2610.00453v1), Proposition 4.7,
equation (87), bounds the shell Hessian below by
`sigma^-2*(1-12*t*kappa1*D_j*2^(-2j))*I`.
Theorem 7.4, equation (142), controls interacting background moments by
`K*C_g^p*p!*(J+1)^p`. Theorems 7.6–7.7 give shell errors
`C_T*2^(-2j)*j^3` and ultraviolet convergence in two dimensions.
The width schedule is `N_j>=c0*(j+1)*2^(4j)`; almost-sure feature thresholds
are retained. Lemma 8.1 tracks width-independent constants; Theorems 8.3–8.4
commute width/UV limits and identify the standard finite-volume scalar measure.
Section 10.2 explicitly says volume enters constants, including an exponential
moment prefactor. Section 10.3 records failed reflection positivity for the
infinite-width finite-cutoff free field and unresolved network regularizations.

Inference: the moment bootstrap and constant-dependence ledger are useful
patterns. They bound absolute scalar moments, not Casimir costs relative to
the original Wilson variance. Gaussian linear shells, scalar Wick interaction
and fixed volume are essential; no four-dimensional gauge construction,
physical time calibration or constructive Lean realization is supplied.
Its constructive-field-theory terminology is not a certification of this
repository's MLTT/HoTT gate; almost-sure feature existence is not an explicit
Lean witness or computable good-geometry modulus.

### Scan operator comparisons

[2610.01121](https://arxiv.org/abs/2610.01121), Youngwoo Kwon,
*Cost Comparisons for Random and Deterministic Scans in Component-Wise Markov Chains*.
[Theorems 1.1–1.2, equations (4) and (9)](https://arxiv.org/html/2610.01121v1)
assume reversible component updates on the same `L2(Pi)` with
`||K_j-P_j||<=lambda0<1`, where `P_j` is conditional expectation:

    eta_random >= (1-lambda0)*eta_sweep/(d*(2-eta_sweep))
    eta_sweep >= (1-lambda0)*eta_random/(8*d).

Section 5.1, equations (31)–(37), retains the telescoping squared norm losses
along the actual sweep. The reverse cost comparison can lose `d^2`.
Inference: useful algebra for composing contractions after SAME-space,
conditional-projection and global contraction identities are proved. It does
not produce a first positive gap or identify heat-channel operations with
conditional updates, and it gives no physical spacing or source survival.
The abstract exposes Lean ancillary files. Their coverage and dependency
files could not be read through the browser (unsupported Markdown content
type/cache-miss responses); no axiom compatibility or compilation is claimed.
Lemma 5.1's displayed proof uses the spectral theorem. Any constructive
adaptation needs the project's positive-form algebra or a witnessed substitute,
not an unchecked import of that spectral argument.

### Dissipative locality

[2610.01669](https://arxiv.org/abs/2610.01669), Marius Lemm and Tim Möbus,
*Dissipation-Enabled Operator-Norm Locality Bounds for Bose-Hubbard Hamiltonians*.
[Theorem 3.1, equations (6)–(7); Appendix A.1](https://arxiv.org/html/2610.01669v1)
require bounded graph degree/hopping, summable spatial weights and uniformly
positive bounded loss rates, with photon-loss order `ell>2` for locality.
Moment regularization scales as `t^(-k/(ell-1))`; its constants are independent
of total finite volume. The adaptive-cutoff time factor includes
`t^((ell-2)/(ell-1))`. Inference: explicitly paying an integrable short-time
Sobolev singularity is a useful cutoff-control method. Engineered loss is
load-bearing; weighted particle moments are not the original Casimir moment
budget, and adding dissipation changes the theory and operator.

### Other dynamics and models

| Primary record and verified title | Inspected scope and applicability |
| --- | --- |
| [2610.00548](https://arxiv.org/abs/2610.00548), A polynomial-time classical sampler for noisy quantum circuits from statistical mechanics | [Theorem 1.1; Appendix B](https://arxiv.org/html/2610.00548v1): geometrically local unital two-qubit layers with depolarizing noise after every layer; depth threshold `O(p^-1*log(p^-1))`, with inverse-polynomial output error. Polymer expansion and hypercontractivity provide algorithmic methods under that noise regime. Neither a Wilson polymer-activity estimate nor the same OS dynamics is supplied. |
| [2610.01190](https://arxiv.org/abs/2610.01190), Rapid mixing of quantum spin chains at any finite temperature | [Theorem 1.1; equation (3); Proposition 2.9](https://arxiv.org/html/2610.01190v1): bounded finite-range one-dimensional spin Hamiltonians, fixed finite beta/local dimension, and Petz block-recovery dynamics. Block length is independent of n and mixing time is `O(log(n/epsilon))`; constants depend on the fixed parameters. A four-dimensional Wilson family is not this one-dimensional sampler; extending transverse size changes the hidden constants and requires proof. |
| [2610.01987](https://arxiv.org/abs/2610.01987), On the Metastability of the Mean-Field Interchange Model for Local Dimension >= 3 | Abstract-level screen only: a Davies gap for a mean-field model and specified Pauli bath is exponentially small in n between `beta_min(d)` and d, and inverse-polynomial outside. Schur–Weyl sector separation is a method; neither inverse-polynomial mixing nor thermal-bath metastability supplies the physical Yang–Mills mass. No theorem anchor is claimed. |

### Intrinsic observable algebra

[2610.01622](https://arxiv.org/abs/2610.01622), Yoshitsugu Sekine,
*The Buchholz Algebra from the Universal Resolvent Algebra—Particle Structure,
Gibbs States, and Closed-Path Expansions without Fock Representations*.
[Theorem 2.8 and Remark 3.3](https://arxiv.org/html/2610.01622v1) expose extra
particle-block, injective compression, compatibility and reconstruction data;
the universal algebra does not itself provide them. Theorems 2.9–2.11 assume
corner-dimension growth, superstability and summability to construct Gibbs
states, a trace-norm product limit and closed paths. Reflection positivity
requires extra positivity/reflection conditions. Here gauge fixing refers to
the CCR particle-number phase action, not a constructed compact-simple-group
Yang–Mills Gauss law.

Inference: useful discipline for a SAME-algebra inverse-limit construction.
It does not fill our continuum observable/OS identification or spectral
estimate; the explicit additional hypotheses need actual constructive
producers before any transfer.

### Polynomial roots and certificates

[2610.02035](https://arxiv.org/abs/2610.02035), Teng Zhang,
*Borcea's 2-variance conjecture*.
[Theorem 1.2 and Appendix B](https://arxiv.org/html/2610.02035v1) concern the
spread of polynomial zeros and their distance to critical points. Its rational
subdivision, whole-box coverage, degree coverage and directed treatment of
favorable negative terms are useful certificate patterns. This variance is
not variance under the interacting field measure.

The [author's formalization README](https://github.com/zhangteng2000/Borcea-2-variance-conjecture-Lean-4)
reports typed-tree coverage and `decide +kernel` exact acceptance, but also
explicitly pins Mathlib and reports `Classical.choice` in the main theorem's
axiom closure. That library is not an admissible direct dependency under this
repository's constructive contract. These are inspected author reports,
not an independent build/axiom audit by this reviewer. Any adapted certificate
must be independently parsed and kernel-checked within our existing gate.

## Consequence for the proof path

The most concrete new planning lesson is to retain squared norm loss before
composition (01121), track interacting moment constants through every limit
(00453), and make algebra compatibility inputs explicit (01622). Their needed
original-model identifications and uniform estimates remain unproved.
Keep the existing active-channel budget on the original source, partition and
OWN variance; the next result must bound the combined signed costs with useful
physical-scale dependence. No reviewed paper supplies that input, no external
theorem was installed as a premise, and no Clay proof-status node closes.
