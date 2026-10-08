# Lattice mass measurements and the proof target (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4, every compact simple group, SAME-theory QFT axioms and
a finite positive physical Hamiltonian mass gap.

Targeted review of the user's pasted lattice-measurement note, not a routine
math-ph listing scan. The latest cached listing scan remains 2026-09-30
03:38 UTC. No sampling result is imported as a Lean premise.

Targeted primary-source reread, 2026-10-08 UTC: the Athenodorou--Teper
SU(3) scalar entry, Creutz's temporal-spacing limit and the official
Jaffe--Witten target were rechecked. The corrections and existing proof-plan
interfaces below are retained; no new analytic hypothesis or roadmap box.

Attachment reconciliation, 2026-10-08 05:31 UTC: the newly supplied
`cf965d8e-085c-42c2-a303-16f0ae70d860/Pasted text.txt` repeats the chain already
reviewed here. Reuse these corrections; no new literature fetch or numerical
premise. Continue with the actual SAME-source relative response budget; the
new full-cost/filtering screen is recorded in the adaptive-score audit.

## Useful distinctions, with corrections

1. Keep a glueball-channel measurement separate from a theory-wide spectral
   gap. Morningstar--Peardon, section II, describes asymptotic decay for the
   lowest state created by the chosen operator; states with zero overlap
   are not excluded. Its section VI/Table 7 gives the scalar estimate
   1730(50)(80) MeV using r0^-1=410(20) MeV. This verifies the rough 1.7 GeV
   scale-set estimate, not the note's attribution of m/sqrt(string tension)
   approximately 3.9 to that paper: **NOT FOUND** in the inspected text.
   The primary dimensionless result there is r0*m=4.21(11)(4).
   Dividing its MeV estimate by an independently chosen 440 MeV does not
   produce its measured string-tension ratio. Athenodorou--Teper (2021),
   Table 34, instead reports SU(3) m0++/sqrt(sigma)=3.405(21).
   Keep these reference scales separate; neither result fixes a required
   numerical mass for the Clay theorem.
   Neither that number nor its extrapolation is a kernel certificate.
   [Primary paper, sections II and VI](https://arxiv.org/html/hep-lat/9901004).
   [Athenodorou--Teper, continuum tables](https://arxiv.org/html/2106.00364v2).
2. Preserve physical time normalization. An exact discrete-time generator,
   when its logarithm/domain is constructed, is -log(T)/a_t. Do not identify
   it at finite a_t with the standard Kogut--Susskind electric-plus-magnetic
   Hamiltonian: Creutz extracts that Hamiltonian by taking a_t to zero.
   The regulator limit and SAME-action/operator identification must be proved,
   including conventions for one-step versus two-step time.
   [Creutz, abstract](https://doi.org/10.1103/PhysRevD.15.1128).
3. Do not prescribe W^{1,p} convergence of quantum sample connections from a
   smooth Riemann-sum heuristic. Cao--Chatterjee works with distributional
   gauge orbits and regularized Wilson observables; sections 1.5 and 1.9
   distinguish this state-space construction from constructing a nonabelian
   3D Euclidean Yang--Mills measure. It does not supply the note's claimed
   general 2+1D continuum Hamiltonian with a gap. No such input is adopted.
   [Primary state-space paper](https://doi.org/10.1007/s00220-023-04870-y).
   A targeted primary-source check on 2026-10-08 UTC also inspected
   Chandra--Chevyrev--Hairer--Shen, *Stochastic quantisation of Yang--Mills--Higgs
   in 3D* (Invent. Math. 237, 2024), accepted manuscript section 1.2, printed
   pages 7--8: whether its constructed process admits an invariant measure
   remains an explicitly open problem. Its local renormalized dynamics do
   not justify importing a general 2+1D gapped OS/Hamiltonian construction.
   [Accepted primary manuscript, section 1.2](https://www.pure.ed.ac.uk/ws/portalfiles/portal/435998276/YangMills.pdf).
4. The limiting gap must refer to the Hamiltonian of the constructed limiting
   theory. We do not define it to be liminf of finite-volume fitted masses,
   or use an area law as the missing spectral-limit theorem. These are
   different requirements; the official problem asks for existence and a
   positive spectral gap, including the limiting-theory/QFT obligations.
   This is a scope restriction on our proof route, not an imported theorem
   equating or separating all possible confinement criteria.
   [Official Jaffe--Witten specification, sections 3--4](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf).

## Effect on the forward/backward work plan

Numerical channel masses may guide observable selection and sanity checks,
but cannot replace nontrivial survival or an every-state bound. Work backward
from the SAME limiting Hamiltonian and calibrated physical time; work forward
with the original action, partitions and transfer. The intermediate joins
remain proof obligations, not consequences of a fitted lattice exponential.
The SU(3) measurement does not instantiate the current SU(2) quaternion
carrier, prove a result for every compact simple group, or prescribe a GeV
value that Clay requires us to reproduce.

Reuse the existing conditional exact-rate interfaces rather than add a new
measurement-driven one: `lean/YMGap/Continuum/PhysicalRateBridgeExactLog.lean:34`,
`exactLogRateFamily`, and `lean/YMGap/Continuum/OSExactLogGap.lean:121`,
`ExactLogGapAt`. They require supplied rate/reconstruction identifications;
they do not construct those missing inputs. The active original-family
two-sided margin input remains
`lean/YMGap/Continuum/BF4WilsonAllNomeGenericNormalizedAnchor.lean:895`,
`PathPhysicalContractionBand`.

No Sobolev regularity, measured GeV value, area-law-to-gap inference or
finite-spacing Kogut--Susskind equality is added to a hypothesis bundle.
The genuine interacting-energy estimate, independent AF survival, actual
all-vector comparison, physical/volume control and SAME limiting QFT remain
the work. No chart claim changes from this research review.

## Concrete source-family lead: spatial-only smearing (2026-10-08 UTC)

Targeted primary-source screen, not a new listing scan. Sakai--Sasaki,
sections II.A--B, explains that four-dimensional flow mixes temporal support;
equations (3)--(4) instead evolve only spatial links using spatial plaquettes.
This is a numerical spectroscopy method, not a constructive continuum
existence or nonzero-overlap theorem. Lohmayer--Neuberger, section 6, likewise
distinguishes spatial-only Hamiltonian smearing from spacetime smearing;
section 4 discusses the regulated perimeter term. We do NOT import its
four-dimensional finiteness assertions as a proved spatial-flow input.
[Sakai--Sasaki, sections II.A--B](https://arxiv.org/html/2211.15176).
[Lohmayer--Neuberger, sections 4 and 6](https://arxiv.org/html/1110.3522).

Independent read-only source map found a usable EXISTING carrier, not a
smearing producer:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonProbe.lean:44`,
  `SourceLoop`, certifies ordered, compatible, closed SAME-base-link paths.
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:49`,
  `WindowExpression`, accepts signed finite sums/products. Offset zero and
  `source_supported:124` give one-slice polynomial support;
  `expression_pin:172` and `placed_ledger_invariant:232` join the actual
  slab placement, not a new action.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:123`,
  `originalWindowScalar_pin`, retains original normalization/transfer.
  `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:152`,
  `centeredExcitation`, constructs its actual completed centered vector;
  `centeredVector_time_pairing:159` and `centeredVector_diagonal:167`
  pin its responses and norm.
- `lean/YMGap/Continuum/BF4WilsonAllNomeExprAnchorTrajectory.lean:235`,
  `ExprAnchorTrajectory`, accepts an explicit scale-dependent expression.
  `ExprHVar:267`, `ExprHRay:273`, and `ExprShiftedWindowSurvival:291`
  are OPEN inputs for the new source. Its radius is temporal box smoothing,
  not spatial link flow. The smoothed-loop comment at line 40 constructs
  nothing; no such constructor was found in these modules.

Plan use: investigate spatial-only original-algebra approximants only when
actual paths/weights and approximation moduli can be supplied, followed by
their OWN completed norm/Rayleigh and window bounds. A finite Wilson mixture
is not automatically a flowed link; unitary nonlinear projection or flow
requires its own certified approximation. Do not reuse square-source floors
for a changed source, change the original action, or claim continuum survival
from operator smearing. The signed interacting estimate remains primary.

### Source reconciliation: observable profiles versus link flow

2026-10-08 UTC, independent read-only source reviews and root inspection;
no additional literature scan, Lean edit or compiler run. The general
expression inputs above must not obscure existing source-specific producers:

- `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:140`,
  `centered_norm_floor`, already gives the original Wilson connected-moment
  floor varianceFloor(w)*sum(c_p^2) for an arbitrary signed family of physical,
  nonrepeated spatial plaquettes. `familyExcitation_norm_floor:151` joins it
  to the actual completed vector; `familyExcitation_correlator_pin:187`
  retains the SAME completed time operator. Positive norm additionally needs
  sum(c_p^2)>0, as in `familyExcitation_norm_ne_zero:162`; physical/Nodup
  guards alone allow all-zero coefficients. This permits spatial profiles
  of plaquette OBSERVABLES now. The constant depends on strict nome; neither
  a useful changing-family Rayleigh bound nor window survival follows.
- `lean/YMGap/Continuum/BF4ExactSlabWilsonWordVariance.lean:142`,
  `normalizedVariance_floor`, retains the actual selected-action mean and
  gives starRatio(w)*(1+m^2). `finiteValue_variance_floor:196` supplies the
  weaker starRatio(w) bound at every regulator stage for a physical word
  with a forward selected head link absent from its tail. The physical,
  nonrepeated action-face list stays explicit. This is already a general
  finite word producer, not merely a plaquette/square example.
- `lean/YMGap/Continuum/BF4ExactSlabSpatialWilsonRectangle.lean:38`,
  `rectangleEdges`, and `rectangle:47` supply a concrete closed six-link
  spatial word; `no_coefficient_plaquette_recoding:121` is a pointwise
  algebra distinction, not a variance or scaling theorem. A new source-loop
  specialization/limit join would still need proof. It is not selected just
  to obtain another fixed-nome nondegeneracy example.

The eligible simpler alternative is therefore an EXPLICIT signed spatial
plaquette profile using those existing constructors and floors. Its unpaid
task is a useful original-action FILTERED cost/window estimate with all cross
terms and OWN means, not its source representation or unfiltered positive
variance. No such estimate was produced in this review. Individual word
floors are not a variance floor for an arbitrary word mixture. Actual
staple-averaged/flowed unit-link construction and its unit, gauge, support,
approximation and survival joins remain absent from the inspected source
modules. Do not identify an observable profile with link flow.
