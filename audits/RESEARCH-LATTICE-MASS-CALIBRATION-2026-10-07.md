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
