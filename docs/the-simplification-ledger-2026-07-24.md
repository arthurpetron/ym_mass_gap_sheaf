# The Simplification Ledger

**Named-result genealogy and counterfactual impact audit for the Yang--Mills
mass-gap program**

Date: 2026-07-24

## 0. Scope, method, and a necessary warning

This is a dependency audit, not a claim that the Yang--Mills mass-gap problem
has been solved.  The terminal theorem is still the shared-object theorem in
`ClayTargetPinned`: for every compact simple \(G\), construct one nontrivial
four-dimensional continuum Yang--Mills theory, reconstruct its physical
Hilbert space and Hamiltonian, and prove
\(\operatorname{spec}H\cap(0,\Delta_G)=\varnothing\) for some
\(\Delta_G>0\).

Here “we are using” means that a human-eponymous theorem, law, construction,
identity, transform, expansion, criterion, or strategic comparison occurs on
the repository's live mathematical route.  The census covers:

- the BF1--BF10 route in
  `docs/birkhoff-fusion-clay-closure-plan-2026-07-24.md`;
- the four live formal chains identified in `docs/continuum-map.md`;
- the continuum and Clay boundary in `docs/clay-open-boundary-ledger.md`;
- the exact dual-positivity, recoupling, Core-B, cluster, and finite-category
  campaigns in `notes/`, `computations/`, `tests/`, and `lean/YMGap/`.

An eponym found only in an archive, bibliography, historical aside, or
abandoned route is not called load-bearing.  Strategic comparisons are
included but explicitly labelled.  Generic operations such as induction,
finite summation, and ordinary polynomial arithmetic are omitted unless the
repository invokes a named theorem or identity.

The historical relation “led to” is interpreted as **mathematical ancestry**:
the older body supplies concepts or results needed by the newer one.  It is
not an exclusive priority claim.  History branches, and the same older work
can support several later results.

### Status key

| Mark | Meaning |
|---|---|
| **T** | terminal target or defining physical framework |
| **D** | directly used in a proved repository result or live proof interface |
| **F** | frontier machinery proposed for a currently open gate |
| **I** | structural inspiration; no theorem transferring it to 4D gauge duals |
| **C** | comparator/no-go route; useful because its failure localizes the wall |
| **S** | mathematical substrate used inside certificates |

## 1. Result first: ranked net effect on this project

The counterfactual audit produces a sharp ranking.

1. **Retain the full positive Haar-network boundary tensor through blocking.**
   The largest avoidable loss occurs when a positive group integral is
   expanded into signed fixed-face channels, and then reduced again to
   multiplicity vectors.  Undoing both quotients means carrying boundary
   intertwiners, fusion-tree bases, phases, and reflected Gram data.  This is
   the most plausible route to the missing BF1--BF4 positive carrier and exact
   block map.

2. **Retain the scale dependence and group over fixed physical distance.**
   Requiring one microscopic contraction \(q<1\) independent of the spacing is
   stronger than the continuum physics permits.  The correct target is
   \(q_a=1-ma+o(a)\), whose product across distance \(L\) is
   \(e^{-mL}\).  This changes the statement of BF4, and therefore RG-I7--I9,
   from an apparently impossible per-step estimate to a dimension-free
   grouped Birkhoff estimate.

3. **Keep one physical object from Gibbs pushforward through OS
   reconstruction.**  The repository has many genuine finite witnesses, but
   different witnesses cannot be assembled into the Clay theorem merely
   because each inhabits an analogous interface.  Not simplifying the
   measure to a functional shell, clustering to a finite transfer model, or
   covariance to the identity rotation would force the actual common
   continuum object to be constructed.  This does not make BF7--BF10 easier;
   it prevents a false closure and identifies the remaining Clay content.

4. **Keep the complete 4D intersection geometry.**  Single binary surfaces
   reduce to 2D Yang--Mills and are positive; Migdal--Kadanoff and other
   hierarchical reductions also erase joint coarse intertwiners.  Preserving
   intersections, branching, and fusion-path multiplicity is precisely where
   dual positivity and the physical RG can live.

5. **Keep exact physical activities inside the cluster/RG step.**  Replacing
   the Gibbs law by a multiplicity-product surrogate or an abstract polymer
   majorant proves convergence only for the surrogate.  Propagating the
   unsimplified activities would turn the existing Penrose/KP and Bałaban
   architecture into an actual RG-I7--I9 result, if the needed bounds hold.

6. **Retain per-group representation and heat-kernel data.**  The formal
   “SU(2) worst case” reduction is conditional on monotonicity interfaces that
   the physical carrier has not supplied.  Carrying each compact simple group
   is more work, but it is the safe BF9 route and exposes any group-specific
   failure of positivity or diameter control.

7. **Use finite tensor categories only as local coherence envelopes.**
   Refusing the simplification from full maps to the Grothendieck ledger is
   useful; refusing the \(SU(2)_k\) truncation itself is also necessary for the
   continuum.  The resulting lesson is negative but valuable: Ocneanu
   rigidity does not provide a cutoff-uniform cone, and the central vacuum
   carrier grows like \(k+1\).

8. **Restore complete heat-kernel tails and signed recoupling before claiming
   uniformity.**  Low-spin and squared-\(6j\) certificates are exact where
   stated, but they cannot decide the all-label carrier or coherent block map.
   Tail bounds and signed \(F/R\)-symbol identities are required.

The rest of the ledger records why these eight conclusions follow.

---

# Part I. Lists A--E

## 2. List A — named results presently used

List A is keyed by the human or humans conventionally attached to the result.
The “parents” column points into List B, so every row has a recursive route.

| ID | Human key | Named work used here | Status and exact role | List-B parents |
|---|---|---|---|---|
| A01 | **Chen Ning Yang; Robert Mills** | Yang--Mills gauge theory, action, and equations | **T.** Defines the theory to be constructed. | B01, B06 |
| A02 | **Kenneth Wilson** | Wilson lattice action, Wilson loops, lattice gauge theory, and Wilsonian RG | **D/T.** Regulated Gibbs law and gauge-invariant observables; also the scale architecture. | B01, B11 |
| A03 | **Arthur Jaffe; Edward Witten** | Yang--Mills existence and mass-gap problem | **T.** Fixes the all-groups, nontriviality, axiomatic-QFT, and positive-gap quantifiers. | B01, B02, B03 |
| A04 | **Lars Gårding; Arthur Wightman** | Gårding--Wightman/Wightman axioms | **D/T.** Required strength of the reconstructed continuum QFT. | B02 |
| A05 | **Konrad Osterwalder; Robert Schrader** | Osterwalder--Schrader axioms and reconstruction | **D/T.** Euclidean route to the physical Hilbert space and Hamiltonian. | B02, B03 |
| A06 | **Konrad Osterwalder; Erhard Seiler** | reflection positivity for lattice gauge theories | **D.** The repository's heat-kernel/character OS2 diagonalization route. | B03, B20 |
| A07 | **Israel Gelfand; Mark Naimark; Irving Segal** | GNS construction | **D.** Positive functional \(\rightarrow\) cyclic Hilbert-space representation. | B02, B04 |
| A08 | **Marshall Stone; Einar Hille; Kôsaku Yosida** | Stone generator theorem and Hille--Yosida semigroup theory | **D/F.** Identifies positive-time translations with a Hamiltonian once the continuum semigroup exists. | B04 |
| A09 | **Gunnar Källén; Harry Lehmann** | Källén--Lehmann spectral representation | **F.** Intended same-object bridge from Euclidean decay to exclusion of low spectral mass. | B04, B21 |
| A10 | **Percy Daniell; Andrey Kolmogorov** | Daniell--Kolmogorov extension/consistency theorem | **D/F.** Functional inverse-limit structure is present; the actual Yang--Mills measure remains open. | B05 |
| A11 | **Frigyes Riesz; Andrey Markov; Shizuo Kakutani** | Riesz--Markov--Kakutani representation theorem | **D/F.** Positive functionals to regular Borel measures in the compact/projective construction. | B05 |
| A12 | **Salomon Bochner; Robert Minlos** | Bochner--Minlos theorem | **F.** Quarantined classical route from characteristic functionals to measures on distribution spaces. | B05 |
| A13 | **Yuri Prokhorov** | Prokhorov compactness theorem | **F.** Tightness/subsequence tool for continuum measures; no physical uniform modulus is yet supplied. | B05 |
| A14 | **David Gross; Frank Wilczek; H. David Politzer** | asymptotic freedom of nonabelian gauge theory | **D/T.** One-loop sign is formalized; the true nonperturbative UV limit remains a BF7 condition. | B06, B11 |
| A15 | **Alfréd Haar** | invariant Haar measure | **D.** Exact link integration and the native positive compact-group Gibbs representation. | B07 |
| A16 | **Fritz Peter; Hermann Weyl** | Peter--Weyl theorem | **D.** Character/matrix-coefficient expansion of heat kernels and link integrals. | B07, B21 |
| A17 | **Issai Schur** | Schur lemma and Schur orthogonality | **D.** Link-channel collapse and reflection-positive sum-of-squares diagonalization. | B07, B20 |
| A18 | **Hermann Weyl** | character, integration, and dimension formulae | **D.** SU(2) exact integrator, heat tails, and all-group representation data. | B07, B08 |
| A19 | **Hendrik Casimir** | quadratic Casimir operator/eigenvalues | **D.** Heat exponent, representation gap, and per-group spectral data. | B08, B23 |
| A20 | **Alfred Clebsch; Paul Gordan** | Clebsch--Gordan decomposition and coefficients | **D.** Face fusion, parity/triangle rules, and intertwiner multiplicities. | B09 |
| A21 | **Eugene Wigner; Giulio Racah** | \(3nj\), \(6j\), Racah \(W\), and recoupling/orthogonality formulae | **D/F.** Exact signed recoupling; squared kernels are proved only where stated. | B09 |
| A22 | **Leonard Biedenharn; John Elliott** | Biedenharn--Elliott pentagon identity | **D/F.** Required coherent reassociation; general signed identity remains a named frontier in parts of the formal chain. | B09, B15 |
| A23 | **Élie Cartan; Wilhelm Killing; Eugene Dynkin; Harold Coxeter** | root systems, Dynkin diagrams, Coxeter/Weyl data, classification of compact simple Lie types | **D/F.** Finite type enumeration exists; physical all-group monotonicity is conditional. | B08, B22 |
| A24 | **Josiah Willard Gibbs; Ludwig Boltzmann** | Gibbs measure/state and Boltzmann weight | **T/D.** The exact lattice law whose pushforward must be blocked, not a surrogate law. | B10 |
| A25 | **Julius Mayer; Harold Ursell** | Mayer expansion and Ursell connected functions | **D/F.** Connected polymer reorganization; the real multi-plaquette identity is the live D1 wall. | B11 |
| A26 | **Arthur Cayley** | Cayley tree formula | **S.** Entropy/counting factor in tree and polymer majorants. | B24 |
| A27 | **Oliver Penrose** | Penrose tree-graph identity/inequality | **D/F.** Controls signed connected graphs by trees; physical activity identification is still required. | B11, B24 |
| A28 | **David Brydges; Paul Federbush** | Brydges--Federbush tree/Mayer formula | **D/F.** Quantitative cluster majorant used with small-field activities. | B11 |
| A29 | **Roman Kotecký; David Preiss** | Kotecký--Preiss abstract-polymer convergence criterion | **D/F.** Volume-uniform cluster convergence after physical activities meet its hypothesis. | B11 |
| A30 | **Roland Dobrushin** | Dobrushin uniqueness/comparison and polymer criteria | **D/F.** Ratio/uniqueness architecture; physical step ratio remains nontrivial. | B11 |
| A31 | **Tadeusz Bałaban** | constructive lattice-gauge renormalization group and large-/small-field expansion | **D/F.** Governs the intended exact physical RG; current constants include explicitly labelled fiducials and uninhabited steps. | B11, B12 |
| A32 | **David Hilbert** | Hilbert projective metric | **F.** Proposed metric for dimension-free contraction of positive dual activities. | B13 |
| A33 | **Garrett Birkhoff; Eberhard Hopf** | Birkhoff--Hopf contraction theorem | **F.** Candidate BF4 engine; no physical finite-diameter carrier has yet been constructed. | B13 |
| A34 | **Oskar Perron; Ferdinand Frobenius** | Perron--Frobenius theorem | **D/F.** Finite positive-transfer intuition and proposed graded positive-sector control. | B13, B21 |
| A35 | **Mark Krein; Mikhail Rutman; Stefan Banach** | Krein--Rutman positive-operator theorem and Banach contraction principle | **F/S.** Infinite-dimensional and fixed-point ancestry of the proposed contraction argument. | B13 |
| A36 | **Pafnuty Chebyshev; Carl Jacobi** | Chebyshev polynomials/orthogonality; Jacobi theta identities and triple product | **D.** SU(2) character coordinates and exact Core-B/theta positivity certificates. | B14, B21 |
| A37 | **Sergei Bernstein; Jacques Sturm; Andrey Markov; Gyula Lukács** | Bernstein basis positivity, Sturm chains, and Markov--Lukács interval positivity | **D/S.** Exact polynomial sign certificates and fallback decision procedures. | B14 |
| A38 | **Semyon Gershgorin** | Gershgorin circle theorem | **D/S.** Finite/minor spectral-margin bounds in the Core-B chain. | B14, B21 |
| A39 | **Siméon Denis Poisson; Leonhard Euler; Colin Maclaurin** | Poisson summation and Euler--Maclaurin formula | **D/C.** Theta/local-CLT comparison tools; exact Poisson inversion was later eliminated from one live tail. | B14, B21 |
| A40 | **Vladimir Drinfeld; Alexei Davydov; David Yetter; Adrian Ocneanu; Pavel Etingof; Dmitri Nikshych; Viktor Ostrik** | Drinfeld center/central Hopf monad, Davydov--Yetter cohomology, Ocneanu rigidity, fusion-category rigidity | **D/C/F.** Exact finite \(SU(2)_k\) audit; a coherence envelope, not the positive cutoff-uniform carrier. | B15 |
| A41 | **Heinrich Maschke; Ferdinand Frobenius; Oskar Perron** | Maschke semisimplicity, Frobenius reciprocity, and Frobenius--Perron dimension | **D/S.** Degree-zero/module comparison and finite fusion algebra. | B07, B15 |
| A42 | **Mark Kac; John Ward; Pieter Kasteleyn; Lars Onsager** | Kac--Ward and Kasteleyn sign absorption/Pfaffians; Onsager solution | **I.** Motivates searching for a higher-dimensional coherence/orientation absorbing dual signs; no 4D gauge theorem follows. | B16 |
| A43 | **Alexander Migdal; Leo Kadanoff; Boris Rusakov; Edward Witten** | Migdal--Kadanoff recursion and exact 2D Yang--Mills/Migdal formula | **D/C.** 2D formula proves single-surface positivity; MK is a structural comparator and does not equal the 4D physical pushforward. | B12, B17 |
| A44 | **Joseph Fourier; Marc-Antoine Parseval; Michel Plancherel** | Fourier analysis, Parseval identity, Plancherel theorem | **D/S.** Character/Fourier reconstruction and norm identities. | B21 |
| A45 | **Guido Fubini; Leonida Tonelli; Pierre Fatou; Augustin Cauchy; Hermann Schwarz; Otto Hölder; Johan Jensen; Thomas Grönwall; Karl Weierstrass** | interchange, convergence, norm inequalities, Grönwall iteration, and infinite-product convergence | **S.** Certificate-level analytic substrate; never supplies the missing physical uniform constants. | B18 |
| A46 | **Errett Bishop; Ernst Specker** | constructive analysis and Specker obstruction | **D/S.** Located/Cauchy-modulus policy and the reason arbitrary monotone limits are not silently admitted. | B19 |
| A47 | **Jørgen Pedersen Gram; James Joseph Sylvester** | Gram matrices/sum of squares and Sylvester positivity criteria | **D/F.** Reflection/frozen-hub positivity and candidate carrier geometry. | B20 |
| A48 | **Werner Heisenberg; Pascual Jordan; Wolfgang Pauli; Paul Dirac** | angular-momentum quantum algebra underlying spin networks | **S.** Physical and algebraic ancestry of SU(2) spin coupling. | B09 |
| A49 | **Paul Turán; Thomas Joannes Stieltjes; Carl Severin Wigert; Elwin Christoffel; Pierre Desnanot; Carl Jacobi** | Turán inequalities, Stieltjes--Wigert moment systems, Christoffel transforms, and Desnanot--Jacobi determinant identity | **D/S.** Core-B log-concavity, \(q\)-Hankel, and determinant certificates; some routes are structural and others were superseded. | B14 |
| A50 | **Ludwig Saalschütz; John Dougall; Doron Zeilberger** | terminating hypergeometric summation and creative telescoping | **D/F.** Exact Racah-sum reductions and the still-guarded coupled recurrence route. | B09, B14 |
| A51 | **Dominique Bakry; Michel Émery** | Bakry--Émery curvature criterion | **D/C.** A genuine free heat-kernel curvature anchor and a documented no-go for the required 4D continuum functional form. | B13, B23 |
| A52 | **Elliott Lieb; Barry Simon; Derek Robinson; Matthew Hastings; Tohru Koma** | Simon--Lieb, Lieb--Robinson, and Hastings--Koma correlation/gap bounds | **C.** Comparison routes clarifying the hypotheses needed to transport clustering and gaps; not a physical-Yang--Mills closure. | B04, B21 |

### List-A exclusions that prevent overclaiming

The repository also discusses Schwinger--Dyson, Wetterich, BRST/Krein-space,
instanton, higher-dimensional continuation, and several hierarchical routes.
They are not List-A dependencies of the current BF critical path.  They are
retained as conditional interfaces or documented no-gos.  Bakry--Émery and
the Simon--Lieb/Lieb--Robinson/Hastings--Koma family *are* listed because
specific proved or diagnostic repository results invoke them, but their
status is **C**, not a claimed path to the terminal theorem.

## 3. List B — immediate bodies of work behind List A

Each row is keyed by its principal humans, names all List-A children, and
points to List C.  This is the first recursive expansion.

| ID | Human key | Body of work that led to the List-A items | List-A children | List-C parents |
|---|---|---|---|---|
| B01 | **Maxwell; Weyl; Yang; Mills; Wilson** | Gauge covariance: Maxwell's field equations, Weyl's gauge principle, nonabelian connections/curvature, and Wilson's compact lattice regularization. | A01--A03 | C01, C07, C16 |
| B02 | **Wightman; Gårding; Haag; Kastler; Gelfand; Naimark; Segal** | Axiomatic and algebraic QFT: fields/distributions, covariance, locality, positivity, vacuum, local observable algebras, and cyclic representations. | A03--A05, A07 | C02, C03 |
| B03 | **Symanzik; Nelson; Osterwalder; Schrader; Seiler** | Euclidean QFT: Markov fields, reflection positivity, analytic continuation, and lattice-gauge reflection arguments. | A03, A05, A06 | C02, C04, C20 |
| B04 | **Hilbert; Stone; Hille; Yosida; Källén; Lehmann** | Spectral/semigroup theory: self-adjoint generators, positive semigroups, spectral measures, and spectral representations of two-point functions. | A07--A09, A52 | C03, C04, C21 |
| B05 | **Daniell; Kolmogorov; Riesz; Markov; Kakutani; Bochner; Minlos; Prokhorov** | Measure construction from positive functionals or compatible marginals, plus tightness/weak compactness. | A10--A13 | C05, C03 |
| B06 | **Yang; Mills; ’t Hooft; Gross; Wilczek; Politzer** | Perturbative renormalization of nonabelian gauge theories and the negative one-loop beta function. | A01, A14 | C01, C11 |
| B07 | **Haar; Frobenius; Schur; Peter; Weyl** | Harmonic analysis and representation theory of finite/compact groups: invariant integration, irreducible decomposition, characters, and orthogonality. | A15--A18, A41 | C06, C13 |
| B08 | **Lie; Cartan; Killing; Weyl; Casimir; Dynkin; Coxeter** | Structure and classification of semisimple Lie algebras/groups, roots/weights, Weyl groups, and invariant quadratic operators. | A18, A19, A23 | C07 |
| B09 | **Clebsch; Gordan; Heisenberg; Jordan; Pauli; Wigner; Racah; Biedenharn; Elliott** | Quantum angular momentum, tensor-product decomposition, recoupling coefficients, hypergeometric formulae, orthogonality, and pentagon coherence. | A20--A22, A48, A50 | C06, C08, C14 |
| B10 | **Boltzmann; Gibbs; DLR school** | Equilibrium statistical mechanics: normalized exponential weights, finite-volume Gibbs laws, conditional specifications, and thermodynamic limits. | A24 | C09, C05 |
| B11 | **Mayer; Ursell; Penrose; Brydges; Federbush; Kotecký; Preiss; Dobrushin** | Connected-graph and polymer expansions, tree domination, and volume-uniform convergence/uniqueness criteria. | A25, A27--A30 | C09, C10 |
| B12 | **Kadanoff; Wilson; Migdal; Bałaban** | Block-spin/coarse-graining ideas, hierarchical/bond-moving approximations, and rigorous multiscale effective-density analysis. | A31, A43 | C11, C09 |
| B13 | **Hilbert; Birkhoff; Hopf; Perron; Frobenius; Krein; Rutman; Banach; Jentzsch** | Ordered cones, projective metrics, positive eigenvectors/operators, and contraction/fixed-point theory. | A32--A35, A51 | C03, C12 |
| B14 | **Chebyshev; Jacobi; Poisson; Euler; Maclaurin; Bernstein; Sturm; Markov; Lukács; Gershgorin; Turán; Stieltjes; Wigert; Christoffel; Desnanot; Saalschütz; Dougall; Zeilberger** | Special functions, theta transforms, moment determinants, polynomial approximation/positivity, root counting, hypergeometric summation, local asymptotics, and spectral enclosures. | A36--A39, A49, A50 | C08, C13 |
| B15 | **Eilenberg; Mac Lane; Drinfeld; Davydov; Yetter; Ocneanu; Etingof; Nikshych; Ostrik** | Monoidal coherence, centers/coends, deformation cohomology, semisimple tensor categories, and rigidity. | A22, A40, A41 | C06, C14 |
| B16 | **Onsager; Kac; Ward; Kasteleyn; Arf; Cimasoni** | Exact planar Ising/dimer solution, non-backtracking determinants, Pfaffian orientations, and their reformulation by spin structures/quadratic refinements. | A42 | C10, C17 |
| B17 | **Migdal; Rusakov; Witten; Sengupta** | Exact two-dimensional Yang--Mills via heat-kernel convolution and representation sums weighted by dimension, Casimir, area, and Euler characteristic. | A43 | C07, C13, C16 |
| B18 | **Cauchy; Schwarz; Hölder; Jensen; Fubini; Tonelli; Fatou; Grönwall; Weierstrass** | Classical real/functional analysis for estimates, interchange of limits/integrals, and convergence of sums/products. | A45 | C05, C13 |
| B19 | **Brouwer; Bishop; Specker** | Constructive/intuitionistic analysis: witness-bearing existence, locatedness, moduli, and counterexamples to unqualified classical convergence principles. | A46 | C15 |
| B20 | **Gram; Schur; Osterwalder; Seiler; Sylvester** | Positive quadratic forms, Gram/SOS factorization, and reflected-kernel diagonalization. | A06, A17, A47 | C03, C06 |
| B21 | **Fourier; Parseval; Plancherel; Stone; Källén; Lehmann; Perron; Frobenius** | Orthogonal expansions and the identification of decay rates with spectral support/eigenvalue separation. | A09, A16, A34, A36, A38, A39, A44, A52 | C03, C13 |
| B22 | **Cartan; Killing; Dynkin; Coxeter; Weyl** | Finite classification and tabulation of compact simple Lie types and their representation invariants. | A23 | C07 |
| B23 | **Fourier; Laplace; Beltrami; Casimir; Peter; Weyl** | Heat semigroups on compact groups and character expansions with Casimir eigenvalues. | A19, A51 | C13, C16 |
| B24 | **Euler; Cayley; Kirchhoff; Penrose** | Graph/tree combinatorics: connected graphs, labelled trees, spanning trees, and graph-to-tree partition schemes. | A26, A27 | C10 |

## 4. List C — the second recursive expansion

| ID | Human key | Earlier body of work | List-B children | List-D parents |
|---|---|---|---|---|
| C01 | **Maxwell; Weyl; Yang; Mills; Noether** | Classical fields, local symmetry, connections, curvature, variational actions, and conserved currents. | B01, B06 | D01, D02 |
| C02 | **Einstein; Poincaré; Wigner; Gårding; Wightman; Haag; Kastler** | Relativistic symmetry and local quantum fields/observables. | B02, B03 | D02, D03 |
| C03 | **Hilbert; Banach; Riesz; von Neumann; Gelfand; Naimark** | Hilbert/Banach spaces, operator algebras, positive functionals, spectral theory, and ordered operators. | B02, B04, B05, B13, B20, B21 | D03 |
| C04 | **Wiener; Feynman; Kac; Nelson; Symanzik** | Path/Markov measures and Euclidean-time representations of quantum dynamics. | B03, B04 | D02, D05 |
| C05 | **Borel; Lebesgue; Daniell; Carathéodory; Radon; Riesz; Kolmogorov** | Measure, integration, extension, regularity, and probability on products/projective systems. | B05, B10, B18 | D05 |
| C06 | **Frobenius; Schur; Maschke; Burnside; Peter; Weyl** | Character theory, semisimplicity, induced/restricted representations, and compact-group decomposition. | B07, B09, B15, B20 | D04, D03 |
| C07 | **Galois; Lie; Klein; Cartan; Killing; Weyl** | Groups and continuous symmetries, Lie algebras, root systems, and invariant geometry. | B01, B08, B17, B22 | D04, D09 |
| C08 | **Euler; Gauss; Jacobi; Clebsch; Gordan; Racah** | Hypergeometric series, orthogonal polynomials, theta functions, and angular-momentum summation identities. | B09, B14 | D08 |
| C09 | **Bernoulli; Laplace; Boltzmann; Gibbs; Ising** | Probability, ensembles, partition functions, correlations, and lattice statistical mechanics. | B10--B12 | D05, D06 |
| C10 | **Euler; Cayley; Kirchhoff; Ising; Onsager; Penrose** | Graphs, planar topology, spanning trees, lattice models, and connected combinatorics. | B11, B16, B24 | D07 |
| C11 | **Kadanoff; Wilson; Callan; Symanzik; Gell-Mann; Low** | Scaling, running couplings, beta functions, and renormalization-group flow. | B06, B12 | D01, D06 |
| C12 | **Cayley; Klein; Hilbert; Birkhoff** | Cross-ratio/projective geometry and its order-cone metric realization. | B13 | D09 |
| C13 | **Fourier; Dirichlet; Sturm; Liouville; Parseval; Plancherel; Poisson** | Harmonic and spectral analysis, orthogonal series, transforms, and eigenfunction expansions. | B07, B14, B17, B18, B21, B23 | D08, D03 |
| C14 | **Noether; Eilenberg; Mac Lane; Hochschild; Drinfeld** | Abstract algebra, natural transformations, cohomology/deformation theory, and monoidal coherence. | B09, B15 | D04, D07 |
| C15 | **Brouwer; Heyting; Bishop; Specker** | Intuitionistic logic and constructive mathematics. | B19 | D10 |
| C16 | **Newton; Leibniz; Euler; Lagrange; Laplace; Beltrami** | Differential equations, variational calculus, Laplacians, and heat flow on manifolds. | B01, B17, B23 | D11, D09 |
| C17 | **Euler; Riemann; Poincaré; Arf** | Surface topology, homology/intersection forms, and quadratic refinements/spin structures. | B16 | D07, D09 |
| C20 | **Feynman; Kac; Schwinger; Osterwalder; Schrader** | Positivity/analytic-continuation formulations connecting Euclidean and quantum time. | B03 | D02, D05 |
| C21 | **Sturm; Liouville; Hilbert; Riesz; Stone** | Spectral theory from differential operators through abstract self-adjoint operators. | B04, B21 | D03, D11 |

## 5. List D — the third recursive expansion

| ID | Human key | Earlier body of work | List-C children | List-E parents |
|---|---|---|---|---|
| D01 | **Newton; Lagrange; Maxwell; Noether** | Variational field equations and symmetry/conservation laws. | C01, C11 | E01, E07 |
| D02 | **Planck; Einstein; Heisenberg; Schrödinger; Dirac; Wigner** | Quantum mechanics, relativistic covariance, and quantum fields. | C01, C02, C04, C20 | E02, E07 |
| D03 | **Hilbert; Banach; Riesz; von Neumann** | Linear/functional analysis, Hilbert spaces, operators, spectra, and topological vector spaces. | C02, C03, C06, C13, C21 | E05, E06 |
| D04 | **Galois; Cayley; Lie; Frobenius; Noether** | Abstract groups, continuous groups, representation theory, rings, and modules. | C06, C07, C14 | E03, E06 |
| D05 | **Bernoulli; Laplace; Borel; Lebesgue; Carathéodory; Kolmogorov** | Probability and measure-theoretic integration. | C04, C05, C09, C20 | E02, E04, E05 |
| D06 | **Boltzmann; Gibbs; Ising; Kadanoff; Wilson** | Statistical mechanics, critical phenomena, and scale dependence. | C09, C11 | E04, E07 |
| D07 | **Euler; Kirchhoff; Cayley; Riemann; Poincaré** | Combinatorics, graph theory, and topology. | C10, C14, C17 | E02, E08 |
| D08 | **Euler; Gauss; Fourier; Jacobi; Sturm; Liouville** | Special functions, harmonic analysis, and ordinary differential equations. | C08, C13 | E01, E02 |
| D09 | **Euclid; Gauss; Riemann; Klein; Hilbert; Cartan** | Geometry from metric/projective ideas to manifolds and connections. | C07, C12, C16, C17 | E02, E03, E06 |
| D10 | **Cantor; Brouwer; Heyting; Bishop** | Foundations, real-number constructions, and constructive logic. | C15 | E05, E06 |
| D11 | **Newton; Leibniz; Euler; Lagrange; Laplace** | Calculus, variational principles, PDEs, and diffusion. | C16, C21 | E01, E02 |

## 6. List E — the fourth recursive expansion and stopping roots

List E is the requested fifth list.  The recursion stops here because going
farther would become a genealogy of mathematics rather than a diagnostic of
this repository.  These roots are broad enough that “undoing a
simplification” no longer selects a concrete Yang--Mills carrier.

| ID | Human key | Root body of work | List-D children |
|---|---|---|---|
| E01 | **Isaac Newton; Gottfried Leibniz; Leonhard Euler; Joseph-Louis Lagrange** | Calculus, differential equations, and variational mechanics. | D01, D08, D11 |
| E02 | **Carl Friedrich Gauss; Joseph Fourier; Bernhard Riemann; Henri Poincaré** | Geometry, harmonic analysis, complex/real analysis, and topology. | D02, D05, D07--D09, D11 |
| E03 | **Évariste Galois; Arthur Cayley; Sophus Lie; Felix Klein** | Abstract and continuous symmetry. | D04, D09 |
| E04 | **Jacob Bernoulli; Pierre-Simon Laplace; Ludwig Boltzmann; Josiah Willard Gibbs** | Probability and statistical mechanics. | D05, D06 |
| E05 | **Georg Cantor; Richard Dedekind; Émile Borel; Henri Lebesgue; Constantin Carathéodory** | Sets, real numbers, measure, and integration. | D03, D05, D10 |
| E06 | **David Hilbert; Stefan Banach; Emmy Noether; Frigyes Riesz** | Abstract algebra and functional analysis. | D03, D04, D09, D10 |
| E07 | **James Clerk Maxwell; Max Planck; Albert Einstein; Werner Heisenberg; Erwin Schrödinger; Paul Dirac** | Classical fields, relativity, and quantum theory. | D01, D02, D06 |
| E08 | **Leonhard Euler; Gustav Kirchhoff; Arthur Cayley** | Graph invariants, networks, trees, and combinatorial enumeration. | D07 |

### Recursion completeness check

Every A row names at least one B parent; every B row names at least one C
parent; every used C row names at least one D parent; and every D row names
at least one E parent.  Branches merge where the mathematics genuinely
merges.  For example:

\[
\begin{aligned}
\text{Birkhoff--Hopf}
&\to \text{ordered/projective geometry}
\to \text{functional analysis + projective geometry}
\to \text{Hilbert/Banach and Gauss--Riemann roots},\\
\text{Biedenharn--Elliott}
&\to \text{angular momentum + monoidal coherence}
\to \text{representation theory + hypergeometric identities}
\to \text{group theory + harmonic analysis},\\
\text{Osterwalder--Schrader}
&\to \text{Euclidean QFT}
\to \text{Markov/path measures + axiomatic QFT}
\to \text{measure theory + quantum theory}.
\end{aligned}
\]

---

# Part II. The simplifications and their counterfactuals

## 7. What “simplification” means in this ledger

Not every arrow in Lists A--E is a simplification.  Some are
generalizations, syntheses, or changes of language.  The ledger below records
only reductions that occur in the mathematical route used by this
repository:

- **restriction:** smaller dimension, group, label range, volume, or sector;
- **truncation:** discard high representations, long polymers, or tails;
- **quotient/decategorification:** retain multiplicities but lose maps,
  bases, phases, or coherence;
- **linearization/expansion:** replace a positive nonlinear/group object by
  signed coordinates;
- **majorization:** replace the physical law by an upper-bound polymer or
  tree model;
- **object separation:** prove clauses on different witnesses instead of one
  common theory;
- **qualitative replacement:** use existence or a fiducial constant where a
  located uniform modulus is required.

## 8. The Simplification Ledger, ordered by net effect

The “counterfactual” column answers the user's question literally: what
changes if the simplification is not made and the richer object is propagated
all the way back up the A--E tree?

| Rank / ID | Simplification actually made | Where it appears in the genealogy and repo | If we do **not** simplify, and propagate the richer object upward | Net effect on the mass-gap program |
|---|---|---|---|---|
| **1 / S01** | **Positive Haar integral \(\rightarrow\) signed Peter--Weyl fixed-channel coefficients.** Coordinate expansion exposes negative \(6j\)/intertwiner terms even when the grouped physical amplitude is positive. | E02/E06 \(\to\) D03/D08 \(\to\) C06/C13 \(\to\) B07/B09 \(\to\) A15--A22. Exact negative fixed channels but positive complete pair activities are in `notes/fusion-pair-heat-census.md`. | Carry a boundary-tensor/reflected-Gram cone on which Haar integration remains a positive conditional expectation. Expand only after grouping a complete physical family. The BF1 carrier would be defined by positivity of the unsplit boundary object, not coefficientwise positivity in an arbitrary recoupling basis. | **Potentially decisive for BF1--BF4.** This is the strongest route to (DP), a physical positive block map, and finite projective diameter. It may also fail honestly if a complete physical family is negative. |
| **2 / S02** | **Intertwiner maps and \(F/R\) symbols \(\rightarrow\) fusion multiplicities/Grothendieck vectors.** | E03/E06 \(\to\) D04 \(\to\) C06/C14 \(\to\) B09/B15 \(\to\) A20--A22/A40--A41. The exact failure is documented in `notes/su2k-central-monad-campaign.md`. | Enrich each carrier element with a fusion tree, orthonormal intertwiner basis, signed/unitary \(F/R\) matrices, and coend counit/multiplication maps. The coarse map could then be tested as an actual central-module/comodule morphism rather than an equality of dimensions. | **Decisive for BF3.** It restores the joint coarse-intertwiner transport that the multiplicity carrier provably cannot encode. It increases dimension but removes a false positive from the finite-category route. |
| **3 / S03** | **Exact plaquette-coupled Haar Gibbs pushforward \(\rightarrow\) one-face fusion kernel or multiplicity-product surrogate.** | E04/E07 \(\to\) D06 \(\to\) C09/C11 \(\to\) B10/B12 \(\to\) A02/A24/A31/A43. | Integrate every fine internal link of the corrected slab with the actual boundary data and identify the normalized coarse Gibbs density plus a literal remainder. All subsequent KP/Birkhoff estimates would concern the same physical law. | **Necessary for BF3, BF5, and BF6.** It converts the present architecture into physical RG-I7--I9. It may reveal new signs or nonlocal interactions, but those are precisely the real wall. |
| **4 / S04** | **Physical-distance decay \(\rightarrow\) a spacing-independent contraction at every microscopic step.** | E06 \(\to\) D03 \(\to\) C12 \(\to\) B13 \(\to\) A32--A35. The corrected target is already stated in the BF plan. | Keep \(q_a=1-ma+o(a)\) and bound the product over \(L/a\) steps, including the graded distortion: \(\prod(q_a+C\kappa_a^{64})\le e^{-m_*L}\). Projective diameter may diverge per microscopic step while the grouped physical diameter remains effective. | **Decisive conceptual correction for BF4--BF6.** It aligns “uniform in cutoff” with a finite physical mass rather than an unrealistically strong lattice-scale gap. |
| **5 / S05** | **One shared continuum Yang--Mills object \(\rightarrow\) separate finite witnesses for OS axioms, clustering, nontriviality, covariance, and spectral data.** | E05--E07 \(\to\) D02/D03/D05 \(\to\) C02--C05/C21 \(\to\) B02--B05/B21 \(\to\) A03--A13. `ClayTargetPinned` was created to prohibit this separation. | Carry the exact RG trajectory into one limiting Schwinger functional/measure; prove OS0--OS4, locality, covariance, non-Gaussianity, and decay there; reconstruct one Hilbert space and identify its Hamiltonian spectrum. | **The entire BF7--BF10 content.** It does not shorten the problem, but it is the difference between a collection of reductions and a Clay solution. |
| **6 / S06** | **Full 4D branched/intersecting geometry \(\rightarrow\) isolated 2D surfaces.** | E02/E03 \(\to\) D07/D09 \(\to\) C07/C17 \(\to\) B17 \(\to\) A43. | Preserve intersections, four-valent edge invariant spaces, branch loci, and fusion-path multiplicities under every merge. The exact 2D formula remains a positive base case rather than a model of the whole 4D amplitude. | **High positive effect for BF1/BF2.** It moves attention to the first genuinely 4D interference. Cost: the simple formula \(d^{\chi-F}\) disappears and signs/coherence return. |
| **7 / S07** | **Physical connected Gibbs correlations \(\rightarrow\) an abstract hard-core polymer gas and tree majorant.** | E04/E08 \(\to\) D06/D07 \(\to\) C09/C10 \(\to\) B11/B24 \(\to\) A25--A30. | First prove an exact activity-preserving map from the plaquette Gibbs law to polymers, including Ursell signs and observable insertions; only then apply Penrose/Brydges--Federbush/KP. | **Necessary for physical clustering and BF6.** Existing combinatorial theorems become load-bearing instead of conditional. The hard new input is the physical activity norm, not more tree combinatorics. |
| **8 / S08** | **Complete effective density \(\rightarrow\) small-/large-field shape plus fiducial constants.** | E04/E07 \(\to\) D06 \(\to\) C11 \(\to\) B12 \(\to\) A31. See `notes/fiducials_notes.md` and `docs/multiscale-2026-07-07.md`. | Extract or reprove the normalized Bałaban step for the repository's exact heat-kernel conventions, with explicit volume/cutoff moduli and the actual remainder norm. | **High effect on BF5/BF6.** It replaces literature-shaped pilots by an RG certificate. It is substantial new constructive analysis, not parameter tuning. |
| **9 / S09** | **All compact simple groups \(\rightarrow\) an SU(2) “worst case” scalar floor.** | E03 \(\to\) D04/D09 \(\to\) C07 \(\to\) B08/B22 \(\to\) A18/A19/A23. | Build the physical carrier, heat tails, intertwiner bounds, and grouped projective diameter separately for every Cartan type, or prove monotonicity on those actual objects. | **Necessary for BF9 unless monotonicity is proved.** It may show SU(2) is not worst for branching/multiplicity even though it minimizes some Casimir scalars. |
| **10 / S10** | **Infinite \(\mathrm{Rep}(SU(2))\) \(\rightarrow\) finite \(SU(2)_k\) fusion category.** | E03/E06 \(\to\) D04 \(\to\) C06/C14 \(\to\) B15 \(\to\) A40/A41. | Work with bounded local fusion words inside \(\mathrm{Rep}(SU(2))\), proving estimates uniform as the label cutoff grows; use \(SU(2)_k\) only to test coherent finite windows. | **Prevents a wrong BF1/BF4 route.** Low-spin identities stabilize, but the central vacuum rank \(k+1\) and finite-category rigidity constants do not supply cutoff-uniform contraction. |
| **11 / S11** | **Physical heat-weighted block transport \(\rightarrow\) pure fusion module transport.** | Same category branch as S10. The explicit counterexample \(D_w(x\otimes V)\ne x\otimes D_w(V)\) is in `notes/su2k-central-monad-campaign.md`. | Construct a heat-twisted/lax module structure whose coherence maps carry Casimir weights and normalization, then compare it exactly with Haar blocking. | **High-risk enabling step for BF3.** It is the correct categorical question left by the finite campaign; ordinary module naturality cannot be cited. |
| **12 / S12** | **All labels and heat-kernel tail \(\rightarrow\) fundamental/binary surfaces or a finite spin cutoff.** | E02/E06 \(\to\) D03/D08 \(\to\) C06/C13 \(\to\) B07/B23 \(\to\) A15--A21. | Prove a uniform tail envelope compatible with fusion growth, face dimensions, and intertwiner multiplicities; combine it with exact low-label census results. | **Necessary for BF1/BF2 uniformity.** The 100 pair-orbit result is strong evidence, not a theorem for higher labels or three strands. |
| **13 / S13** | **Signed \(6j\) coherence \(\rightarrow\) squared Racah probability kernels.** | E02/E03 \(\to\) D04/D08 \(\to\) C08/C14 \(\to\) B09 \(\to\) A21/A22. | Retain the phase and square-root data through the pentagon, then group only at a genuinely positive physical boundary pairing. | **Necessary for BF3 coherence.** Squared kernels are ideal for positivity but do not determine the signed associator; the repository already contains an exact permutation-model no-go for deriving pentagon from squared data alone. |
| **14 / S14** | **Continuum measure \(\rightarrow\) compatible finite/projective positive functionals.** | E05/E06 \(\to\) D03/D05 \(\to\) C03/C05 \(\to\) B05 \(\to\) A10--A13. | Supply tightness/regularity, sigma-additive extension, gauge-compatible support, and convergence moduli for the actual RG family. | **BF7 remains open until this is done.** Non-simplification removes the current functional/measure ambiguity and forces the real continuum construction. |
| **15 / S15** | **Continuum Hamiltonian gap \(\rightarrow\) finite transfer-operator second eigenvalue or abstract clustering predicate.** | E06/E07 \(\to\) D02/D03 \(\to\) C21 \(\to\) B04/B21 \(\to\) A08/A09/A34. | Establish same-object OS reconstruction, identify time translations, and use the spectral measure to turn uniform continuum decay into an interval with zero spectral support. | **Necessary for BF8.** Finite Perron--Frobenius gaps are useful prototypes but do not by themselves survive the continuum limit. |
| **16 / S16** | **Full \(O(4)\ltimes\mathbb R^4\) Euclidean covariance \(\rightarrow\) hypercubic symmetry, or merely the identity rotation.** | E02/E07 \(\to\) D02/D09 \(\to\) C02 \(\to\) B02/B03 \(\to\) A04/A05. | Construct nontrivial lattice \(H_4\) actions first, then prove restoration of translations and rotations in the continuum Schwinger functions. | **Necessary for BF7/BF10.** This is not cosmetic: the current identity-rotation witness explicitly does not establish continuum covariance. |
| **17 / S17** | **Local field algebra and stress/OPE information \(\rightarrow\) Wilson-loop/character algebra.** | E03/E07 \(\to\) D02/D04 \(\to\) C02/C06 \(\to\) B01/B02/B07 \(\to\) A02--A05/A16. | Show that the continuum Wilson algebra generates an adequate local observable net, or construct local curvature/composite fields and their short-distance products on the same measure. | **Important for a defensible BF7/BF10 assembly.** Wilson loops are natural gauge-invariant probes, but the Clay axiomatic target cannot be satisfied by an unrelated single-edge character algebra. |
| **18 / S18** | **Exact 4D block geometry \(\rightarrow\) Migdal--Kadanoff bond moving/hierarchical recursion.** | E04 \(\to\) D06 \(\to\) C11 \(\to\) B12 \(\to\) A43. | Retain all plaquette-sharing constraints and integrate internal links exactly. Use MK only as a comparison/majorant after an error identity. | **Avoids a known false closure.** The MK route can diagnose scaling and summability but does not prove a theorem for the physical 4D Gibbs pushforward. |
| **19 / S19** | **General positive cone \(\rightarrow\) raw one-face fusion matrix cone.** | E06 \(\to\) D03/D09 \(\to\) C12 \(\to\) B13 \(\to\) A32/A33. The raw cone has support holes and infinite diameter (`notes/local-face-birkhoff-census.md`). | Define the cone from reflected physical block generators, possibly after a fixed physical grouping that makes every cross-ratio finite. | **Corrects BF4's object.** Birkhoff--Hopf remains promising only after BF1--BF3 supply this cone; the theorem cannot manufacture positivity or finite diameter. |
| **20 / S20** | **Full heat-kernel/activity polynomial \(\rightarrow\) an unweighted complete fusion sum.** | B07/B09/B23 \(\to\) A15--A22. | Group fixed channels by their actual dimension and Casimir heat exponents and test coefficientwise or interval positivity of that physical polynomial. | **Already produced real progress.** It upgraded the 100-orbit pair census from unweighted positivity to all-\(w>0\) coefficientwise heat positivity. The same upgrade is required in higher sectors. |
| **21 / S21** | **Planar spin-structure sign cancellation \(\rightarrow\) “all signs can be oriented away” in 4D.** | E02/E08 \(\to\) D07/D09 \(\to\) C10/C17 \(\to\) B16 \(\to\) A42. | Keep the actual 4D cell complex and ask for a higher coherence datum whose coboundary is the recoupling-sign cocycle; allow the result to be an obstruction rather than an orientation. | **Good research question, not a proof step.** A positive answer could reorganize BF2; a nonzero obstruction would locate the first exact sign coordinate. Kac--Ward/Kasteleyn alone imply neither outcome. |
| **22 / S22** | **Exact theta/local-CLT object \(\rightarrow\) Gaussian, Poisson-dual, or Euler--Maclaurin approximation.** | E01/E02 \(\to\) D08/D11 \(\to\) C08/C13 \(\to\) B14 \(\to\) A36--A39. | Retain exact discrete sums with explicit remainders and use approximations only with uniform error certificates. | **Moderate, mostly Core-B effect.** This has already eliminated an unnecessary exact Poisson frontier in one tail and localizes what remains to uniform discrete curvature/margin estimates. |
| **23 / S23** | **Global positivity \(\rightarrow\) finite Bernstein/Sturm windows.** | E01/E02 \(\to\) D08 \(\to\) C08/C13 \(\to\) B14 \(\to\) A36--A38. | Seek a structural total-positivity, moment, convolution, or Gram theorem valid for all scale/label parameters; keep finite certificates as regression pins. | **Moderate positive effect.** It can replace infinitely many growing-degree certificates by one theorem, but it does not address the physical Gibbs/blocking mismatch. |
| **24 / S24** | **Located quantitative theorem \(\rightarrow\) qualitative existence or a literature-shaped fiducial.** | E05/E06 \(\to\) D03/D10 \(\to\) C03/C15 \(\to\) B04/B05/B19 \(\to\) A08--A13/A31/A46. | Require explicit moduli for tightness, contraction, landing, distortion, and spectral exclusion; treat unknown constants as named open inputs rather than values. | **Integrity-critical.** It prevents nonconstructive or numerical placeholders from masquerading as cutoff-uniform estimates. It can make the task harder without changing the classical truth, but it makes every claimed gate auditable. |
| **25 / S25** | **Positive gauge-invariant OS sector \(\rightarrow\) a larger indefinite BRST/Krein space.** | E06/E07 \(\to\) D02/D03 \(\to\) C02/C03 \(\to\) B02/B20. | Carry the indefinite metric, nilpotent charge, physical quotient, and positivity proof through the continuum. | **Likely negative net effect on the current route.** It may be necessary for gauge-fixed local fields, but the compact Wilson/Haar formulation already avoids ghosts. Adding the larger space creates a new quotient-positivity theorem without solving BF1--BF6. |
| **26 / S26** | **Constructive witness-bearing limits \(\rightarrow\) unrestricted classical compactness/subsequence extraction.** | E05/E06 \(\to\) D03/D10 \(\to\) C05/C15 \(\to\) B05/B19 \(\to\) A10--A13/A46. | Permit classical subsequences and nonlocated limits, then separately prove uniqueness and identify a positive numerical gap. | **Mixed effect.** Classical compactness may simplify existence, but it does not provide the uniform rate needed to show the limit's gap is positive. Constructive moduli are stronger than Clay formally requires, yet closely match the uniformity wall. |

## 9. Implications for the current work plan

The audit does not recommend adding another independent analytic route.
It recommends sharpening the existing BF route with four actions:

1. **BF1 carrier enrichment:** extend the three-strand/higher-label/larger-slab
   census while storing boundary fusion trees and intertwiner bases, not only
   masks and multiplicities.  Test whether complete physical Haar families
   are Gram-positive.
2. **BF3 exact map:** implement one whole corrected-slab Haar pushforward with
   boundary tensor data, normalization, coarse-intertwiner transport, and an
   exact remainder identity.  Compare the result with a heat-twisted central
   module, not an ordinary module morphism.
3. **BF4 grouped metric:** define projective distance only after a fixed
   physical grouping and target \(q_a=1-ma+o(a)\).  Record cross-ratio bounds
   and the \(C\kappa^{64}\) graded budget in the same carrier.
4. **BF7--BF10 shared-object spine:** for every finite theorem, record the
   exact map by which it acts on the eventual Gibbs/Schwinger object.  Do not
   count a gate closed if its witness lives on a single-edge character model,
   an abstract polymer gas, a finite transfer matrix, or a finite fusion
   category disconnected from that object.

The first two are novel mathematical work.  The third is the corrected
uniformity target.  The fourth is the assembly discipline needed for a Clay
result.

### 9.1 Post-audit implementation update: aggregate posterior calibration, milestone 233 (2026-09-08)

Milestone 233 implements a concrete consequence of the ledger's shared-object
discipline.  The actual physical connected row and both literal posterior
sectors are no longer routed through separate pointwise receiver bounds.
Instead, constructive finite Fubini and the exact retained/unretained source
partition prove

```text
(abs connected row + connected posterior) + disconnected posterior
  <= full physical source density-coefficient l1
       + full physical target density-coefficient l1.
```

The generic result is in
`FiniteDependentKernelCoefficientPosteriorRelativeBound.lean`; its physical
specialization and matched-AF compiler are in
`CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost.lean`.
The route needs neither receiver-cardinality payment, column capacity, nor
full supported-image coverage.  The earlier pointwise calibration path is
retained as a sufficient adapter but is structurally coverage-sensitive.

The remaining receiver-side analytic obligation is one honest aggregate
estimate,

```text
full source density-coefficient l1 + full target density-coefficient l1
  <= (K * g^2) * Z_f^2.
```

Monitored focused checks and dependency targets pass for the generic module
(220 jobs) and physical compiler (5,448 jobs).  New generic declarations use
only `[propext]`; new physical declarations use only
`[propext, Quot.sound]`.  This is a finite-cutoff analytic reduction, not an
inhabited smallness estimate, continuum construction, OS/GNS reconstruction,
Hamiltonian spectral gap, or Clay closure.  No full-root audit is claimed.

### 9.2 Post-audit implementation update: normalized variation and quantitative coverage, milestone 234 (2026-09-08)

Milestone 234 sharpens the aggregate receiver input without changing the
physical carrier.  The full source-plus-target density-coefficient `l1` mass
is divided by the exact positive fine-to-coarse partition density and proved
equivalent to its coarse-law mass-scale form:

```text
normalized receiver variation <= K * Z_c^2
  iff aggregate coefficient l1 <= K * Z_f^2.
```

In
`CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation.lean`,
the source and target receiver carriers are filtered by their actual
supported-path images.  The resulting exact identity is

```text
normalized receiver variation
  ~= covered-image relative calibration
       + uncovered source/target physical mass.
```

This changes the role of coverage in the live route.  Full supported-image
surjectivity is one sufficient way to erase the second term, but it is not a
necessary premise: an `O(g^2 * Z_c^2)` quantitative missing-mass estimate is
enough.  A producer-facing matched-AF structure combines that estimate with an
`O(g^2 * Z_c^2)` covered calibration estimate and reaches the existing
covariance consumer without receiver-cardinality payment.

The two analytic bounds remain uninhabited.  The result is an exact
finite-cutoff normalization and decomposition, not a proof of receiver
smallness, cutoff-uniform contraction, continuum construction, OS/GNS
Hamiltonian gap, or Clay closure.  Its monitored focused check and
dependency-complete target pass (5,450 jobs), and every printed declaration
uses only `[propext, Quot.sound]`.  No full-root audit is claimed.

### 9.3 Post-audit implementation update: positive coverage deficit, milestone 235 (2026-09-08)

Milestone 235 rewrites the uncovered-mass branch as a lower bound on what the
actual supported receiver images capture.  The new coverage-deficit module
proves

```text
full source-plus-target receiver-cell mass
  ~= covered supported-image mass + uncovered physical mass,

uncovered physical mass <= B
  iff full receiver-cell mass <= covered image mass + B.
```

The corresponding matched-AF structure accepts the positive near-full
coverage estimate with `B = (K_miss * g^2) * Z_c^2`, combines it with the
covered calibration estimate, and reaches the existing covariance consumer.
This is strictly weaker than demanding literal image surjectivity and exposes
the actual quantitative target for endpoint transport.

The endpoint audit did not find an existing identification of this deficit
with raw mismatch.  Supported paths provide particular accepted coarse
assignments, whereas the receiver cells retain all accepted endpoint data.
Thus a genuine image-mass estimate or a proved mass-preserving endpoint
quotient is still required.  The result is a finite-cutoff exact reduction,
not an inhabited coverage estimate, cutoff-uniform contraction, continuum
construction, OS/GNS Hamiltonian gap, or Clay closure.  Its monitored focused
check and dependency-complete target pass (5,451 jobs); every printed
declaration uses only `[propext, Quot.sound]`.  No full-root audit is claimed.

### 9.4 Post-audit implementation update: assignment saturation and physical endpoint coverage, milestone 236 (2026-09-08)

Milestone 236 removes the auxiliary-coordinate part of the supported-image
deficit.  For every positive raw-supported coarse endpoint, the new
assignment-saturation module enumerates every accepted coarse intertwiner
assignment rather than only the witness selected by
`jointSelectionFirstFusionWitness`.  A constant path density divided by the
two physical endpoint weights then satisfies the exact block identity

```text
saturated path density * complete accepted-assignment block mass
  ~= original positive raw-supported path mass.
```

Finite zero-extension preserves the complete source mass, target mass,
four-cell cross, and connected raw-cross defect.  The companion physical
coverage module proves that, inside the established receiver cells,
saturated-image membership is equivalent to existence of a positive
raw-supported path with the same two physical coarse endpoints.  It also
proves

```text
full source-plus-target receiver-cell mass
  ~= assignment-saturated covered mass
       + physically unreachable endpoint mass.
```

The former one-assignment images embed into these saturated images.  Thus an
analytic coverage theorem no longer has to reproduce an arbitrary auxiliary
intertwiner assignment; only physical endpoint non-reachability remains.
The next exact adapter must rebuild the coarse-normalized aggregate variation
with the saturated densities before its covered calibration and unreachable
mass can replace the older selected-density inputs.

Focused monitored checks pass for both new modules, and the saturation
dependency target builds successfully.  Every printed load-bearing
declaration uses only `[propext, Quot.sound]`.  This remains a finite-cutoff
disintegration and coverage identity, not an `O(g^2)` estimate, continuum
measure, OS/GNS reconstruction, Hamiltonian gap, or Clay closure.  No
full-root audit is claimed.

### 9.5 Post-audit implementation update: saturated normalized variation, milestone 237 (2026-09-08)

Milestone 237 completes that exact adapter.  The assignment-saturated source
and target densities now define pointwise scale defects

```text
Z_fine^2 - saturatedDensity(receiver) * Z_coarse^2.
```

Their signed receiver cross is proved equal to the physical connected
raw-cross defect after multiplication by the exact `Z_coarse * Z_fine`
factor, and its absolute value is bounded by the full weighted scale-defect
`l1` sum.  Outside the saturated receiver image, finite zero extension makes
the density exactly zero, so the absolute scale-defect contribution is
exactly `Z_fine^2` times the physical receiver weight.  Positive rational
division therefore proves the exact dimensionless identity

```text
assignment-saturated normalized variation
  ~= covered physical-endpoint calibration
       + physically unreachable endpoint mass.
```

The old auxiliary-assignment coverage loss has consequently disappeared from
the active producer.  The receiver branch now has precisely two analytic
obligations: an `O(g^2)` bound for covered endpoint calibration and an
`O(g^2)` bound for physically unreachable endpoint mass.  These estimates,
as well as the separate lower spacing comparison and raw mismatch estimate,
remain open.

Both new modules pass monitored focused checks, the normalized module passes
its dependency-complete target (5,455 jobs), and every printed load-bearing
declaration uses only `[propext, Quot.sound]`.  This is still finite-cutoff
exact algebra.  It is not an `O(g^2)` estimate, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Clay closure.  No full-root audit is
claimed.

### 9.6 Post-audit implementation update: direct matched-AF saturated compiler, milestone 238 (2026-09-08)

Milestone 238 connects the assignment-saturated receiver branch to the
existing covariance consumer without returning to the older selected-density
posterior decomposition.  Clearing the exact positive `Z_fine^2`
normalization proves

```text
saturated normalized variation <= K * Z_coarse^2
  ==> |physical connected raw cross|
        <= K * (Z_coarse^3 * Z_fine^3).
```

On the matched asymptotically-free chart, a new producer-facing structure
accepts the four still-honest quadratic inputs:

```text
c_spacing * g^2 <= a(g),
raw mismatch <= K_mismatch * g^2,
covered endpoint calibration <= K_covered * g^2 * Z_coarse^2,
unreachable endpoint mass <= K_miss * g^2 * Z_coarse^2.
```

It compiles them directly to the division-free raw-cross transport tail and
therefore to `fineCovariance <= anchorRate + epsilon`.  A companion interface
states the last input as the equivalent positive near-full coverage
inequality for the literal source-plus-target receiver cells.

The module passes a monitored focused check and dependency-complete target
(5,456 jobs); every printed declaration uses only
`[propext, Quot.sound]`.  The structure does not inhabit any of its four
analytic fields.  In particular, this is not a cutoff-uniform contraction,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay closure.
No full-root audit is claimed.

### 9.7 Post-audit implementation update: unreachable mass to one-face occupation, milestone 239 (2026-09-08)

Milestone 239 removes the two-replica unreachable-endpoint mass as an
independent analytic input.  Both the source cell `11 x 00` and the target
cell `10 x 01` embed literally into the same broad carrier

```text
root-positive first replica x arbitrary expanded second replica.
```

Exact finite Fubini identifies that carrier's mass as
`rootPositiveMass * Z_coarse`.  Nonnegativity of the physical pair weights
and filter monotonicity then prove

```text
assignment-saturated unreachable endpoint mass
  <= full source-plus-target receiver-cell mass
  <= 2 * rootPositiveMass * Z_coarse.
```

A new matched-AF producer therefore replaces the former unreachable-mass
field by the strictly simpler one-face estimate

```text
rootPositiveMass <= K_pos * g^2 * Z_coarse.
```

It pays the coefficient twice, once for each determinant cell, and compiles
directly to the milestone-238 covariance consumer.  The remaining receiver
inputs are now this one-face occupation estimate and the covered endpoint
calibration estimate.  The separate quadratic lower-spacing and raw-mismatch
inputs also remain open.

The new module passes a monitored focused check and dependency-complete
target (5,457 jobs); every printed load-bearing declaration uses only
`[propext, Quot.sound]`.  It does not prove the one-face `O(g^2)` estimate
itself and therefore does not establish a cutoff-uniform contraction,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay closure.
No full-root audit is claimed.

### 9.8 Post-audit implementation update: endpoint lifts to exact coverage, milestone 240 (2026-09-08)

Milestone 240 factors the stronger zero-unreachable-mass route through one
explicit finite witness family.  A `PositiveExpandedRawEndpointCoverage`
supplies, for every attached coarse expanded endpoint, an enumerated positive
expanded fine source with strictly positive literal whole-slab raw transition
weight.  The attached carrier is exact: it includes the accepted coarse
intertwiner assignments actually appearing in receiver cells while excluding
link-inadmissible zero-mass labellings from the broader bounded Cartesian
list.  Two such one-replica lifts construct the supported source and opposite
target four-cell paths needed by the assignment-saturated receiver images.

The resulting exact chain is

```text
positive raw fine lift for every attached coarse endpoint
  => full assignment-saturated source and target receiver coverage
  => unreachable source-plus-target receiver mass = 0
  => matched-AF covariance consumer needs no unreachable-mass estimate.
```

The new module passes a monitored focused check and dependency-complete target
(5,458 jobs); every printed load-bearing declaration uses only
`[propext, Quot.sound]`.  The endpoint attachment itself is now proved to
force a strictly positive complete coarse-link multiplicity.  Consequently
the producer-facing interface asks only for a positive expanded fine source
whose local fixed-final face sums are pointwise positive; this data compiles
to the whole-slab raw lift and then to zero unreachable mass.

The module does not construct those face-compatible endpoint lifts.  The
existing fine-to-coarse parity target selects one positive coarse endpoint
for each fine row, whereas this interface needs the reverse statement for
every attached coarse endpoint.  That finite support-lift problem is now the
preferred active branch.  The one-face `O(g^2)` occupation bound remains a
valid alternative, but the matched coarse coupling currently supplies only a
fixed corridor bound, not the required quadratic law.

The producer boundary is now sharper still.  A
`PositiveExpandedFusionChannelEndpointLift` retains one enumerated positive
fine source and, at every coarse face, one pair channel with the prescribed
final spin and three true `fusionOK` guards.  A checked adapter proves that
the selected channel has positive character/fusion weight, occurs in the
finite channel sum, and therefore makes the fixed-final face sum positive.
Channel-list membership follows from the guards and the bounded fine packet,
so it is not a separate producer input.

The canonical stretched channel removes the remaining channel selection:
its three guards hold identically, and its final spin is the sum of the four
fine spins in the dyadic face block.  Moreover, a duplicate-free
even-incidence cutoff-one support at positive fine coupling is proved to have
positive physical weight; the positive term constructively yields an
accepted fine intertwiner and membership in the literal expanded positive
source enumeration.  The matched-AF compiler therefore requests only an
`EvenBinarySupportEndpointCoverage`: for each attached coarse endpoint, a
closed fine binary support whose four-face dyadic block counts reproduce its
coarse spins exactly.  This is the geometric reverse-lift theorem still open.

These strengthened layers pass the same monitored focused check and
dependency-complete target (5,458 jobs); its printed adapters use only
`[propext, Quot.sound]`.  No full-root audit is claimed.

This is still exact finite-cutoff algebra.  It does not prove the covered
calibration or spacing/mismatch estimates, cutoff-uniform contraction,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay closure.
No full-root audit is claimed.

### 9.9 Post-audit implementation update: literal closed binary endpoint subdivision, milestone 241 (2026-09-08)

`Z4DyadicSubdivisionClosure.lean` supplies the previously missing reverse
cellular geometry for one exact subclass.  It defines literal dyadic
subdivision of plaquette and link coefficients and proves that subdivision
commutes with the mod-two cellular boundary.  A duplicate-free closed coarse
support therefore refines constructively to a duplicate-free closed fine
support, and corrected-slab membership is preserved.

The endpoint-lift module computes the relevant packet rather than inferring
it from the number of subdivision cells.  For a selected coarse plaquette,
its four coplanar subdivision cells intersect the four nondegenerate
`wholeSlabFinePacket` preimages in the exact spin tuple

```text
[1, 0, 0, 0].
```

Thus subdivision realizes coarse spin `1`, not coarse spin `4`.  Off the
selected support it realizes spin `0`.  The new
`ClosedBinaryCoarseEndpointPresentation.toEvenBinarySupportEndpointLift`
therefore constructs the full exact fine-support lift for every attached
coarse endpoint presented as the indicator of a duplicate-free closed coarse
surface.  The existing stretched-channel, positive-Gibbs, accepted-
intertwiner, and raw-endpoint adapters then apply unchanged.

Monitored verification passes for the new subdivision module and for the
dependency-complete endpoint target (5,459 jobs).  Every printed new
load-bearing theorem depends on at most `[propext, Quot.sound]`; no
`Classical`, choice, `sorry`, `admit`, `native_decide`, custom axiom, or
noncomputable declaration is introduced.  No full-root audit is claimed.

This milestone does not establish coverage for every attached coarse
endpoint.  General endpoints can carry spins `2`, `3`, and `4`; realizing
them requires a multiplicity-faithful fine-strand routing compatible with the
accepted coarse intertwiner assignment.  Covered calibration, quadratic
spacing and mismatch, cutoff-uniform contraction, continuum construction,
OS/GNS reconstruction, Hamiltonian gap, and Clay closure remain open.

### 9.10 Post-audit implementation update: all-plane closed pair bubbles, milestone 242 (2026-09-08)

`Z4DyadicClosedPairBubble.lean` supplies a local closed generator for two
occupied children in one dyadic coarse-face fibre.  It explicitly enumerates
the unit-cube boundaries in coordinate triples `012`, `013`, and `023`, then
translates the appropriate orientation over each of the six coarse
plaquette planes.  The resulting support is duplicate-free and has even
incidence at every fine link.

For either transverse dyadic layer, exactly the two target-plane cube faces
are nondegenerate.  Their ordered packet is respectively
`[1,1,0,0]` or `[0,0,1,1]`; the other four faces are degenerate under dyadic
projection.  A separate locality theorem proves that every different coarse
fibre receives the zero packet.  Thus this is a genuine one-fibre generator,
not merely a target-face count.

The monitored dependency-complete target passes 822 jobs.  Every printed
load-bearing declaration uses at most `[propext, Quot.sound]`.  During the
audit, broad simplification of symbolic half-coordinates and `getD`
membership was found to introduce `Classical.choice`; both proofs were
replaced by explicit constructive division and finite-membership witnesses,
and the final audit is clean.  No full-root audit is claimed.

This closes the local spin-two geometry but not the global reverse lift.
Literal parity subdivision and lower/upper pair bubbles must now be combined
by coefficient-level XOR over the entire attached coarse assignment.  That
construction must preserve closure, compute all packets for spins `0..4`,
and remain inside the corrected fine slab; list append is invalid because
bubble side faces may overlap.  The receiver calibration, uniform physical
estimates, continuum construction, OS/GNS reconstruction, Hamiltonian gap,
and Clay closure remain open.

### 9.11 Post-audit implementation update: global spin-four XOR assembly, milestone 243 (2026-09-08)

`Z4DyadicSpinFourXorAssembly.lean` now performs the required global
coefficient-level construction.  It recursively XORs the local lower and
upper pair-bubble coefficients over a duplicate-free finite carrier, proves
that off-target bubble contributions vanish on each queried dyadic fibre, and
then XORs that assembly with literal subdivision of the odd-spin support.

The resulting ordered packets are exact for all supported spin values zero
through four: `[0,0,0,0]`, `[1,0,0,0]`, `[1,1,0,0]`, `[1,0,1,1]`, and
`[1,1,1,1]`.  In particular, their coordinate totals reproduce the attached
coarse spin.  Closure follows under the explicit condition that the coarse
odd-spin support has even face incidence.  This isolates, rather than hides,
the parity consequence that the endpoint adapter must obtain from accepted
coarse link admissibility.

The monitored dependency-complete target passes 823 jobs, and every printed
load-bearing theorem audits to at most `[propext, Quot.sound]`.  No full-root
audit is claimed.  Milestone 244 turns this finitely generated Boolean
function into a duplicate-free finite support with the same coefficient and
reduces corrected-slab containment to the precise selected-bubble boundary
condition.  Transverse cube faces at the spatial boundary remain a real
containment seam.  Receiver calibration, uniform physical estimates,
continuum construction, OS/GNS reconstruction, Hamiltonian gap, and Clay
closure remain open.

### 9.12 Post-audit implementation update: finite XOR support and slab interface, milestone 244 (2026-09-08)

`Z4DyadicSpinFourXorAssembly.lean` now enumerates a finite ambient list
containing every face that can be selected by the global spin-four XOR
coefficient.  Filtering by that coefficient and applying `eraseDups` produces
the canonical `dyadicSpinFourSupport`.  The formalization proves this list is
duplicate-free, that membership is equivalent to truth of the Boolean
coefficient, and therefore that its induced support coefficient is exactly
the previously verified global XOR assembly.  Closure and every ordered
four-child packet theorem transfer to the finite support.

Corrected-slab containment is reduced to two explicit inputs: containment of
the literal odd-subdivision carrier and `PairBubbleSlabAdmissible`, which asks
only that each actually selected local bubble face lie in the corrected fine
slab.  This isolates the genuine transverse-boundary question without
claiming that arbitrary local cubes remain in the slab.  The active endpoint
adapter must derive odd-spin even incidence from accepted coarse link
admissibility and either prove the selected-bubble condition or construct a
boundary-corrected generator.

The monitored dependency-complete target passes 823 jobs.  All newly printed
load-bearing declarations audit to at most `[propext, Quot.sound]`; no
full-root audit is claimed.  This closes finite support realization only.  It
does not establish receiver coverage, uniform contraction, the continuum
measure, OS/GNS reconstruction, a Hamiltonian gap, or Clay closure.

### 9.13 Post-audit implementation update: accepted-endpoint lift and receiver coverage, milestone 245 (2026-09-08)

`Z4DyadicSpinFourEndpointLift.lean` closes both interfaces isolated in
section 9.12.  First, the accepted endpoint's global coarse intertwiner
assignment makes every local production multiplicity positive.  The SU(2)
odd-sum obstruction therefore proves even incidence of the coarse odd-spin
support.  Second, a face on a positive spatial boundary exposes a literal
far link whose corrected-slab incident-face list is a singleton.  The
one-valent multiplicity theorem forces that face spin to zero.  Every
selected spin `2`, `3`, or `4` consequently has the exact spatial margin
needed by the closed pair-bubble generator.

This gives a finite duplicate-free even binary support inside the affine
fine slab for every attached endpoint, with exact ordered packet total equal
to each coarse spin from zero through four.  At fine cutoff one and positive
fine/coarse couplings, the existing support-to-channel-to-positive-source
compiler yields positive raw endpoint coverage.  The existing two-replica
coverage theorems then cover both assignment-saturated receiver columns and
prove the physically unreachable receiver mass exactly equivalent to zero.

The monitored dependency-complete target passes 5,489 jobs.  All printed
load-bearing declarations depend on at most `[propext, Quot.sound]`.  Broad
arithmetic and list-membership simplification initially leaked
`Classical.choice`; the accepted proof replaces those steps with explicit
constructive inequalities and literal cons-membership witnesses.  No
full-root audit is claimed.

The active issue is no longer endpoint reachability.  It is the quantitative
covered-image calibration bound, together with the lower physical-spacing
and raw-mismatch estimates needed by the matched-AF contraction compiler.
Cutoff-uniform contraction, the same interacting continuum measure, OS/GNS
reconstruction, the Hamiltonian gap, and Clay closure remain open.

### 9.14 Post-audit implementation update: automatic matched-AF coverage, milestone 246 (2026-09-08)

`Z4DyadicSpinFourMatchedAFCoverage.lean` removes one more historical interface
artifact.  A matched physical observable schedule constructs every scale pair
from cutoff-one fine geometry.  Consequently the concrete spin-four endpoint
coverage from section 9.13 applies definitionally at every scale; it is not an
analytic hypothesis and does not need an eventual-start qualifier.

The minimized record
`MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl` retains only
the lower quadratic physical-spacing estimate, the upper quadratic raw-
mismatch estimate, and the upper quadratic covered normalized-variation
estimate.  Its constructive adapter inserts automatic endpoint coverage into
the established assignment-saturated compiler.  The resulting chain proves
zero unreachable mass and reaches the existing eventual
`fineCovariance <= anchorRate + epsilon` theorem.

The dependency-complete monitored target passes 5,490 jobs.  All four printed
declarations depend exactly on `[propext, Quot.sound]`; no `Classical`, choice,
`sorry`, new axiom, or noncomputable witness is introduced.  No full-root
audit is claimed.

This is a strict interface simplification, not an analytic contraction
estimate.  Covered-image calibration, physical spacing, and raw mismatch are
still open, as are all-cutoff contraction, the same interacting continuum
measure, OS/GNS reconstruction, the Hamiltonian gap, and Clay closure.

### 9.15 Post-audit implementation update: filter-free receiver variation, milestone 247 (2026-09-08)

The exact coverage theorem has one further quantitative consequence.  In
`Z4DyadicSpinFourMatchedAFCoverage.lean`, the covered normalized variation is
proved exactly equivalent to the full normalized variation on the canonical
source and target receiver carriers.  A companion order theorem transfers a
full-carrier upper bound to the covered term with no change in its budget.

The active analytic input can therefore be stated without supported-image
filters: bound the full source-plus-target assignment-saturated scale-defect
`l1` by `(K * g^2) * Z_c^2`.  The endpoint lift and its receiver-image
bookkeeping no longer appear in that estimate.

The dependency-complete monitored target passes 5,490 jobs, and both new
declarations depend exactly on `[propext, Quot.sound]`.  This does not prove
the full-carrier quadratic bound, lower physical spacing, raw mismatch,
all-cutoff contraction, continuum construction, OS/GNS reconstruction, the
Hamiltonian gap, or Clay closure.

### 9.16 Post-audit implementation update: pointwise relative calibration compiler, milestone 248 (2026-09-08)

`Z4DyadicSpinFourReceiverPointwiseCalibration.lean` turns a common pointwise
bound on the saturated source and target receiver defects into the full
aggregate normalized-variation bound.  The useful pointwise scale is
`relative * Z_f^2`: the weighted source and target sums factor
through the exact full receiver-cell mass, that mass is at most `2*Z_c^2`,
and positive division cancels `Z_f^2`.  Consequently the full normalized
variation is at most `2*relative*Z_c^2`; taking `relative = K*g^2` gives the
quadratic receiver bound in exactly the matched-AF producer's units, with no
carrier count.  Exact endpoint coverage then transfers that estimate directly
to the covered-variation field consumed by the covariance compiler.

This supersedes the old unsaturated off-image pointwise alternative only
after exact spin-four endpoint coverage: the current pointwise obligation is
on the assignment-saturated density over the now-covered canonical carriers.
The theorem does not inhabit that obligation.

The dependency-complete monitored target passes 5,491 jobs, and all seven new
printed declarations depend exactly on `[propext, Quot.sound]`.  The actual
pointwise density calibration, lower physical-spacing bound, raw-mismatch
bound, uniform all-cutoff contraction, continuum construction, OS/GNS
reconstruction, Hamiltonian gap, and Clay closure remain open.

### 9.17 Post-audit implementation update: saturated relative-density seam, milestone 249 (2026-09-08)

`Z4DyadicSpinFourReceiverRelativeDensityCalibration.lean` factors each
assignment-saturated source and target scale defect exactly as
`(Z_f^2/Z_c^2 - saturatedDensity) * Z_c^2`.  It then proves that a relative
density error at most `relative * (Z_f^2/Z_c^2)` supplies the pointwise
`relative * Z_f^2` premise of milestone 248.  The quadratic specialization
feeds the exact endpoint-covered matched-AF field with bound
`(2*K*g^2)*Z_c^2` and no receiver count.

The module names the remaining analytic input as
`PositiveExpandedAssignmentSaturatedRelativeDensityCalibration`; it does not
inhabit it.  This sharply separates the proved normalization and aggregation
algebra from the open comparison between actual saturated raw path masses
and physical receiver weights.

The dependency-complete monitored target passes 5,492 jobs, and all ten
printed declarations depend exactly on `[propext, Quot.sound]`.  The actual
relative-density estimate, lower physical-spacing bound, raw-mismatch bound,
uniform all-cutoff contraction, continuum construction, OS/GNS
reconstruction, Hamiltonian gap, and Clay closure remain open.

### 9.18 Post-audit implementation update: schedule-level density compiler, milestone 250 (2026-09-08)

The relative-density module now packages the pointwise saturated estimate as
an eventual matched-AF schedule field.  It preserves the independent spacing
floor and raw-mismatch hypotheses, doubles the common density coefficient
only when adding source and target receiver variation, inserts automatic
spin-four endpoint coverage, and constructs the existing covered-variation
control.  Its final consumer is the finite comparison
`fineCovariance <= anchorRate + epsilon`.

The 5,492-job monitored target passes, and all ten printed declarations use
exactly `[propext, Quot.sound]`.  The schedule structure does not inhabit its
three analytic fields and does not provide all-cutoff persistence, a
continuum measure, OS/GNS reconstruction, a Hamiltonian gap, or Clay closure.

### 9.19 Post-audit implementation update: raw receiver pushforward, milestone 251 (2026-09-08)

The new raw-pushforward module removes the normalization quotient from the
active receiver premise.  For both source and replica-oriented target cells,
it defines the receiver-wise raw mass as the finite zero extension of every
assignment-saturated lift contribution and proves exactly

```text
fiberDensity(receiver) * physicalReceiverWeight(receiver)
  = rawPushforwardMass(receiver).
```

Since each receiver weight is strictly positive, the pointwise raw estimate

```text
|partitionDensity * receiverWeight - rawPushforwardMass|
  <= relative * partitionDensity * receiverWeight
```

is equivalent to the earlier relative-density estimate.  A matched-AF raw
schedule structure now compiles that premise, together with the still
independent spacing and raw-event-mismatch fields, to the same eventual
finite covariance comparison.

The 5,493-job monitored target passes and all nine printed declarations use
exactly `[propext, Quot.sound]`.  This does not prove the raw estimate.  The
repository audit found no literal whole-slab stationarity identity or
small-`g` kernel perturbation theorem, and the all-cutoff raw kernel still has
an open positive-row-closure input.  The active research edge is therefore a
uniform estimate on these explicit raw weights, with a fallback to a
localized or aggregate receiver statement if the pointwise volume-uniform
form is too strong.  No continuum, OS/GNS, Hamiltonian-gap, or Clay claim is
made.

### 9.20 Post-audit implementation update: aggregate raw-column cross, milestone 252 (2026-09-08)

The fallback identified in milestone 251 is now a checked, strictly weaker
producer interface.  `Z4DyadicSpinFourReceiverRawColumnCrossCalibration.lean`
sums the saturated raw receiver masses across the complete source and target
four-cell carriers and proves that each total is exactly a sum of products of
literal one-replica pushed column masses.  Their signed difference is exactly
the actual pushed four-cell cross.

With the coarse and fine partition squares restored, the resulting signed
raw-column scale-defect cross is exactly the saturated scale-defect cross
already connected to the physical covariance numerator.  Consequently the
single cancellation-preserving estimate

```text
|signed raw-column scale-defect cross|
  <= relative * (Z_c^2 * Z_f^2)
```

implies the existing physical raw-cross bound with no receiver count and no
pointwise absolute-value sum.  A matched-AF schedule structure turns the
quadratic specialization `relative = K*g^2`, together with the independent
spacing and raw-event-mismatch fields, into the finite comparison
`fineCovariance <= anchorRate + epsilon`.

The 5,494-job monitored target passes, and all twelve printed declarations
use exactly `[propext, Quot.sound]`.  This module does not inhabit the
aggregate estimate and does not imply receiver total-variation contraction;
it controls only the selected signed connected four-cell observable.  The
actual aggregate `K*g^2` bound is the active analytic producer.  Physical
spacing, raw mismatch, all-cutoff persistence, the same interacting continuum
measure, OS/GNS reconstruction, the Hamiltonian gap, and Clay closure remain
open.

### 9.21 Post-audit implementation update: fine-coupling reference perturbation, milestone 253 (2026-09-08)

The first concrete analytic reduction after the aggregate raw-column cross is
now checked.  `Z4DyadicSpinFourFineCouplingReferencePerturbation.lean` defines
the total face Casimir exponent of a corrected-slab physical labelling and
proves that its production summand at coupling `w` is exactly `w` to that
exponent times the coupling-one summand.  Constructive Bernoulli control for
`0 <= w <= 1` bounds the loss by `(1-w)` times the explicit Casimir-weighted
coupling-one summand.

Kernel positivity transports the estimate to each literal pushed receiver
column, and finite summation gives the analogous partition loss.  Row
normalization also proves that the total unit-coupling pushed mass is exactly
the unit-coupling fine partition.  The 5,495-job monitored target passes; the
six printed declarations use at most `[propext, Quot.sound]`.

This is not a volume-uniform `K*g^2` estimate.  The Casimir moment can grow
with the slab, no coupling-one stationarity or reference signed-cross identity
has been proved, and the matched schedule uses `blockedWeight` rather than the
fine nome whose margin is definitionally `g^2`.  The next honest analytic edge
is to combine a blocked-margin upper bound from `CubicMarginLaw` with a
localized/cancellation-preserving Casimir estimate, or to prove that this
global reference route is too volume-expensive and refine it.  Physical
spacing, raw mismatch, all-cutoff persistence, continuum construction,
same-object OS/GNS reconstruction, the Hamiltonian gap, and Clay closure
remain open.

### 9.22 Post-audit implementation update: matched-AF quadratic reference loss, milestone 254 (2026-09-09)

The scalar mismatch isolated in milestone 253 is now closed.
`BF4MatchedPhysicalAFBridge.lean` derives the constructive upper comparison

```text
1 - blockedWeight(family,g) <= 2*g^2
```

from the existing `CubicMarginLaw`; the proof uses the absolute cubic
remainder, the same one-sided window as the lower comparison, positivity of
the AF coefficients, and no new hypothesis.

`Z4DyadicSpinFourFineCouplingReferencePerturbation.lean` adds the two sign
lemmas needed to multiply this comparison by the literal receiver-local and
total coupling-one Casimir moments.  At a matched fine coupling, it proves

```text
unit pushed column - actual pushed column
  <= 2*g^2 * receiver-local unit-coupling Casimir moment,

unit fine partition - actual fine partition
  <= 2*g^2 * total unit-coupling Casimir moment.
```

The dependency-complete monitored target passes all 5,495 jobs.  The new
load-bearing declarations use at most `[propext, Quot.sound]`, and the
Casimir-exponent definition remains axiom-free.

This does not supply a volume-uniform raw-column cross estimate: both
moments are still global slab sums.  The next honest producer must prove the
coupling-one reference-cross identity and exploit observable cancellation or
localization to control the relevant moment uniformly in volume.  Physical
spacing, raw-event mismatch, all-cutoff persistence, continuum construction,
same-object OS/GNS reconstruction, the Hamiltonian gap, and Clay closure
remain open.

### 9.23 Post-audit implementation update: localized coupling-one raw-column cross perturbation, milestone 255 (2026-09-09)

The scalar and one-column bounds now reach the cancellation-preserving
four-cell observable.  `Z4DyadicSpinFourFineCouplingReferenceCross.lean`
defines the coupling-one product mass of a coarse target pair and its
product-rule Casimir moment.  Monotonicity below coupling one, the exact
product-difference decomposition, and finite-cell summation prove

```text
|couplingOneRawColumnCross - actualPushedFourCellCross|
  <= (1 - fineCoupling)
       * (sourcePairCellCasimirMoment + targetPairCellCasimirMoment).
```

Only the two literal pair cells selected by the signed observable occur.  The
matched-AF specialization replaces the margin by `2*g^2`, and the terminal
corollary uses the milestone-252 identity to state the result directly for
the assignment-saturated receiver raw-column cross.

The dependency-complete monitored target passes all 5,496 jobs, and all
eleven printed declarations use exactly `[propext, Quot.sound]`.  This is not
yet the aggregate `K*g^2` producer: the coupling-one reference cross has not
been proved to vanish, and the localized pair-cell moment has not been
bounded uniformly in the growing slab.  These are now the exact active
co-producers.  Physical spacing, raw-event mismatch, all-cutoff persistence,
the same interacting continuum measure, OS/GNS reconstruction, the
Hamiltonian gap, and Clay closure remain open.

### 9.24 Post-audit implementation update: reference scale-defect decomposition, milestone 256 (2026-09-09)

The coarse nome audit changes the correct next target.  The matched schedule
uses a fine blocked nome near one but an explicitly decimated coarse nome in
the strong-coupling corridor.  Therefore the coupling-one pushed reference
cross is not expected to vanish by itself, and an all-unit coarse reference
would not match the covariance consumer.

`Z4DyadicSpinFourFineCouplingReferenceScaleDefect.lean` instead defines the
literal coarse Gibbs signed cross and proves

```text
rawScaleDefect
  = Z_f^2 * coarseCross - Z_c^2 * actualReceiverCross
  = referenceScaleDefect
      + Z_c^2 * (couplingOnePushedCross - actualReceiverCross),
```

where `referenceScaleDefect` retains the actual fine/coarse partitions and
the actual decimated coarse Gibbs law.  The milestone-255 theorem gives

```text
|rawScaleDefect|
  <= |referenceScaleDefect|
       + Z_c^2 * (2*g^2) * localizedPairCellCasimirMoment.
```

A final constructive compiler shows that a quadratic reference-residual
bound normalized by `Z_c^2*Z_f^2`, together with a localized moment bound
normalized by `Z_f^2`, inhabits the existing aggregate raw-column
calibration with coefficient
`(referenceCeiling + 2*momentCeiling)*g^2`.

The dependency-complete monitored target passes all 5,497 jobs, and all nine
printed declarations use exactly `[propext, Quot.sound]`.  The theorem does
not inhabit either remaining analytic input: reference scale-defect
calibration against the decimated coarse law and volume-uniform localized
moment normalization remain open.  Physical spacing, raw-event mismatch,
all-cutoff persistence, the same interacting continuum measure, OS/GNS
reconstruction, the Hamiltonian gap, and Clay closure also remain open.

### 9.25 Post-audit implementation update: coupling-one partition drift, milestone 257 (2026-09-09)

The reference calibration has been audited one layer further.
`Z4DyadicSpinFourFineCouplingPartitionDrift.lean` proves that the actual fine
partition is at most its coupling-one counterpart and defines the
nonnegative loss

```text
unitFinePartition^2 - actualFinePartition^2.
```

It factors this exactly as the one-power partition loss times the partition
sum, then applies the matched-AF perturbation theorem to obtain

```text
partitionSquareLoss
  <= 2*g^2 * totalUnitCasimirMoment
       * (unitFinePartition + actualFinePartition).
```

The milestone-256 reference defect itself satisfies the exact second
recentring

```text
referenceScaleDefect
  = balancedUnitBlockingDefect
      - partitionSquareLoss * coarseCross,
```

where the balanced defect uses the coupling-one fine partition square as
well as the coupling-one pushed cross.  The resulting absolute bound exposes
two distinct analytic obligations: a true unit-fine versus decimated-coarse
blocking-law comparison, and a global normalization term containing the
Casimir exponent summed over the entire fine slab.

The dependency-complete monitored target passes all 5,498 jobs, and all
twelve printed declarations use exactly `[propext, Quot.sound]`.  This does
not prove a no-go for every global interpolation, but it rules out treating
the existing coupling-one reference as a purely receiver-local perturbation.
The preferred next branch is a face-local or normalization-preserving
reference that retains the two selected pair-cell estimate without paying
the whole-slab moment.  The balanced blocking calibration and localized
moment bound remain open, as do physical spacing, raw-event mismatch,
all-cutoff persistence, the same interacting continuum measure, OS/GNS
reconstruction, the Hamiltonian gap, and Clay closure.

### 9.26 Post-audit implementation update: same-fine-law reference kernels, milestone 258 (2026-09-09)

`Z4DyadicSpinFourNormalizationPreservingReferenceKernel.lean` realizes the
normalization-preserving alternative at the correct abstract level.  Every
`FiniteSlabKernel` is row-normalized, so its unnormalized pushed target law
has total mass equal to the same actual fine partition.  An arbitrary
reference kernel can therefore be compared directly with the production
physical kernel without changing the fine Gibbs weights.

The aggregate signed raw-column scale defect has the exact decomposition

```text
rawScaleDefect
  = referenceKernelScaleDefect
      + Z_c^2 * (referenceKernelCross - physicalKernelCross).
```

The associated absolute bound contains no partition-drift payment.  A
reference blocking defect bounded by
`referenceCeiling*g^2*(Z_c^2*Z_f^2)` and a same-fine-law signed-cross
discrepancy bounded by `kernelCeiling*g^2*Z_f^2` compile to the existing
aggregate raw-column calibration with coefficient
`(referenceCeiling + kernelCeiling)*g^2`.

The dependency-complete monitored target passes all 5,499 jobs, and all nine
printed declarations use exactly `[propext, Quot.sound]`.  This is an honest
interface rather than a hidden existence claim: a concrete local or ideal
reference kernel satisfying the two bounds remains to be constructed.  The
older deterministic parity pushforward is not automatically such a producer,
because its own physical-weight fence already proves that bare parity-fibre
summation need not equal the physical coarse Gibbs weight.  All-cutoff
persistence, the continuum measure, OS/GNS reconstruction, the Hamiltonian
gap, and Clay closure remain open.

### 9.27 Post-audit implementation update: concrete Gibbs refresh, milestone 259 (2026-09-09)

`Z4DyadicSpinFourGibbsRefreshReferenceCross.lean` constructs the preferred
normalization-preserving reference explicitly.  Every fine source uses the
normalized actual coarse Gibbs row.  This rank-one row is nonnegative,
normalized, and reflection-intertwining on the literal physical
edge-labelling carriers.  It is intentionally not declared a
`FiniteSlabKernel`, because that structure requires source dependence.

The generic proportional-column calculation gives the exact pushed law

```text
refreshRawMass(y) = (Z_f / Z_c) * coarsePhysicalTerm(y),
```

including total mass `Z_f`.  Its four-cell determinant therefore scales by
`(Z_f/Z_c)^2`, and the coarse partition square cancels the denominator:

```text
Z_c^2 * refreshCross = Z_f^2 * coarseCross.
```

Thus the refresh blocking defect is zero, not merely small.  The production
raw-column scale defect is exactly

```text
Z_c^2 * (refreshCross - physicalKernelCross).
```

Only one quadratic signed-cross calibration remains on this branch.  The
next proof should expand or bound that determinant difference through the
already exposed physical-kernel pushed-mass remainder while retaining signed
cancellation; an independent pointwise or full-carrier variation bound would
risk reintroducing receiver-cardinality or volume loss.

The dependency-complete monitored target passes all 5,502 jobs, and all
sixteen printed declarations use exactly `[propext, Quot.sound]`.  This is a
finite cutoff-one scale comparison, not all-cutoff persistence, a continuum
measure construction, OS/GNS reconstruction, a Hamiltonian gap, or Clay
closure.

### 9.28 Post-audit implementation update: refresh cross is the connected remainder, milestone 260 (2026-09-09)

`Z4DyadicSpinFourGibbsRefreshConnectedRemainder.lean` proves that the sole
signed-cross input left by milestone 259 is exactly the connected pushed-law
remainder already isolated earlier in the physical transport stack.  For a
witness-bearing face block map `M`, constructive positive-factor cancellation
gives

```text
rawColumnScaleDefect
  = (Z_c^2 * Z_f^2) * centeredCylinderRemainder,

refreshCross - physicalKernelCross
  = Z_f^2 * centeredCylinderRemainder.
```

The second identity also equals `Z_f^2` times the signed remainder expectation
of `connectedRemainderObservable`, the established three-cylinder observable
whose pointwise absolute value is at most one.  Therefore the preferred
quadratic premise is directly

```text
|centeredCylinderRemainder| <= kernelCeiling * g^2.
```

It compiles to the aggregate raw-column calibration without a global
partition-drift, receiver-cardinality, or extra triangle-factor payment.  A
full `physicalKernel.remainderL1 <= kernelCeiling*g^2` estimate is sufficient
through the existing sharp one-copy `L1` majorant, but is deliberately marked
as a stronger fallback because it discards the selected-cylinder signs.

The dependency-complete monitored target passes all 5,503 jobs, and all nine
printed declarations use exactly `[propext, Quot.sound]`.  No quadratic
centered-remainder estimate is asserted.  Cutoff/volume uniformity, continuum
measure construction, OS/GNS reconstruction, the Hamiltonian gap, and Clay
closure remain open.

### 9.29 Post-audit implementation update: direct matched-AF connected producer, milestone 261 (2026-09-09)

`Z4DyadicSpinFourGibbsRefreshConnectedRemainderMatchedAF.lean` removes the
last adapter-level ambiguity from the cancellation-preserving branch.  Its
schedule witness asks directly for a positive quadratic spacing floor, an
`O(g^2)` raw-event mismatch, and

```text
|centeredCylinderRemainder| <= connectedCeiling * g^2
```

on the actual shifted matched-AF scale pair and face map.  The milestone-260
compiler supplies the aggregate receiver raw-column cross with the identical
coefficient, and the existing matched-AF raw-column compiler reaches the
actual covariance raw-cross tail and final finite `anchor + epsilon` theorem.

This is the preferred three-input interface: no receiver cardinality,
pointwise density calibration, global coupling-one partition drift, or full
remainder `L1` norm is introduced.  It does not inhabit any of the three
quantitative fields.  The next analytic proof must act on the selected
centered observable itself (or knowingly choose the stronger `L1` fallback),
alongside the independent raw-mismatch and lower-spacing estimates.

The dependency-complete monitored target passes all 5,504 jobs, and all four
printed declarations use exactly `[propext, Quot.sound]`.  Arbitrary-cutoff
and volume-uniform persistence, the continuum measure, same-object OS/GNS,
the Hamiltonian gap, and Clay closure remain open.

### 9.30 Post-audit implementation update: exact reverse normalization cancellation, milestone 262 (2026-09-09)

The updated `Z4DyadicSpinFourGibbsRefreshConnectedRemainder.lean` proves that
the raw-column and centered-remainder calibrations are constructively
equivalent.  The reverse implication uses the exact scale-defect identity,
multiplicativity of absolute value by a nonnegative factor, strict positivity
of `Z_c^2*Z_f^2`, and ordered-field cancellation to derive

```text
|rawScaleDefect| <= (K*g^2)*(Z_c^2*Z_f^2)
  iff
|centeredCylinderRemainder| <= K*g^2.
```

It also composes the reverse direction with the existing coupling-one
reference/localized-moment compiler.  Hence quadratic control of the honest
reference residual and a volume-uniform bound on only the two selected
pair-cell Casimir moments imply the preferred centered calibration with
coefficient `referenceCeiling + 2*momentCeiling`.

This proves that receiver normalization is no longer a frontier.  The
analytic frontier is exactly the normalized centered quantity itself, with
the reference/localized-moment pair retained as a sufficient decomposition.
Neither estimate is inhabited.  The full remainder-`L1` branch remains a
strictly stronger fallback.

The dependency-complete monitored target passes all 5,504 jobs.  All twelve
printed connected-remainder declarations and the four downstream matched-AF
declarations use exactly `[propext, Quot.sound]`.  Cutoff/volume uniformity,
continuum construction, same-object OS/GNS, the Hamiltonian gap, and Clay
closure remain open.

### 9.31 Post-audit implementation update: normalized signed change-of-measure seam, milestone 263 (2026-09-09)

The new `Z4DyadicSpinFourFineCouplingNormalizedRecentering.lean` removes the
need to estimate coupling-one cross loss and global partition drift as two
separate positive costs.  It normalizes the coupling-one pushed four-cell
cross by the coupling-one partition square and proves

```text
unitCross / unitZ^2 - actualCross / actualZ^2
  = (unitCross*actualZ^2 - actualCross*unitZ^2)
      / (unitZ^2*actualZ^2).
```

The numerator is one signed determinant, so cancellation is retained until
the analytic producer chooses where to apply an absolute value.  The module
also proves that `actualCross/actualZ^2` is the existing blocked covariance
and inserts the unit-normalized cross into the centered-cylinder remainder.
Consequently the preferred centered calibration follows from exactly two
named quadratic premises: a unit-normalized blocking residual and a raw
centered-change numerator bound.

`Z4DyadicSpinFourGibbsRefreshConnectedRemainder.lean` specializes that
compiler to the production physical kernel.  This route does not inhabit the
two premises; it exposes a sharper proof target.  The earlier selected-cell
Casimir estimate remains a sufficient fallback, but because it weights by
the total fine-slab Casimir exponent before selecting receiver cells, it is
not presently a volume-uniform local producer.

The monitored leaf target passes all 5,497 jobs and the downstream Gibbs
target passes all 5,504 jobs.  The printed declarations use exactly
`[propext, Quot.sound]`.  Cutoff/volume uniformity, continuum construction,
same-object OS/GNS, the Hamiltonian gap, and Clay closure remain open.

### 9.32 Post-audit implementation update: selected observable row-action seam, milestone 264 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedRowAction.lean` pushes the
normalized connected remainder down to the source-row level without replacing
the production kernel or observable.  It proves that the proportional Gibbs
refresh row is exactly the normalized coarse physical law and uses finite
Fubini to identify

```text
fine Gibbs average of
  [production row - coarse Gibbs refresh row]
  acting on the connected observable
= centeredCylinderRemainder.
```

This exposes the preferred local analytic target: bound the selected signed
row action, not the full kernel-row variation.  Three nested interfaces are
now checked: the signed average is exactly equivalent to the existing
centered calibration; its absolute value is bounded by the fine-weighted sum
of absolute selected row actions; and a pointwise selected-row estimate
implies that weighted bound because the fine Gibbs law is nonnegative and
normalized.  A full kernel-row `L1` estimate compiles as a conservative
fallback using the observable's pointwise unit bound.

No estimate is inhabited.  The gain is localization and preserved target
cancellation: literal recoupling or receiver/posterior arguments can now
target one observable action per source.  The monitored leaf target passes
all 5,505 jobs, and all fourteen printed declarations depend exactly on
`[propext, Quot.sound]`.  A subsequent monitored aggregate check was safely
stopped at the configured 12 GiB memory reserve and is not reported as
passed.  Cutoff/volume uniformity, continuum construction, same-object OS/GNS,
the Hamiltonian gap, and Clay closure remain open.

### 9.33 Post-audit implementation update: positive raw connected rows, milestone 265 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedRawRow.lean` expands the
selected connected action on each strictly positive fine Gibbs source.  Its
production expectation is proved exactly equal to the globally link-glued
raw observable numerator divided by the complete positive row partition;
the reference expectation is the normalized coarse Gibbs mean of the same
connected observable.  Thus the local producer now sees literal physical
raw weights and one positive denominator rather than an opaque normalized
kernel row.

Dependent recursions separate strictly positive physical terms from the
remaining sources.  Each non-positive branch has exactly zero normalized
fine Gibbs mass, so removing it preserves both the signed source average and
the source-weighted selected-row `L1`.  The surviving positive-raw signed
average is therefore exactly the centered-cylinder remainder.  Direct
signed-average, source-`L1`, and pointwise positive-raw quadratic interfaces
compile to the established centered calibration without coefficient loss.

This is an exact raw recoupling surface, not a smallness proof.  The next
preferred reduction is to place the raw production numerator and coarse
Gibbs mean over one common positive denominator and estimate their signed
cross numerator before taking absolute values.  The monitored leaf target
passes all 5,506 jobs, and all nineteen printed declarations depend exactly
on `[propext, Quot.sound]`.  The aggregate root target was not rerun after its
memory-reserve stop, so no aggregate pass is claimed.  Cutoff/volume
uniformity, continuum construction, same-object OS/GNS, the Hamiltonian gap,
and Clay closure remain open.

### 9.34 Post-audit implementation update: source-resolved raw cross, milestone 266 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedRawCross.lean` clears the two
outer normalizations of each positive connected row without splitting the
signed difference.  The production raw observable numerator over its
complete conditional-row partition and the coarse raw observable numerator
over the coarse physical partition become one cross numerator over the
strictly positive product denominator.

The connected specialization exposes the division-free local premise

```text
|rowNumerator*Zc - coarseNumerator*rowZ|
  <= K*g^2*(rowZ*Zc).
```

This premise compiles through the positive-raw pointwise interface to the
existing normalized centered-remainder calibration with no coefficient
loss.  Thus target and normalization cancellation remain available to the
analytic proof until the final absolute value.

No bound is inhabited.  The observable numerator still carries the blocked
fine-law target moment and coarse-law root moment as normalized coefficients;
clearing those factors into one fully raw joint/root/target expression is
the next algebraic frontier.  The monitored leaf target passes all 5,507
jobs, and all eleven printed declarations depend exactly on
`[propext, Quot.sound]`.  No aggregate root pass is claimed.  Cutoff/volume
uniformity, continuum construction, same-object OS/GNS, the Hamiltonian gap,
and Clay closure remain open.

### 9.35 Post-audit implementation update: literal three-event row cross, milestone 267 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedRawEventCross.lean` expands the
source-resolved connected numerator before estimating it.  Both the selected
conditional recoupling row and the coarse physical comparison row become the
same signed joint/root/target cylinder combination.  Cross-multiplication then
regroups them exactly as

```text
- jointCylinderCross
  + blockedTargetMoment * rootCylinderCross
  + coarseRootMoment    * targetCylinderCross,

cylinderCross(event) = rowEventRaw(event)*Zc
                       - coarseEventRaw(event)*rowZ.
```

Thus each literal event retains production-versus-Gibbs cancellation, and
the signs among the three centered terms are also retained.  A relative
pointwise `K*g^2` bound on the combined event-cross numerator compiles to the
previous raw-cross interface and hence to the normalized centered remainder
without coefficient loss.

No estimate is inhabited.  The blocked target moment and coarse root moment
remain normalized coefficients; clearing their fine/coarse partition
denominators into one fully raw signed polynomial is the next algebraic edge.
The monitored leaf target passes all 5,508 jobs, and all thirteen printed
declarations depend exactly on `[propext, Quot.sound]`.  No aggregate root
pass is claimed.  Cutoff/volume uniformity, continuum construction,
same-object OS/GNS, the Hamiltonian gap, and Clay closure remain open.

### 9.36 Post-audit implementation update: fully raw row polynomial, milestone 268 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCross.lean`
clears the fine and coarse partition denominators hidden in the two moment
coefficients while retaining all event-cross signs.  Multiplying the
three-event cross by `Zf*Zc` gives exactly

```text
-(jointCross * (Zf*Zc))
  + (pushedTargetRaw * rootCross) * Zc
  + (coarseRootRaw  * targetCross) * Zf,
```

where each event cross remains
`rowEventRaw*Zc - coarseEventRaw*rowZ`.  The selected positive connected row
is therefore this fully raw polynomial divided by the strictly positive
denominator `(rowZ*Zc)*(Zf*Zc)`, constructively equal up to association and
commutation to `rowZ*Zf*Zc^2`.

A relative `K*g^2` bound on the polynomial compiles directly to the existing
positive-row pointwise and normalized centered-remainder calibrations.  No
such estimate is inhabited.  It is a sufficient pointwise route but stronger
than the signed fine-law aggregate actually consumed by the physical
remainder; the next audit therefore retains source cancellation before
selecting the analytic premise.
The monitored leaf target passes all 5,509 jobs, and all eleven printed
declarations depend exactly on `[propext, Quot.sound]`.  No aggregate root
pass is claimed.  Raw-event mismatch, lower physical spacing,
cutoff/volume persistence, continuum construction, same-object OS/GNS, the
Hamiltonian gap, and Clay closure remain open.

### 9.37 Post-audit implementation update: signed fully raw source aggregate, milestone 269 (2026-09-09)

The new `Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage.lean`
keeps the cancellation between positive fine Gibbs sources.  It forms the
literal finite sum

```text
sum_source fineNormalizedMass(source)
  * fullyRawEventCross(source)
      / ((rowZ(source)*Zc)*(Zf*Zc)),
```

omitting Gibbs-null rows before requesting any positive denominator witness.
This aggregate is proved exactly equal to the previous signed raw-row average
and hence to the normalized `centeredCylinderRemainder`.  Composing with the
existing positive partition-square cancellation also proves a two-way,
constant-preserving equivalence with the aggregate receiver-column raw-cross
calibration.  A schedule-level accessor then shows that the existing
matched-AF raw-column control supplies the fully raw aggregate calibration at
every controlled scale, with no additional hypothesis.

Therefore an aggregate `K*g^2` estimate is equivalent, without coefficient
loss, to the physical centered-remainder calibration.  This is strictly the
preferred interface over the sufficient pointwise fully raw premise because
it preserves source cancellation.  The pointwise premise is nevertheless
proved to imply the aggregate as a fallback.

No quadratic estimate is inhabited.  The active producer is a cutoff- and
volume-uniform bound on this signed aggregate, ideally from the established
receiver-column or posterior-contraction machinery.  The monitored leaf
target passes all 5,510 jobs, and all ten printed declarations depend
exactly on `[propext, Quot.sound]`.  No aggregate root pass is claimed.
Raw-event mismatch, lower physical spacing, cutoff/volume persistence,
continuum construction, same-object OS/GNS, the Hamiltonian gap, and Clay
closure remain open.

### 9.38 Post-audit implementation update: posterior producer for the fully raw aggregate, milestone 270 (2026-09-09)

The new
`Z4DyadicSpinFourGibbsRefreshConnectedFullyRawPosteriorColumn.lean` closes the
exact seam between the previously separate posterior-column and fully raw
branches.  The assignment-saturated raw-column cross and the accepted
receiver-fiber scale-defect cross are proved equal by observing that each,
after multiplication by the same positive `Z_coarse*Z_fine` factor, is the
physical raw covariance defect.  Positive-factor cancellation avoids any
new dependent receiver transport.

The receiver-fiber cross is already bounded by the three-term posterior
budget.  Its exact rescaling by `Z_coarse^2` now yields

```text
posteriorThreeBudget <= relative * Z_fine^2
  => |rawColumnCross| <= relative * (Z_coarse^2 * Z_fine^2),
```

with no cardinality factor or change of constant.  Hence the existing
`MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl` produces the
raw-column quadratic control and, through the signed-average equivalence,
the fully raw aggregate calibration at every controlled scale.

No posterior estimate is inhabited.  The active analytic edge is now the
cutoff- and volume-uniform `O(g^2)` control of the connected row loss and the
connected/disconnected posterior-column mismatches, rather than a separate
abstract aggregate premise.  The monitored leaf target passes all 5,511
jobs, and all four printed declarations depend exactly on
`[propext, Quot.sound]`.  No aggregate root pass is claimed.  Raw-event
mismatch, lower physical spacing, cutoff/volume persistence, continuum
construction, same-object OS/GNS, the Hamiltonian gap, and Clay closure
remain open.

### 9.39 Post-audit implementation update: signed posterior cancellation, milestone 271 (2026-09-09)

The posterior-to-fully-raw bridge now preserves the cancellation which the
three-term `l1` majorant discards.  The exact receiver-fiber posterior
identity, composed with the raw-column/receiver-fiber equality, proves

```text
rawColumnCross
  = connectedRowDebt
      + connectedPosteriorColumnDebt
      + disconnectedPosteriorColumnDebt.
```

A named calibration bounds the absolute value only after forming this signed
sum.  It is proved equivalent to the raw-column calibration and therefore to
the signed fully raw source-average calibration, in both directions with the
same quadratic constant.  No partition or receiver-cardinality factor is
lost.

The previously compiled separate row/column `l1` estimates remain a
sufficient fallback.  They are not the minimal physical hypothesis.  The
preferred active producer is now a cutoff- and volume-uniform `O(g^2)` bound
on the signed posterior debt sum itself.  The monitored leaf target passes
all 5,511 jobs, and all nine printed declarations depend exactly on
`[propext, Quot.sound]`.  No aggregate root pass is claimed.  Raw-event
mismatch, lower physical spacing, cutoff/volume persistence, continuum
construction, same-object OS/GNS, the Hamiltonian gap, and Clay closure
remain open.

### 9.40 Post-audit implementation update: coarse-square cancellation in the signed posterior seam, milestone 272 (2026-09-09)

The signed posterior frontier has been normalized one step further without
losing cancellation.  Two generic finite-dependent-transport lemmas show
that a common coefficient rescaling passes through the target coefficient
mass and the signed posterior-column defect.  In contrast to the existing
posterior-column `l1` rescaling theorem, the signed-defect result needs no
factor-sign assumption because no absolute value has yet been taken.

Applying these identities to the connected and disconnected literal
receiver transports gives the exact factorization

```text
signedPosteriorDebt
  = signedPosteriorDensityDebt * Z_coarse^2.
```

Consequently the former physical premise is equivalent to

```text
|signedPosteriorDensityDebt| <= K*g^2*Z_fine^2,
```

and hence, through milestones 269 and 271, to the same quadratic calibration
of the signed fully raw source aggregate.  The coarse partition square is
cancelled before the absolute value, so cancellation among the connected
row, connected posterior column, and disconnected posterior column remains
available to the analytic proof.

No density estimate is inhabited.  The active producer is now a cutoff- and
volume-uniform bound on this one normalized signed sum; componentwise `l1`
control remains a sufficient but stronger fallback.  The monitored leaf
target passes all 5,511 jobs.  The two generic declarations use only
`[propext]`, and the five new literal declarations use exactly
`[propext, Quot.sound]`.  No aggregate root pass is claimed.  Raw-event
mismatch, lower physical spacing, cutoff/volume persistence, continuum
construction, same-object OS/GNS, the Hamiltonian gap, and Clay closure
remain open.

### 9.41 Post-audit implementation update: posterior-density and connected-remainder join, milestone 273 (2026-09-09)

The normalized posterior frontier has now been joined to the pre-existing
Gibbs-refresh connected-observable frontier.  The assignment-saturated raw
column already had the two exact presentations

```text
rawColumnDefect = signedPosteriorDensityDebt * Z_coarse^2
rawColumnDefect = Z_coarse^2 * (refreshCross - productionCross).
```

Cancelling the strictly positive common factor before taking an absolute
value proves

```text
signedPosteriorDensityDebt
  = refreshCross - productionCross
  = Z_fine^2 * centeredCylinderRemainder.
```

The density-debt calibration is therefore equivalent both to the concrete
Gibbs-refresh physical-kernel cross calibration and to the centered-
remainder calibration, in both directions with the same quadratic constant.
The posterior-column expansion has not created a second analytic hypothesis:
it is another exact coordinate system for the already identified connected
remainder.

No quadratic estimate is inhabited.  The preferred active producer is the
cutoff- and volume-uniform `O(g^2)` centered-remainder bound; the signed
fine-law aggregate, unit-normalized two-premise recentering, and stronger
posterior componentwise `l1` route remain the existing decompositions of that
same obligation.  The monitored leaf target passes all 5,511 jobs, and all
four new bridge theorems depend exactly on `[propext, Quot.sound]`.  No
aggregate root pass is claimed.  Raw-event mismatch, lower physical spacing,
cutoff/volume persistence, continuum construction, same-object OS/GNS, the
Hamiltonian gap, and Clay closure remain open.

### 9.42 Post-audit implementation update: exact normalized margin factorization, milestone 274 (2026-09-09)

The cancellation-preserving unit-normalized recentering has now been refined
before any absolute-value estimate.  The exact finite identity

```text
1 - w^n = (1 - w) * geomSum(w,n)
```

is propagated through corrected-slab terms, the fine partition, pushed
receiver columns, pair products, the signed four-cell cross, and the
partition square.  The complete centered normalized-change numerator is
therefore exactly

```text
(1 - fineCoupling) * centeredNormalizedMarginNumerator.
```

This is a material improvement over separately bounding cross loss and
whole-partition drift: the residual numerator still contains their signed
cancellation.  A new dimensionless calibration asks only for

```text
|centeredNormalizedMarginNumerator| <= C * commonDenominator.
```

When the actual fine coupling is the matched-AF blocked weight, the already
proved `0 <= 1-w <= 2*g^2` estimate compiles any nonnegative ceiling `C` into
the existing raw centered-change calibration with ceiling `2*C`.

No volume-uniform ceiling is constructed, and the unit-normalized
coupling-one blocking residual remains a second signed analytic producer.
The result is an exact localization of the open estimate, not a continuum or
mass-gap claim.  The monitored leaf target passes all 5,498 jobs, and all
eleven printed declarations depend exactly on `[propext, Quot.sound]`.
Cutoff/volume persistence, continuum construction, same-object OS/GNS, the
Hamiltonian gap, and Clay closure remain open.

### 9.43 Post-audit implementation update: balanced raw defect to normalized residual, milestone 275 (2026-09-09)

The unit-normalized blocking residual introduced by the cancellation-
preserving recentering is now proved to be an exact normalization of the
already existing balanced coupling-one raw scale defect:

```text
coarseCovariance - unitNormalizedPushedCross
  = balancedRawScaleDefect / (Z_coarse^2 * Z_unit^2).
```

The new module proves the missing coarse four-cell quotient identity and the
strict positivity of this denominator.  Below coupling one the actual fine
partition is bounded by the coupling-one partition, so the stronger prior
calibration normalized by `Z_coarse^2 * Z_actual^2` transports to the
unit-normalized residual with no loss in its constant.

Together with the exact margin factorization from milestone 274, this yields

```text
|centeredCylinderRemainder|
  <= (C_balanced + 2*C_margin) * g^2
```

from precisely two raw premises: a balanced blocking calibration and a
signed centered margin-quotient calibration.  No premise is inhabited; the
result consolidates the analytic frontier rather than closing it.  The
monitored leaf target passes all 5,501 jobs, and all six printed declarations
depend exactly on `[propext, Quot.sound]`.  Cutoff/volume persistence,
continuum construction, same-object OS/GNS, the Hamiltonian gap, and Clay
closure remain open.

### 9.44 Post-audit implementation update: centered receiver-pair margin debt, milestone 276 (2026-09-09)

The residual signed geometric-quotient numerator from milestone 274 is now
identified exactly with a selected cross of a centered receiver-pair debt.
At one coarse target pair the debt is

```text
pairMarginMass * Z_actual^2
  - actualPairMass * partitionSquareMargin.
```

Exact finite-sum identities show that its total over the complete coarse
target-pair carrier is zero.  The source four-cell debt minus the opposite
target four-cell debt is precisely the cancellation-preserving normalized
margin numerator.  Bounding this selected mass-zero debt cross is therefore
equivalent to the existing margin calibration with no change of constant.

This removes the interpretation of whole-partition drift as an independent
positive loss; it is the centering component of the signed pair measure.
The theorem does not inhabit the volume-uniform bound.  The two active
analytic producers are still the balanced blocking calibration and the
selected centered-debt-cross calibration.  Cutoff/volume persistence,
continuum construction, same-object OS/GNS, the Hamiltonian gap, and Clay
closure remain open.  The monitored leaf target passes all 5,502 jobs.  Nine
printed declarations depend exactly on `[propext, Quot.sound]`, and the pair
carrier definition depends on no axioms.

### 9.45 Post-audit implementation update: fine-source pullback of centered margin debt, milestone 277 (2026-09-09)

The selected centered receiver-pair debt cross is now pulled back exactly
through the literal independent two-replica product kernel.  The resulting
identity is

```text
centeredNormalizedMarginNumerator
  = sum_finePair centeredSourcePairDebt(finePair)
      * (P_K^2(source cell | finePair) - P_K^2(target cell | finePair)).
```

The centered source-pair debt has exactly zero total mass.  The coarse
target-pair margin, actual mass, and centered debt are its exact
product-kernel pushforwards, while each selected output-cell probability is
in `[0,1]`; hence the product-kernel output contrast has pointwise absolute
value at most one.  Bounding this signed fine-source average is exactly
equivalent to the prior normalized margin calibration with no constant loss.

This is a localization, not an inhabited uniform estimate.  The active
analytic producers remain the volume-uniform balanced blocking calibration
and a volume-uniform bound on the signed fine-source average that preserves
both cancellations.  A full source-debt `L1` estimate is stronger and may be
volume-extensive.  Cutoff/volume persistence, continuum construction,
same-object OS/GNS, the Hamiltonian gap, and Clay closure remain open.  The
monitored leaf target passes all 5,503 jobs, and all 17 printed load-bearing
declarations depend exactly on `[propext, Quot.sound]`.

## 10. What this changes—and what it does not

This investigation changes the priority order:

- **More valuable now:** a boundary-tensor positive carrier, exact joint
  coarse-intertwiner transport, grouped physical-distance projective
  diameter, and shared-object maps.
- **Less valuable now:** larger multiplicity-only central-monad tables,
  more one-face Birkhoff tests, more isolated finite Bernstein windows, or
  more conditional interfaces with surrogate witnesses.

It does **not** prove (DP), a Birkhoff contraction, RG-I7--I9, the continuum
limit, OS reconstruction for the physical limit, or a Yang--Mills spectral
gap.  Its contribution is to identify which historical simplifications are
harmless coordinate changes and which ones discard exactly the data the
remaining proof needs.

---

# Part III. Evidence and sources

## 11. Repository evidence

The most important local evidence for the ranking is:

- `docs/birkhoff-fusion-clay-closure-plan-2026-07-24.md` — BF1--BF10 and
  the grouped physical-distance contraction target;
- `notes/su2k-central-monad-campaign.md` — exact degree-zero comparison,
  heat-weight failure of module naturality, loss of counit/multiplication
  maps, and the \(k+1\) central-vacuum growth;
- `notes/fusion-pair-heat-census.md` — 100/100 intersecting pair orbits
  physically heat-positive despite negative fixed channels;
- `notes/local-face-birkhoff-census.md` — raw one-face support holes and
  infinite projective diameter;
- `docs/clay-open-boundary-ledger.md` and
  `lean/YMGap/Rubric/ClayTargetPinned.lean` — the unconstructed continuum
  measure, covariance, same-object reconstruction, and spectral gap;
- `docs/continuum-map.md` — the four live formal dependency chains;
- `notes/fiducials_notes.md`, `docs/multiscale-2026-07-07.md`, and
  `docs/largefield-2026-07-07.md` — the exact boundary of the Bałaban-shaped
  inputs;
- `docs/q-representability-audit.md` and
  `formal/sub_papers/README.md` — the distinction between squared rational
  Racah kernels and signed \(6j\) coherence;
- `docs/theta-inversion-2026-07-08.md` — the removal of an unnecessary
  Poisson/modular residual;
- `formal/references.bib` — the repository's primary bibliography.

## 12. External sources checked

Primary or publisher-hosted sources were preferred.

1. Arthur Jaffe and Edward Witten,
   [*Quantum Yang--Mills Theory* (official Clay problem
   description)](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf).
   This fixes the target and records the Wightman/Euclidean reconstruction
   lineage.
2. Kenneth Wilson,
   [*Confinement of Quarks*](https://doi.org/10.1103/PhysRevD.10.2445)
   (1974), introducing the lattice gauge framework used here.
3. David Gross and Frank Wilczek,
   [*Asymptotically Free Gauge Theories I*](https://doi.org/10.1103/PhysRevD.8.3633),
   and H. David Politzer,
   [*Reliable Perturbative Results for Strong
   Interactions?*](https://authors.library.caltech.edu/records/fm8ka-55a61)
   (1973).
4. Konrad Osterwalder and Robert Schrader,
   [*Axioms for Euclidean Green's
   Functions*](https://doi.org/10.1007/BF01645738) (1973): necessary and
   sufficient Euclidean conditions for a unique Wightman theory.
5. Irving Segal,
   [*Irreducible Representations of Operator
   Algebras*](https://www.ams.org/journals/bull/1947-53-02/S0002-9904-1947-08742-5/)
   (1947), a source for the GNS lineage.
6. Garrett Birkhoff,
   [*Extensions of Jentzsch's
   Theorem*](https://www.ams.org/tran/1957-085-01/S0002-9947-1957-0087058-6/)
   (1957), applying Hilbert's projective metric to positive kernels and
   contraction/fixed-point arguments.
7. Roman Kotecký and David Preiss,
   [*Cluster Expansion for Abstract Polymer
   Models*](https://doi.org/10.1007/BF01211762) (1986).
8. Tadeusz Bałaban,
   [*Renormalization Group Approach to Lattice Gauge Field
   Theories I*](https://doi.org/10.1007/BF01215223) (1987), and
   [*Convergent Renormalization Expansions for Lattice Gauge
   Theories*](https://doi.org/10.1007/BF01217741) (1988).
9. Mark Kac and John Ward,
   [*A Combinatorial Solution of the Two-Dimensional Ising
   Model*](https://doi.org/10.1103/PhysRev.88.1332) (1952), and Pieter
   Kasteleyn,
   [*Dimer Statistics and Phase
   Transitions*](https://doi.org/10.1063/1.1703953) (1963).
10. A. A. Migdal,
    [*Recursion Equations in Gauge Field
    Theories*](https://jetp.ras.ru/cgi-bin/dn/e_042_03_0413.pdf) (1975);
    B. E. Rusakov,
    [*Loop Averages and Partition Functions in \(U(N)\) Gauge Theory on
    Two-Dimensional Manifolds*](https://doi.org/10.1142/S0217732390000780)
    (1990); and Edward Witten,
    [*On Quantum Gauge Theories in Two
    Dimensions*](https://doi.org/10.1007/BF02100009) (1991).
11. Azat Gainutdinov, Jonas Haferkamp, and Christoph Schweigert,
    [*Davydov--Yetter Cohomology, Comonads and Ocneanu
    Rigidity*](https://arxiv.org/abs/1910.06094) (2019), and Pavel Etingof,
    Dmitri Nikshych, and Viktor Ostrik,
    [*On Fusion
    Categories*](https://doi.org/10.4007/annals.2005.162.581) (2005).

## 13. Final audit statement

The most important historical simplification to reverse is not
“lattice \(\rightarrow\) continuum” or “nonabelian \(\rightarrow\) abelian.”
It is more local:

\[
\boxed{
\text{positive physical Haar boundary object}
\;\longrightarrow\;
\text{signed channels}
\;\longrightarrow\;
\text{multiplicity ledger}
}
\]

The repository's exact evidence says the first arrow can create apparent
signs that disappear after complete physical grouping, while the second
arrow loses the maps needed for blocking.  Reversing those losses, while
using a scale-dependent grouped Hilbert metric, is the highest-leverage
mathematical course now visible.  Even if it succeeds, the resulting RG
theorem must still be carried through BF7--BF10 on one shared continuum
object before it is a solution of the Yang--Mills mass-gap problem.
