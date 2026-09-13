# Constructive Yang--Mills mass-gap formalization

> **Research status (2026-09-13): this repository does not prove the Clay
> Yang--Mills existence and mass-gap theorem.** It contains kernel-checked
> finite-lattice and strong-coupling results, explicit proof compilers, and an
> honest ledger of the bridges that remain open.

This project is a Mathlib-free Lean 4 formalization of a constructive route
from four-dimensional lattice gauge theory to continuum quantum Yang--Mills.
The active concrete data are SU(2) BF4 lattice data. The positive
multiplicity-product conditional model and the signed exact-Haar model are
distinct; the former's gap is not a gap theorem for the latter. Existence
statements carry witnesses and explicit moduli; numerical exploration is not
part of the trusted proof.

## Whole-project goal

The Clay target requires a non-trivial quantum Yang--Mills theory on
`R^4`, satisfying suitable QFT axioms, with an isolated vacuum and a uniform
mass gap `Delta > 0` for every compact simple gauge group. The repository is
currently pursuing SU(2) as the concrete non-abelian construction; a valid
all-group lift remains separate work.

```text
WHOLE-PROJECT GOAL / CLAY TARGET
Continuum 4D Yang--Mills + QFT axioms + isolated vacuum + Delta > 0
for every compact simple gauge group, in Lean within the MLTT/HoTT gate
                                  |
                   EXPAND into necessary inputs
                                  v
CURRENT CONDITIONAL BRANCH: positive multiplicity-product law
  finite contraction, 0<w<=1/2 and K>=K0(w); rate depends on w      [PROVED]
    + cutoff limit + reflected marginal completion                 [PROVED]
    -> completed gap / decay / vacuum isolation at w=1/400, extent 1 [PROVED]
                                  |
        identity with the ORIGINAL signed exact-Haar law
                                  X                               [REFUTED]
        The original vacuum-delta quadratic is 1; the positive-law
        value is strictly smaller, every w>0 and K>=1.
        NO causal arrow from this identity to a Yang--Mills gap.

REQUIRED PHYSICAL ROUTE: ORIGINAL signed SU(2) slab law
  original weights, signed boundary sums, same Haar carrier        [PROVED]
       |
       +--> full Haar pin + literal U = theta(L)
       |      + lower locality + actual square channels            [PROVED]
       |      -> ORIGINAL mixed Gram identity
       |      -> symmetry + positivity, all odd extents, w>=0      [PROVED]
       |                       |
       |                       +----------------------------------+
       |                                                          |
       +--> exposed links + four swaps + harmonic degree selection |
              + SAME boundary zero extension                       |
              -> ORIGINAL full bilinear cutoff limit              |
                 + computed pair-dependent modulus                [PROVED]
                                  |                               |
                                  +<---- BOTH inputs --------------+
                                  v
  One common original GNS form per odd slab, w>=0                   [PROVED]
    -> null quotient + constructive CReal Hilbert completion       [PROVED]
    -> all cutoff anchors in that slab share ONE completed carrier [PROVED]
       with exact original finite/limit inner-product pins         [PROVED]
                                  |
                                  +<-- all-extent norm-one,
                                  |    non-null boundary CODE       [PROVED]
                                  |      -> code-centered completed
                                  |         pairing = original
                                  |         finite code covariance  [PROVED]
                                  +--> full heat-unit sequence:
                                  |    ORIGINAL three-cutoff pairing[PROVED]
                                  |      + original face remainders
                                  |        with w-dependent moduli  [PROVED]
                                  |      -> shared-variable product
                                  |         remainder + norm pin    [PROVED]
                                  |      -> growing-unit GNS Cauchy
                                  |         + explicit modulus      [PROVED]
                                  |      -> completed full unit     [PROVED]
                                  |         for each 0<w<1, odd slab
                                  |      + full action-integral limit
                                  |      + vanishing interface error[PROVED]
                                  |      -> completed squared norm
                                  |         = ORIGINAL action limit [PROVED]
                                  |      -> finite-floor criterion
                                  |         and nonzero consequence [PROVED]
                                  |      + retained original channel
                                  |         Z_K >= lowerHaar_K^2    [PROVED]
                                  |      -> lower-half finite margin
                                  |         suffices for full floor [PROVED]
                                  |      + differentiated JTP
                                  |        + Euler prefix/tail floor
                                  |        + first positive S term  [PROVED]
                                  |        -> original heat floor
                                  |           c(w)>0 on [-1,1]      [PROVED]
                                  |        + finite derivative error
                                  |          with computed cutoff   [PROVED]
                                  |        -> late character prefixes
                                  |           >= c(w)/2             [PROVED]
                                  |        + exact face evaluation  [PROVED]
                                  |          + scalar boxes at the
                                  |            common environment    [INPUT]
                                  |        -> shared-link product
                                  |           pointwise floor b(w)^F[PROVED]
                                  |      + actual Haar-unit holonomy
                                  |        -> four-square certificate
                                  |           for 1+face scalar     [PROVED]
                                  |      + finite Jacobi derivative
                                  |        has nonnegative shifted
                                  |        coefficients, constant>=c[PROVED]
                                  |        -> SAME shared-link Haar
                                  |           approximant floor c^F [PROVED]
                                  |        + coefficient-level pin
                                  |          to weighted heat terms [PROVED]
                                  |        -> same floor for WEIGHTED
                                  |           original face-product [PROVED]
                                  |        + finite-band weight loss
                                  |          + original coefficient tail
                                  |          + shared-link telescope[PROVED]
                                  |        -> quantified Haar passage
                                  |           to ORIGINAL heat action[PROVED]
                                  |      -> strict positive floor
                                  |         for THAT action limit   [PROVED]
                                  |      -> successful finite certificate
                                  |         + non-null full heat unit[PROVED]
                                  |      -> explicit reciprocal of Z
                                  |         with positive bounds    [PROVED]
                                  |      -> SAME completed pairing / Z
                                  |         + full unit norm one
                                  |         + norm/rate comparison  [PROVED]
                                  |      + original action with
                                  |        arbitrary polynomial p
                                  |        + insertion-tail modulus [PROVED]
                                  |        + same-link positive
                                  |          approximants and limit [PROVED]
                                  |      -> E(p)=N(p)/SAME Z
                                  |         + E(1)=1 + E(p^2)>=0
                                  |         + explicit real modulus [PROVED]
                                  |      + concrete lower plaquette
                                  |        algebra + literal reflection
                                  |        + temporal Haar pin       [PROVED]
                                  |      -> SAME full-action reflected
                                  |         numerator = square value [PROVED]
                                  |      -> E(theta(p)*p)>=0
                                  |         + reflected unit = 1     [PROVED]
                                  |      + ORIGINAL action reflection
                                  |        invariance at every cutoff[PROVED]
                                  |      -> finite plaquette GNS / CS[PROVED]
                                  |        + original numerator limits
                                  |          + SAME positive Z       [PROVED]
                                  |      -> normalized reflected form
                                  |         symmetric, bilinear, CS
                                  |         + norm-null descent
                                  |         + explicit real modulus [PROVED]
                                  |      -> actual null quotient
                                  |         + positive-definite form[PROVED]
                                  |      -> Cauchy completion CARRIER
                                  |         + injective embedding
                                  |         + nonzero unit          [PROVED]
                                  |      + explicit pairing tolerance
                                  |        + computed Cauchy bounds
                                  |        + two-level limit moduli [PROVED]
                                  |      -> completed mixed pairing
                                  |         + representative descent
                                  |         + original-form pin
                                  |         + symmetry/positivity
                                  |         + unit diagonal one     [PROVED]
                                  |      + explicit addition/scaling
                                  |        continuity tolerances    [PROVED]
                                  |      -> completed rational linear
                                  |         laws + bilinearity      [PROVED]
                                  |      + pairing rate controls
                                  |        distance to its limit    [PROVED]
                                  |      -> completed norm zero
                                  |         iff completed state zero[PROVED]
                                  |      +--> original CS + product
                                  |      |    continuity through limits[PROVED]
                                  |      |    -> sharp completed CS
                                  |      |       + distance geometry [PROVED]
                                  |      |    -> explicit approximants
                                  |      |       from supplied reps [PROVED]
                                  |      |    -> represented-row limits
                                  |      |       + computed rate
                                  |      |       + row independence [PROVED]
                                  |      |
                                  |      +--> supplied scalar QCauchy data
                                  |           + computed tail ceilings
                                  |           -> SAME real-scalar action
                                  |              + representative descent
                                  |              + arithmetic laws/moduli
                                  |              + distance scaling [PROVED]
                                  |      + SAME pairing modulus
                                  |        + original unit norm one [PROVED]
                                  |      -> P(x)=<x,u>u; C(x)=x-P(x)
                                  |         + orthogonal projections
                                  |         + Pythagoras / no norm loss[PROVED]
                                  |      + literal mean E(p) pin
                                  |      -> <C(p),C(q)> equals
                                  |         E(theta(p)q)-E(p)E(q)
                                  |         + explicit real modulus [PROVED]
                                  |      + original approximants/rows
                                  |      -> centered approximation
                                  |         + represented-row limits[PROVED]
                                  |      + original square-tree channels
                                  |        -> two distinct retained leaves
                                  |        -> centering-invariant minor
                                  |        -> finite raw norm floor [PROVED]
                                  |      + fundamental coordinate leaves
                                  |        -> literal plaquette-boundary
                                  |           channels + heat weights[PROVED]
                                  |      + reference Haar mixed moment
                                  |        = 1/128; determinant nonzero[PROVED]
                                  |      + original heat-dressed
                                  |        four-moment identity      [PROVED]
                                  |      + small-nome face guards
                                  |        -> shared-link moment error
                                  |           bound, independent of K[PROVED]
                                  |      + w=1/1024, extent-one
                                  |        kernel guard certificate
                                  |        -> D <= -1/1024, every K [PROVED]
                                  |        -> concrete positive minor
                                  |           for every K>=1         [PROVED]
                                  |        -> one raw norm floor,
                                  |           every K>=1 and center c[PROVED]
                                  |      + SAME action reciprocal
                                  |        + cutoff/centering limits [PROVED]
                                  |      -> nonzero centered observable
                                  |         + positive normalized floor
                                  |         + norm Cauchy modulus,
                                  |         at THAT w and slab       [PROVED]
                                  |      + actual geometric face maps
                                  |        + independent padding/lags
                                  |        -> original time-separated
                                  |           connected correlations
                                  |           = completed pairings,
                                  |           with Cauchy moduli     [PROVED]
                                  |      + space AND time placement
                                  |        + explicit boundary margin
                                  |        -> ORIGINAL bulk correlations
                                  |           = completed pairings  [PROVED]
                                  |      + actual embedded face list
                                  |        + exterior face complement
                                  |        -> exact ORIGINAL action
                                  |           = interior * exterior [PROVED]
                                  |        -> boundary covariance D
                                  |           + same-cutoff modulus
                                  |           + limit comparison
                                  |             E_full(p) I(1)-I(p)
                                  |               = D(p)/Z_full     [PROVED]
                                  |      + injective actual link map
                                  |        + Haar/ordered action pins
                                  |        -> I(embed p) = N_small(p)
                                  |           I(1) = Z_small        [PROVED]
                                  |        + BOTH original reciprocals
                                  |        -> E_large(embed p)-E_small(p)
                                  |           = D/(Z_large Z_small) [PROVED]
                                  |           for actual bulk means,
                                  |           with Cauchy data      [PROVED]
                                  |      + original unit holonomies
                                  |        + computed square bounds
                                  |        + positivity and E(1)=1
                                  |        -> original bulk means,
                                  |           OS/centered norms and
                                  |           correlation SIZE bounds
                                  |           independent of w/padding
                                  |           for fixed expressions [PROVED]
                                  |      + all-spin Haar certificates
                                  |        + ORIGINAL Casimir weights
                                  |        + explicit small-nome guard
                                  |        -> one-face remainder
                                  |           delta(w)=128*w^3,
                                  |           all K and extents     [PROVED]
                                  |        + constructed ORIGINAL
                                  |          positive face backgrounds
                                  |        -> ONE-face integral factors
                                  |           1-delta(w),1+delta(w)
                                  |           independent of volume [PROVED]
                                  |      + exact finite face selections
                                  |        + shared-link interval products
                                  |        -> ORIGINAL activities bounded
                                  |           by delta(w)^n          [PROVED]
                                  |      + literal face-link locality
                                  |        + original Haar factorization
                                  |        -> disconnected-split connected
                                  |           numerator cancels     [PROVED]
                                  |      + actual exterior selections
                                  |        -> EXISTING boundary D equals
                                  |           sum of selection responses
                                  |           at the SAME cutoff    [PROVED]
                                  |        -> empty / entirely detached
                                  |           selections vanish     [PROVED]
                                  |      + finite inclusion-exclusion
                                  |        of ORIGINAL connected numerator
                                  |        + computed selected-face cuts
                                  |        -> separated coefficients vanish
                                  |           even in interacting slabs
                                  |        -> SAME boundary D: exterior sum
                                  |           of filtered interior sums
                                  |           with no separating cut [PROVED]
                                  |      + SAME two-copy Haar moment form
                                  |        + exact three-term insertion
                                  |        -> ACTUAL coefficient bound
                                  |           2*c_p*c_q*kappa(w)^n,
                                  |           kappa=2*delta+delta^2 [PROVED]
                                  |        -> original boundary D has a
                                  |           computed finite majorant
                                  |           independent of cutoff [PROVED]
                                  |      + ANCHORED spectator families:
                                  |        exact signed resummation
                                  |        -> original spectator Z^2
                                  |        + computed detached/collar split
                                  |        + removed-face partition cost
                                  |        -> F^2*|family| <= cap*Z^2 [PROVED]
                                  |      + global ordered family decomposition
                                  |        + collar / path-length counting
                                  |        + boundary mixed normalization
                                  |        + normalized summability  [OPEN]
                                  |      + quantitative control of
                                  |          NORMALIZED response    [OPEN]
                                  |      + padding limit and genuine
                                  |        time homogeneity         [OPEN]
                                  |      + full quotient-level
                                  |        completeness              [OPEN]
                                  |      + physical realization and
                                  |        observable-action maps    [OPEN]
                                  |      + all required gauge observables
                                  |        beyond this subalgebra     [OPEN]
                                  |      + physical vacuum
                                  |        identification             [OPEN]
                                  +<-- larger-slab compatibility      [OPEN]
                                  +<-- physical observable/unit
                                  |    realization                    [OPEN]
                                  v
  One physical positive-time completed carrier                     [OPEN]
                                  |
                                  +<-- geometric time / transfer      [OPEN]
                                  +<-- stationary physical vacuum     [OPEN]
                                  +<-- strict bound on ITS completed
                                  |    vacuum complement              [OPEN]
                                  v
  Physical spectral gap on the SAME objects                         [OPEN]
                                  |
                                  +<-- volume + spacing mass control  [OPEN]
                                  +<-- constructive limits + QFT      [OPEN]
                                  +<-- remaining compact simple groups[OPEN]
                                  v
                 CONTRACT through proved same-object bridges
Continuum 4D Yang--Mills + QFT axioms + isolated vacuum + Delta > 0
WHOLE-PROJECT GOAL / CLAY TARGET

Scope: arbitrary signed boundary coefficients; original overlapping links.
Finite-slab positivity is not a strict gap, compatibility or continuum limit.
The normalized FULL heat unit is not yet a stationary physical vacuum.
```

`INPUT` marks an explicit hypothesis, not a discharged prerequisite.
`PROVED` means kernel-checked at exactly the displayed scope. It does not mean
that downstream arrows have been proved. `PARTIAL` means concrete objects and
useful theorems exist but a required bridge is missing.

## Current frontier

**Route correction: the literal exact-Haar/positive-law identity is
refuted, not an open identity to prove.** The preceding roadmap mislabeled
`ExactHaarPhysicalPerronSameActionAt` as an available next bridge. The
repository already refutes it at cutoff one and every positive coupling:
[`exactHaarPhysicalPerronSameActionAt_cutoffOne_uninhabited`](lean/YMGap/Continuum/BF4ExactPhysicalPerronSameActionFence.lean#L565).
The canonical `[BF4-exact-physical-Perron]` ledger entry already records
this obstruction. The completed conditional gap remains valid for its
own operator; it cannot cross that refuted identity.

**Latest result: exact spectator resummation with an ORIGINAL partition-relative bound.**
[`spectatorSum_pin`](lean/YMGap/Continuum/BF4ExactSlabSpectatorResummation.lean#L114)
sums signed spectator coefficients before taking absolute values and returns
`anchor coefficient * Z_spectator^2`, with the original Haar partition.
The detached spectator faces and their removed collar are computed from
literal probe/anchor links; their partition and disjointness are proved.

[`relative_floor`](lean/YMGap/Continuum/BF4ExactSlabRelativePartitionBound.lean#L50)
proves `(1-delta)^|removed| Z_background <= Z_full`, retaining shared links.
Combined with resummation,
[`detached_cleared_bound`](lean/YMGap/Continuum/BF4ExactSlabResummedCoefficientBound.lean#L72)
gives `F^2 |family| <= anchorCap * Z_ambient^2`, where
`F=(1-delta(w))^(collar size)` and `anchorCap=2*c_p*c_q*kappa(w)^|anchor|`.
The loss counts removed faces, not spectator faces. The explicit small-nome
guards remain, with `delta<=1`; `F>0` is checked for every finite collar at
the existing `w=1/1024` pilot.

**Scope and next step:** this is an anchored-family estimate, not a global
reorganization of the boundary numerator. The boundary-insertion
specialization uses the INTERIOR partition square, not the boundary
comparison's mixed denominator `Z_large*Z_small`. Global ordered family
decomposition, collar/path counting, mixed normalization and summability
remain open, before distance decay, padding limits and the physical/Clay gap.
Five modules, 4+8+6+7+6=31 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: actual connected-coefficient bounds and an ORIGINAL boundary majorant.**
[`connectedCoefficient_bound`](lean/YMGap/Continuum/BF4ExactSlabConnectedCoefficientBound.lean#L74)
bounds the existing inclusion–exclusion coefficient by `2*c_p*c_q*kappa(w)^n`,
where `c_p,c_q` are constructed Haar interval caps and
[`kappa(w)=2*delta(w)+delta(w)^2`](lean/YMGap/Continuum/BF4ExactSlabConnectedCoefficientBound.lean#L45),
with `delta(w)=128*w^3`. It holds at every cutoff and extent under
`0<=w<=1` and `(2*w^3)*16<=1/2`. The general guard does **not** imply
`kappa<1`; strict smallness is kernel-checked at the existing `w=1/1024` pilot.

The proof identifies the actual coefficient with repeated simultaneous
insertions into the original two-copy Haar moment form. Each step has exactly
three terms: remainder in the left copy, right copy, or both. This proves the
new bound rather than borrowing a single-copy activity estimate.

[`boundarySummand_bound`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCoefficientBound.lean#L63)
gives `2*c_p*delta(w)^|S|*kappa(w)^|T|` for each exterior/interior selection
pair. [`boundaryNumerator_bound`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCoefficientBound.lean#L86)
sums those caps over the actual separating-cut filtered expansion, producing
a computed finite bound for the EXISTING boundary numerator with **no cutoff
parameter**. Volume, nome and probe support/cap remain explicit.

**Next:** handle disconnected spectator pieces together with the original
partition factors, and prove geometric counting and normalized summability.
The finite majorant is not volume-uniform or a distance-decay bound. No
padding limit, physical gap or continuum/Clay theorem is proved here.
Five modules, 7+8+9+6+7=37 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: selected-cut cancellation reaches the ORIGINAL boundary response.**
[`boundaryNumerator_connecting_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundaryConnectingSelections.lean#L85)
is an exact double finite expansion of the existing boundary numerator:
exterior remainder selections, then interior inclusion–exclusion coefficients
filtered by a computed separating-cut search. The same probe, action, cutoff,
Haar carrier and determinant factors are retained.

[`coefficient_zero_of_separator`](lean/YMGap/Continuum/BF4ExactSlabConnectedSelectionExpansion.lean#L83)
proves a coefficient is zero whenever its selected faces admit a cut between
the probes. Every subselection inherits the separator and its original
connected numerator vanishes. Thus the FULL interior may remain interacting;
detachment from the entire interior is no longer required for this cancellation.
[`findSeparator`](lean/YMGap/Continuum/BF4ExactSlabSelectionSeparation.lean#L103)
returns an actual cut with a disjoint-support proof; retained selections
[`have no enumerated separating cut`](lean/YMGap/Continuum/BF4ExactSlabConnectedSelectionExpansion.lean#L102).
The search is exhaustive finite enumeration, not an efficient cluster algorithm.

**Next:** bounds on these inclusion–exclusion coefficients, geometric
path-length control and normalized summability yielding separation decay.
The previous `delta(w)^n` bounds concern remainder activities, not these new
coefficients; no such bound is inferred. No distance-decay, padding-limit,
physical-gap or continuum/Clay theorem is proved by this finite identity.
Four modules, 9+15+9+4=37 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: an exact expansion of the ORIGINAL boundary response.**
[`boundaryNumerator_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundarySelectionExpansion.lean#L92)
expresses the existing boundary numerator as a finite sum of actual exterior
face-selection responses. The interior action, probe, shared links, common
cutoff and partition factors are retained. This is an identity for the
tracked physical quantity, not a replacement correlation model.

[`moment_expansion`](lean/YMGap/Continuum/BF4ExactSlabRemainderExpansion.lean#L53)
and `partition_expansion` expand the original moments and partition into
products of original heat remainders. Under the explicit small-nome guard,
[`activity_bound`](lean/YMGap/Continuum/BF4ExactSlabRemainderExpansion.lean#L81)
gives `delta(w)^n` for each selection of `n` faces, at every cutoff and
extent, even when faces share links. `original_background_bound` retains
the same positive original background integral on the right-hand side.

Literal face-link locality and original Haar factorization give
[`connectedNumerator_zero`](lean/YMGap/Continuum/BF4ExactSlabDisconnectedHaarCancellation.lean#L122)
for a supplied disjoint split, including all four moment/partition factors.
In the boundary expansion, empty selections and selections detached from
the **entire interior/probe region** contribute exactly zero.

**Next mathematical frontier:** connecting-selection reorganization and
normalized summability that yield decay with probe-to-boundary distance.
The proved detachment condition is stronger than being far from the probe;
counting all selections can still grow with volume. No distance-decay,
padding-limit, physical-gap or continuum/Clay claim follows yet.
Six modules, 6+8+12+14+7+6=53 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: local heat-weight comparisons on the ORIGINAL action.**
[`faceRemainderInterval`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean#L54)
constructs both signs of the original face-remainder bound under Haar
integration, retaining shared links. The explicit cap is
[`delta(w)=128*w^3`](lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean#L85),
at every representation cutoff and physical face in every finite slab,
under `0<=w<=1` and `(2*w^3)*16<=1/2`.

With `delta(w)<=1`, the actual original heat factors and their finite products
receive constructed positivity certificates.
[`originalBackground_comparison`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean#L160)
then proves that inserting one face multiplies any such background integral
by factors bounded between `1-delta(w)` and `1+delta(w)`. These factors do not
depend on cutoff, volume or the number of background faces. No link
independence or substitute probability law is used. The existing `w=1/1024`
pilot satisfies both guards by kernel calculation.

**Boundary of this result:** the finite-product floor `(1-delta(w))^F`
depends on the number of faces `F`; it is not a volume-uniform partition
floor. The local comparison has no separation factor. Quantitative
normalized boundary decay, padding convergence, nonzero-norm persistence,
physical transfer/gap and the continuum/Clay target remain open.
Three modules, 10+12+10=32 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic inputs,
numerical oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: uniform observable-size bounds on the ORIGINAL action.**
The computed [`bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformSquareBound.lean#L33)
depends only on an expression's spins, rational coefficients and operations.
Constructed sum-of-squares certificates bound its actual lower and reflected
upper polynomials; they retain all shared link variables. Positivity of the
original action and exact normalization then give
[`form_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L98)
and [`connected_norm_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L108).
No full-action coefficient bound or partition-reciprocal ceiling enters these estimates.

[`bound_bulkAtTime`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformSquareBound.lean#L69)
proves that padding and admissible time displacement leave the cap unchanged.
[`bulk_completed_norm_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L134)
bounds the actual completed centered state at every padding, and
[`bulk_correlation_square_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L141)
proves `C_bulk(e,f)^2 <= bound(e) * bound(f)` at any two admissible lags.
All rational `0<w<1` and finite odd slabs are quantified; means are bounded
on both sides by `bound(e)+1`. The cap is deliberately coarse, not optimal.

**Scope and next step:** these are a priori size bounds, with NO decaying
distance factor and NO norm-relative `q<1`. They do not prove boundary
insensitivity, persistence of a positive excitation norm, padding convergence,
bounded time descent, a physical gap, or the continuum/Clay target. Existing
cutoff moduli keep their parameter dependence; no uniform padding modulus
is claimed. Next remains quantitative normalized boundary-response control.
Three new modules: 21+6+15=42 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic inputs, numerical
oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: exact comparison of ORIGINAL expectations in two slabs.**
An explicit injective map places each source link in the larger slab.
[`haar_embedding`](lean/YMGap/Continuum/BF4ExactSlabBulkHaarEmbedding.lean#L145)
proves that unused target variables integrate to one; the same map preserves
the original ordered plaquette words, all-spin characters and heat action.
[`interiorLimit_small`](lean/YMGap/Continuum/BF4ExactSlabBulkInteriorHaarPin.lean#L148)
identifies the interior-weighted target integral with the original smaller
slab integral, after cutoff removal.
[`interiorPartition_small`](lean/YMGap/Continuum/BF4ExactSlabBulkInteriorHaarPin.lean#L157)
identifies its normalization with the original smaller partition function.

Combining those identities with the previous exact boundary response gives
[`expectationDifference_formula`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L115):
`E_large(embed p) - E_small(p) = D(embed p)/(Z_large Z_small)`.
Both partition reciprocals are constructed, not assumed. The
[`bulk_mean_comparison`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L136)
specialization uses the actual bulk-translated original plaquette expressions.
[`expectationDifferenceCauchy`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L132)
retains explicit representative-index modulus data at each fixed pair of slabs.

**Next:** quantitative control of this normalized response for deep-interior
observables, retaining the nome, volume, insertion and partition factors.
The identity does not assert smallness, volume-uniform reciprocal bounds,
padding convergence, persistence of the nonzero seed, time homogeneity or
a physical spectral gap. The continuum/Clay target remains open. Five new
modules: 23+14+12+9+7=65 exact focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic assumptions,
numerical constants, oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: bulk placement and an exact ORIGINAL boundary-response identity.**
The new geometry shifts all three spatial coordinates as well as time.
[`paddingForMargin_bound`](lean/YMGap/Continuum/BF4ExactSlabBulkEmbeddingGeometry.lean#L197)
proves that padding `lag+radius` places every translated plaquette-edge
endpoint at least `radius` from all box boundaries. The observable map uses
the existing original expression algebra;
[`bulkCorrelation_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteBulkEmbedding.lean#L147)
identifies its connected correlations with the actual completed centered
pairings at that stage.

[`fullHeatProduct_dressing`](lean/YMGap/Continuum/BF4ExactSlabBulkActionDressing.lean#L107)
partitions the full target action into the embedded original face factors
and their actual exterior complement, with all shared link variables retained.
Writing `I` for the interior-weighted Haar moment and `W` for the exterior
factor, [`boundaryNumerator_covariance`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L68)
proves the exact same-cutoff identity
`D(p) = I(p W) I(1) - I(p) I(W)`.

This determinant has a constructed cutoff-limit CReal and explicit
[`boundaryCutoff`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L114).
[`normalized_boundary_response`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L150)
then proves `E_full(p) I(1) - I(p) = D(p)/Z_full` after cutoff removal,
using the SAME original full partition reciprocal. No reciprocal of `I(1)`
or independence of overlapping plaquettes is assumed.

**Scope at that checkpoint:** this exposed the boundary response but did not
bound its size as the boundary recedes. The smaller-carrier identification
is now proved in the latest result above. Quantitative response control remains, before
padding convergence, time homogeneity, physical transfer and a spectral gap.
The continuum/Clay target remains open. Four new modules: 79 focused axiom
gates within `{propext, Quot.sound}`, final error/warning free. No new holes,
analytic assumptions, numerical constants, oracle or raised limits; no full
build/audit/guard/progress run.

**Preceding result: literal time-separated ORIGINAL correlations, with separate stage padding and time lags.**
[`faceId_pin`](lean/YMGap/Continuum/BF4ExactSlabTimeEmbeddingGeometry.lean#L79)
constructs the actual translated physical face ID. Its map is injective and
composes correctly. Reflection changes a shift `s` under enlargement `n`
into the upper shift `2*n-s`. The observable maps preserve sums, products,
scalars, and literal all-spin plaquette evaluation.

[`displaced`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeEmbedding.lean#L132)
keeps the stage padding `n` independent of the lag. Lower and reflected upper
coordinates shift by `n-lag` and `n+lag`. The exact
[`reflected_time_separation`](lean/YMGap/Continuum/BF4ExactSlabTimeEmbeddingGeometry.lean#L179)
therefore grows by the sum of the two outward lags.

[`correlation_formula`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeCorrelations.lean#L80)
uses these original translated polynomials in three expectations under ONE
original slab action and partition function, after representation-cutoff
removal. Its `correlationCauchy` returns explicit Cauchy data.
[`correlation_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeCorrelations.lean#L94)
identifies it with the two actual centered states in THAT stage's existing
completion. Symmetry, nonnegative diagonal and sharp Cauchy--Schwarz hold
for every rational `0<w<1`. At zero padding/lags, `probe_zero_floor` recovers
the strictly positive original seed below.

**Scope:** no decay estimate, transfer-power identity, inter-stage isometry,
or stationary-vacuum claim. Geometry has sum-of-lags separation; the finite
correlations are NOT proved to depend only on that sum. Spatial coordinates
are unchanged, so this alone is not a bulk-centered 4D exhaustion.
**At that checkpoint:** spatial bulk placement and an exact boundary
comparison were next; the new result above constructs them. Quantitative
boundary control, padding limits and time homogeneity needed for bounded
physical transfer descent remain open. Three modules: 53 focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; no new holes, numerical
constants, oracle, raised proof limits or full-tree build/audit.

**Preceding result: a nonzero centered state in the ORIGINAL completed plaquette space.**
At the certified nome `w=1/1024` on the extent-one slab,
[`determinant_negative`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeMinor.lean#L88)
proves `D<=-1/1024` at every representation cutoff. The actual channel
weight is positive for `K>=1`.
[`rawFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeUniformFloor.lean#L85)
gives one strictly positive rational raw reflected-norm floor for every
`K>=1` and every rational centering coefficient.

That floor survives cutoff removal, normalization by the SAME original
partition function, and the actual Cauchy representative of orthogonal
centering. The constructed
[`state`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L112)
belongs to the existing original unit complement;
[`state_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L123)
proves it is nonzero. Its normalized positive floor is computed from the raw
floor and original reciprocal bound, and
[`normCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L103)
retains the explicit norm modulus.
[`connectedCovariance_floor`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L134)
pins this result to the ORIGINAL connected reflected covariance.

**Scope:** one fixed positive nome and finite slab, after representation-cutoff
removal and completion. This is not a stationary-vacuum identification,
physical transfer, spectral gap, or volume/spacing-uniform estimate.
**At that checkpoint:** geometric time translation on original observables
was next. The maps and finite-stage correlations are now constructed above;
slab comparison and a bound allowing physical transfer descent remain open.
The full physical OS root and continuum/Clay target remain open.
Four new Lean modules: 49 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free; exact-rational pilot passed. No new proof holes,
native oracle, raised limits or full-tree build/audit.

**Preceding result: ORIGINAL interacting moment identity and small-nome error bound.**
[`scalarPlaquetteMinor_eq`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteHeatDressedMinor.lean#L91)
identifies the actual two-channel minor with `(2*w^3)^4 * D^2`, where
`D = H(p L)*H(r L)-H(p r L)*H(L)`. Here H is the same 116-link Haar
functional, p the original plaquette, r its scalar-coordinate loop, and L
the ORIGINAL lower heat product. No tree-path recoding remains in D.

Under the explicit per-face guard `(2*w^3)*R(face) <= 1/2`, where
`R(f)=2*coefficientL1(f)+1`,
[`faceTail_coefficientL1`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeFaceRemainder.lean#L76)
bounds all positive-label terms by twice the first character majorant.
A shared-variable telescope computes `E=product_i(1+delta_i)-1` from these
face bounds, without treating plaquettes as independent.
[`lowerMoment_eq`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHeatPerturbation.lean#L145)
and [`lowerMomentError_bound`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHeatPerturbation.lean#L149)
give `H(p L)=H(p)+error` and `abs(error)<=coefficientL1(p)*E` at every
representation cutoff. E depends explicitly on w and the face list.

**At that checkpoint:** the remaining task was to certify a positive nome
satisfying the finite guards, separate D from zero, and retain a positive
normalized floor through cutoff removal. The latest result above now
supplies these at w=1/1024, extent one. This estimate is not beta-, volume- or
spacing-uniform mass control. Three new modules: 40 focused axiom gates
within `{propext, Quot.sound}`, final error/warning free. No new proof holes
or full-tree build/audit; the Clay goal remains open.

**Preceding result: concrete ORIGINAL plaquette channels and exact reference Haar moments.**
[`interfaceChoice`](lean/YMGap/Continuum/BF4ExactSlabFundamentalRetainedChannels.lean#L150)
constructs the actual interface leaf for any selection of quaternion
coordinates, with coefficient-level polynomial and exact heat-weight pins.
[`loopChannel`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCoordinateChannels.lean#L108)
specializes this to the four boundary links of the original fundamental
plaquette `probe`: crossing faces `[2,4,20,40]` correspond to `A,D,C,B`.
Each resulting coordinate-product channel has weight `(2*w^3)^4`, positive
for w>0 and unchanged as the character cutoff increases past one.

The unit leaf and scalar-coordinate loop now give a fully specified
[`scalarPlaquetteFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteConcreteMinor.lean#L124)
for the ORIGINAL raw reflected norm of `probe-c*unit`, for every rational c.
The two-probe bound allows overlap and pays a factor two; the sharper
distinct-path bound below remains available. No channel witness is assumed.

Bare product-Haar integration on the same 116-link carrier gives both
means zero and
[`probe_scalarChannel_haar`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteProbeHaarMoments.lean#L38)
equal to `1/128`. The resulting reference determinant is proved exactly
`-1/128`, with square `1/16384`.

**At that checkpoint:** the determinant still needed control after inserting
the ORIGINAL lower heat product, followed by a positive normalized floor
through cutoff removal. Both are now supplied above at w=1/1024, extent one.
The reference Haar computation omits that insertion; it is not the
interacting covariance. Positive channel weights alone do not establish a
positive minor. This reference computation alone did not prove a nonzero
completed centered state or mass gap.
Five new modules: 68 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free, no new proof holes or full-tree build/audit.

**Preceding result: a centering-independent lower bound from ORIGINAL interface channels.**
Two distinct paths in the actual reflected-square expansion retain two
weighted Haar squares without double-counting. For their observable
amplitudes `a0,a1`, unit amplitudes `b0,b1`, and weights `w0,w1`, set
`D = a0*b1-a1*b0` and `B = w0*b0*b0+w1*b1*b1`.
[`retainedFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRetainedMinor.lean#L134)
proves, for **every rational centering coefficient** `c`,

```text
w0*w1*D*D / (B+1) <= ORIGINAL raw reflected norm squared of (e-c*unit).
```

The weighted Lagrange identity proves the bound; subtracting `c*unit`
leaves `D` unchanged. The denominator is proved positive without assuming
any amplitude is nonzero. All four amplitudes retain the original lower
heat product, shared links, and finite cutoff. No surrogate action occurs.

The floor is computable but **may be zero**. A positive minor for a concrete
original observable/channel pair, and a positive floor surviving cutoff
removal and normalization, remain open. This does not yet construct a
nonzero completed centered state, transfer operator, or spectral gap.
Two new modules: 38 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free; no new proof holes or full-tree build/audit.

**Preceding result: actual orthogonal centering and literal ORIGINAL connected covariance.**
[`unitProjection`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUnitProjection.lean#L78)
constructs `P(x)=<x,u>u` from the actual pairing coefficient and its
computed modulus. It is self-adjoint, idempotent and contractive.
[`center`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean#L81)
is `x-P(x)`, exactly orthogonal to the original norm-one unit. Its
projection/linearity laws and
[`orthogonal_decomposition_inner`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean#L161)
give Pythagoras and nonexpansiveness with no extra factor.

[`approximateCentered`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredDensity.lean#L59)
returns an original expression whose exactly centered completed state
approximates a supplied centered Cauchy representative at its original
rate. Centering commutes with represented-row limits, and
[`complementRowLimit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredDensity.lean#L94)
retains their explicit convergence rate. No arbitrary quotient
representative is selected.

[`connectedCovariance_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteConnectedCovariance.lean#L86)
proves the literal identity
`<C(p),C(q)> = E(theta(p)q)-E(p)E(q)` with the SAME original action and
partition function. Its real representative has a computed Cauchy
modulus, symmetry, nonnegative diagonal and sharp Cauchy--Schwarz.

This is a finite-slab unit complement, **not yet a stationary physical
vacuum complement**. Next: a concrete centered observable with a strictly
positive original reflected norm. Nontriviality, physical transfer,
compatible slabs, full quotient completeness, strict gap and
continuum/Clay remain open. No temporal decay is asserted here.

Four new modules: 72 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: real-scalar action on the ORIGINAL completed plaquette space, with explicit moduli.**
[`realScalarCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarCauchy.lean#L160)
constructs the actual expression stream `s.approx n * X.seq n`. Its
modulus uses computed scalar/vector tail ceilings and explicit error
budgets, not a modulus extracted from an erased existence proof.
[`completedRealSmul`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedRealScalar.lean#L84)
descends to the SAME completion.
[`completedRealSmul_congr`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedRealScalar.lean#L105)
proves independence of the scalar representative and supplied modulus;
both-slot homogeneity and the rational-action pin are proved.

[`scalarMulCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarAlgebra.lean#L51)
computes product moduli from the two supplied scalar moduli. Addition
and negation also retain moduli. The action respects scalar addition,
composition and vector addition; its
[`completedDist_realSmul`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarAlgebra.lean#L123)
is exact squared-distance scaling by the scalar twice.

Scope: `CReal` scalars **with supplied `QCauchy` data** for their actual
streams. This does not select such data for arbitrary legacy quotient
reals, prove full quotient-level Hilbert completeness, or prove a gap.
Canonical centering against the original norm-one unit using its actual
pairing coefficient is now supplied above. Physical vacuum stationarity, transfer,
strict mass gap and continuum/Clay remain open.

Three new modules: 37 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: sharp completed Cauchy--Schwarz and explicit limits of represented Cauchy families.**
[`completedInner_cauchySchwarz`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedGeometry.lean#L47)
passes the original sharp inequality through the actual pairing limits.
The reused product-continuity theorem has only constructive-real inputs;
no older gauge carrier or physical transfer is imported into the statement.
The completed squared distance is symmetric, nonnegative, obeys the
sqrt-free triangle bound, and is zero exactly when its states are equal.

[`constantApproximation_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedApproximation.lean#L65)
shows how to approximate a state from its supplied Cauchy representative.
[`rowLimit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L98)
constructs a limit for a Cauchy family supplied with such representatives
and an outer modulus `M`. The diagonal has rate
`max(M(epsilon/16), (epsilon/16).den)`; convergence to the completed limit
has rate `M(epsilon/16)`. Its value is unique and
[`rowLimit_independent`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L146)
proves independence from row representatives and their moduli.
[`rowLimit_expressionRows`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L168)
also proves that limiting the dense expressions of any supplied original
Cauchy representative recovers its same completion class.

This **does not select representatives of an arbitrary quotient-valued
Cauchy sequence**. Modulus-bearing real-scalar extension is supplied above;
the stronger completeness claim remains open. The `epsilon/16` split is an error budget, not a physical
decay rate. The physical observable/transfer/vacuum, strict mass-gap,
volume/spacing/QFT and all-group Clay obligations remain open.

Three new modules: 45 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: the ORIGINAL completed pairing is rationally bilinear and positive definite on every completion state.**
[`addition`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletionLinear.lean#L93)
and [`scalarContinuous`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletionLinear.lean#L97)
construct completed operations from their proved distance estimates.
Scaling by `c` uses the explicit tolerance `epsilon/(c*c+1)`, including
negative and zero scalars. The additive-group and rational scalar laws
descend from original plaquette coefficient identities.

[`completedInner_add_left`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedBilinear.lean#L43)
and [`completedInner_smul_left`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedBilinear.lean#L55)
pass the original form laws through the constructed limits; both right-slot
laws follow by symmetry. The quotient embedding preserves these operations.
[`completedInner_posdef`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedPosdef.lean#L84)
proves zero completed squared norm **if and only if** the completed state
is zero. Its forward direction returns an explicit closeness witness
[`closeZeroOfInnerZero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedPosdef.lean#L70),
using the existing pairing rate, not a chosen modulus.

Three new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Completed CS and limits of represented Cauchy rows are now supplied above.
Modulus-bearing real-scalar extension is now supplied above.
**Still open at the Hilbert boundary:** full quotient-level constructive
completeness. Observable action,
all required gauge observables, compatible slabs, physical transfer,
stationary vacuum, strict physical gap, continuum QFT and all-group Clay
remain open. No new analytic premise or substitute carrier is used.

**Preceding result: the ORIGINAL mixed pairing descends to its actual completion.**
[`pairing_close`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingContinuity.lean#L101)
controls changes in both arguments with the explicit squared-distance
tolerance `epsilon^2 / (8*(B+1))`. The required eventual diagonal bound
is computed from a Cauchy anchor and the original action bounds, not assumed.
[`representativeInner`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingLimit.lean#L137)
constructs the pairing limit with explicit outer and inner moduli;
[`representativeInnerCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingLimit.lean#L147)
retains its approximation modulus as data.

[`completedInner`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedInner.lean#L83)
is independent of both representatives. It is symmetric, nonnegative on
the diagonal, has unit diagonal one, and
[`completedInner_embedQuotient`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedInner.lean#L105)
recovers exactly the original null-quotient form. All bounds retain their
coupling, slab and representative dependence; none is a strict gap bound.

That increment passed 45 focused axiom gates within `{propext, Quot.sound}`,
with no new holes or full-tree audit. Its completed rational linear laws,
bilinearity and positive-definiteness frontier is now discharged above.
The remaining Hilbert and physical obligations are explicitly open;
the older boundary-code completion is not substituted for this carrier.

**Preceding result: the ORIGINAL plaquette null quotient embeds faithfully into an explicit-modulus completion carrier.**
[`null_iff_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteNullQuotient.lean#L119)
characterizes zero reflected distance as equality of all mixed pairings.
The actual normalized form therefore descends to the null quotient, where
[`inner_posdef`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteNullQuotient.lean#L209)
proves positive definiteness. Addition and rational scaling descend, and
the unit has squared norm one.

[`distSq_reflected`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L77)
pins the squared distance to `E(theta(p-q)*(p-q))`.
Positivity of a difference gives its square-root-free triangle bound;
the radical theorem supplies null congruence. This constructs the existing
explicit-modulus Cauchy
[`Completion`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L144).
[`embedQuotient_injective`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L173)
proves that completion loses no additional quotient states, and
[`completedUnit_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L184)
proves the embedded unit is nonzero. These statements hold for every
rational `0<w<1` and odd slab, on the same plaquette-generated subalgebra.

That increment passed 53 focused axiom gates within
`{propext, Quot.sound}`, with no new proof holes or full-tree audit.
Its pairing-limit and representative-independence frontier is now
discharged by the latest result above; the remaining Hilbert/physical
obligations are unchanged.

**Preceding result: the ORIGINAL normalized plaquette reflected form has sharp Cauchy--Schwarz and norm-null descent.**
[`form_reflected`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L53)
identifies the form with the literal `E(theta(p)*q)`, for every rational
`0<w<1` and odd slab. It is symmetric, rationally bilinear, nonnegative
on the diagonal and normalized at the unit.
[`form_cauchySchwarz`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L185)
proves `B(p,q)^2 <= B(p,p)*B(q,q)`, and
[`form_radical_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L213)
proves that norm-null expressions pair to zero.
[`formCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L106)
retains the explicit original expectation modulus.

The proof uses
[`expectation_reflection_invariant`](lean/YMGap/Continuum/BF4ExactSlabPolynomialReflectionInvariance.lean#L135)
for the actual full action with any supported polynomial, and
[`finiteGNSData`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteFiniteGNS.lean#L84)
for actual finite-cutoff plaquette expressions. Finite Cauchy--Schwarz
passes through the original numerator limits; normalization divides every
pairing by the SAME positive partition function. No auxiliary-law identity
or additional analytic premise is used.

Three new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Bounds and moduli depend on the nome, slab and expressions. This is still
the **plaquette-generated subalgebra**, not all gauge observables. Its
null quotient and completion carrier are now supplied above; the completed
inner product, Hilbert-space laws and observable action, compatible slabs,
transfer, stationary vacuum, uniform physical gap and continuum Clay
target remain open. The older boundary-code completion is not silently
identified with this form.

**Preceding result: reflected positivity for the ORIGINAL normalized plaquette functional.**
[`expectation_reflection_nonnegative`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L196)
proves `E(theta(p)*p)>=0` for every finite sum, product and rational multiple
of lower-half plaquette characters, at every rational `0<w<1` and odd slab.
The reflection is the literal oriented link reflection.
[`reflected_numerator_eq_squareValue`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L178)
pins the ORIGINAL full-action numerator to an explicit finite square
expansion at each cutoff. The original numerator limit and SAME positive
partition function then give the normalized inequality.
[`expectation_reflection_eq_upper`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L201)
also pins every mixed reflected pair, and
[`expectation_reflected_unit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L212)
proves the distinguished unit has reflected value one.

Two new modules: 44 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
This is the **plaquette-generated subalgebra**: completeness among all gauge
observables is not proved. The mixed-form laws are supplied by the newer
result above. Physical completion, observable action, compatible slabs,
transfer and stationary vacuum remain to be connected; the strict uniform
physical gap and continuum Clay target remain open.

**Preceding result: positive normalized polynomial expectations for the ORIGINAL slab action.**
[`BF4ExactSlabPolynomialExpectation.expectation`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L46)
constructs `E(p)=N(p)/Z` for every rational `0<w<1` and odd slab, on the
original shared link coordinates. The signed numerator has a computed
cutoff modulus; normalization uses the same original action limit `Z`.
[`expectation_one`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L48)
proves `E(1)=1`, and
[`expectation_square_nonnegative`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L82)
proves positivity on every supported ordinary polynomial square. Linearity,
quaternion-Haar carrier invariance and exact recovery `E(p)*Z=N(p)` are proved.
[`expectationCauchy`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L133)
provides a modulus for the actual normalized real approximants, with an
explicit bound depending on the nome, finite slab and polynomial.

Three new modules: 49 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Ordinary-square positivity is **not** reflection positivity. The new result
above supplies the latter on the concrete plaquette-generated subalgebra;
its physical completion/observable action, transfer, stationary vacuum,
strict physical gap, volume/spacing passage and continuum QFT remain open.

**Preceding result: the original completed slab pairing is normalized, with its FULL heat unit of norm one.**
[`BF4ExactSlabNormalizedCompletedPairing.completedHeatUnit_norm_one`](lean/YMGap/Continuum/BF4ExactSlabNormalizedCompletedPairing.lean#L86)
proves this on the unchanged completed carrier, for every rational `0<w<1`
and every odd slab. The normalized form is exactly `B(x,y)/Z`, where `Z`
is the ORIGINAL interacting action limit. No square root, substitute vector,
or auxiliary positive law is used.

[`action_mul_reciprocal`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionReciprocal.lean#L125)
constructs and cancels the reciprocal of that same `Z`. Its rational samples,
positive lower/upper bounds and modulus are explicit. The completed pairing
retains positivity, symmetry, additivity, Cauchy–Schwarz and exactly the same
zero pairings; multiplying by `Z` recovers the original form.
[`normalizedDense_approximation`](lean/YMGap/Continuum/BF4ExactSlabNormalizedCompletedPairing.lean#L166)
supplies a computed rescaling of the original dense-approximation modulus.

Three new modules: 50 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
The normalization constants depend on the nome and finite slab.

**Next: physical observable realization, compatible slabs and geometric transfer.**
Norm one does not establish a stationary physical vacuum. These physical
identifications, the strict gap on its complement, volume/spacing control,
continuum QFT and the all-group Clay target remain open. The existing raw
completion is unchanged; this milestone proves the normalized pairing and
its quantitative comparison, not a new physical reconstruction package.

**Preceding result: the ORIGINAL action limit is strictly positive, and its completed full heat unit is non-null.**
[`BF4ExactSlabOriginalActionStrictFloor.fullActionLimit_ge_floor`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionStrictFloor.lean#L61)
proves `Z(w,slab) >= c(w)^F > 0` for every rational `0<w<1` and every odd
slab, on the existing interacting Haar action limit. The bound and all
approximation cutoffs are explicit. `fullActionFloorCertificate` constructs
the existing finite certificate without a positive-floor premise; its
finite margin is `c(w)^F/4`.

[`completedHeatUnit_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionStrictFloor.lean#L94)
then proves the ACTUAL completed full heat unit is not the zero vector,
using the previously proved norm/action identity on the same slab carrier.
This is not the earlier norm-one boundary CODE or the auxiliary positive law.

The last limit step is now proved: a computed finite label band controls
the `(1-W)` coefficient deficit, the original character tail pays the
remaining error, and a shared-link product telescope gives an explicit
Haar comparison. No pointwise-to-Haar principle or link independence is used.
Four new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Boundary of the action-floor milestone.** Normalization of the completed
pairing is now proved above; physical vacuum stationarity is not. Compatible slabs,
physical observable realization, geometric time transfer, a strict bound on
its vacuum complement, volume/spacing control, continuum QFT and the
all-group Clay target remain open. The floor depends on `w` and the finite
face count `F`; it is not a uniform spectral-gap estimate.

The dated milestones below preserve their historical verification scope.
Their former action-floor/non-nullness and scalar-normalization residues are superseded above;
the remaining physical and continuum obligations are not.

**Preceding result: the Jacobi approximants are the weighted ORIGINAL heat polynomials.**
[`BF4ExactSlabJacobiWeightedHeatPin.face_coeffEqv`](lean/YMGap/Continuum/BF4ExactSlabJacobiWeightedHeatPin.lean)
proves coefficient equality with the existing original `faceHeatTerm`s,
carrying the actual finite weights `W(w*w,N,r+1)`. `product_haar_insertion`
preserves every shared-link product with ANY insertion polynomial present.
`productFloor_le_weightedHaar` therefore gives `c(w)^F` below the integral
of those weighted original terms, at `0<w<1` and `N>=1`.

The proof uses constructive finite-grid polynomial uniqueness followed by
coefficient-preserving substitution. It does not assume that agreement of
scalar evaluations implies equality of Haar integrals. The original label
shift, heat coefficients, and inverse-nome/half normalization are retained.

**Boundary of the coefficient-identification milestone.** The finite weights
are not one. The required finite-band/tail/product comparison and original
action-limit floor are now proved above. Physical vacuum/transfer/gap and
continuum/Clay remain open. Three new modules in this preceding milestone:
31 focused gates within `{propext, Quot.sound}`, no new holes, final
error/warning free. No full-tree build or audit was run.

**Preceding result: a strict shared-link Haar floor for finite Jacobi approximants.**
[`BF4ExactSlabJacobiHaarFloor.productFloor_le_haar`](lean/YMGap/Continuum/BF4ExactSlabJacobiHaarFloor.lean)
proves that the ORIGINAL normalized quaternion Haar integral of the
finite Jacobi face-product is at least `c(w)^F > 0`, at every rational
`0<w<1`, every finite slab and every truncation `N>=1`. All overlapping
link variables and actual ordered plaquette words are retained. The floor
depends on the nome `w` and face count `F`; it is NOT coupling- or
volume-uniform, nor a spectral-gap bound.

The algebraic core is short: the actual unit holonomy gives the four-square
identity `2(1+a)=(1+a)^2+b^2+c^2+d^2` under every Haar insertion. The finite
Jacobi factors and their derivative have nonnegative coefficients in `1+a`.
The square-certificate compiler preserves products with shared variables;
retaining each constant coefficient supplies the integrated floor. No
general pointwise-to-Haar order principle or independence is assumed.

**Boundary of the preceding finite Haar result.** They are not the original
unweighted heat cutoffs. The coefficient-level pin to weighted character
polynomials and quantified Haar-limit passage are now proved above, as are
the original action-limit floor and non-null full unit. Compatible physical
slabs, stationary vacuum/transfer, strict physical gap and continuum/QFT/
all-group target remain open. Five new modules in this preceding milestone:
51 focused axiom gates within `{propext, Quot.sound}`, no new holes, final
error/warning free. No full-tree build or audit was run.

**Preceding result: an explicit strictly positive original heat floor.**
[`SU2PointwiseHeatStrictFloor.pointwiseHeatCReal_geRat_floor`](lean/YMGap/Continuum/SU2PointwiseHeatStrictFloor.lean)
proves `K_q(x) >= c(q) > 0`, for every rational `0<q<1` and `x` in
`[-1,1]`, endpoints included. With a computed prefix length `L(q)`,
`c(q) = (product_{j=1..L(q)} (1-q^j))^2 / 16`.
The proof uses a finite positive Euler prefix, a geometric tail budget,
and the proved differentiated Jacobi identity. No positive limit is assumed.

`finiteCutoff q` additionally gives an explicit label count beyond which
every ORIGINAL character prefix is at least `b(q)=c(q)/2`.
[`BF4ExactSlabHeatPointwiseFloor.eval_faceHeatPolynomial_eqv`](lean/YMGap/Continuum/BF4ExactSlabHeatPointwiseFloor.lean)
pins those prefixes to the original shared-link face polynomials, including
their exact `K+1` convention. Its product theorem gives `b(q)^F` for `F`
faces at a common rational environment, with each scalar box hypothesis
explicit. Neither the heat floor nor the product floor is coupling- or
volume-uniform. Four new modules: 30 focused axiom gates within
`{propext, Quot.sound}`, no new holes, final error/warning free.

**Boundary of the preceding pointwise result.** Pointwise
positivity is not silently promoted to a Haar-integral lower bound: the
existing algebraic Haar positivity theorem applies to polynomial squares.
The new square-certified Jacobi approximation above supplies a finite
integrated bound; its original-action limit identification is still open.
The original interacting-action floor and non-null full unit remain open,
as do physical slab compatibility, stationary vacuum/transfer, strict
physical gap, continuum/QFT and the all-group Clay target. No full-tree
build or audit was run; the refuted auxiliary-law identity remains unused.

**Preceding analytic result: differentiated JTP and original SU(2) heat nonnegativity.**
[`JacobiDifferentiatedIdentityOnBox.diffJTP`](lean/YMGap/Continuum/JacobiDifferentiatedIdentityOnBox.lean)
proves the existing, unchanged obligation `dSeriesCReal = (1/2)*Theta*S`
for every rational `0<q<1` and `-1<=x<=1`, including both endpoints.
Its `pointwiseHeatCReal_geRat_zero` then proves nonnegativity of the
ORIGINAL completed SU(2) heat series through the existing nome/offset bridge.
No same-function hypothesis, off-box totalizer, or limit-interchange premise
is supplied.

The proof identifies the actual finite product derivative with twice the
weighted heat partials, then bounds the entire derivative error by
`C_d(q) q^(2N+1)`, with a computed cutoff. All q-dependence is explicit;
uniformity is only over x in the stated interval. Four new proof modules:
36 focused axiom gates within `{propext, Quot.sound}`, no new holes.

**Remaining: a strictly positive original-action floor.** Nonnegativity alone
does not establish a non-null full unit, stationary physical vacuum, strict
spectral gap, controlled continuum limit, or the Clay theorem. Those remain
open; the refuted auxiliary-law identity above is not used.

**Preceding analytic result: the original theta product equals its series on `[-1,1]`.**
[`JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries`](lean/YMGap/Continuum/JacobiTripleProductOnBox.lean)
proves the undifferentiated Jacobi triple product for every rational `0<q<1`
and rational `-1<=x<=1`, using the EXISTING product and series `CReal`s.
The normalization is explicit: full theta is `1 + 2 * chebTConvPt`, not
the nonconstant half-series alone. No same-limit premise is assumed.

The key estimate in
[`FiniteJacobiSeriesComparison.Ppart_sub_bareTheta_le`](lean/YMGap/Continuum/FiniteJacobiSeriesComparison.lean)
bounds the whole finite-polynomial error by `C(q) q^(2N+1)`, with
`C(q) = (2/(1-q*q)) (1+2/(1-q))` and a computed tolerance-to-cutoff map.
Gaussian absorption of the coefficient deficit avoids a separate finite-band
split. The estimate is uniform in `x` on the stated interval, NOT in `q`.
Two focused checks passed: 22 gates inside `{propext, Quot.sound}`, no new
holes. Differentiated JTP and heat nonnegativity are now proved above.
Strict original-action positivity, physical vacuum/transfer/gap, and
continuum/Clay remain open; no full-tree audit was run.

**Preceding analytic result: explicit convergence of the finite Jacobi weights.**
[`FiniteJacobiWeightBounds.centeredWeight_eq_segments`](lean/YMGap/Continuum/FiniteJacobiWeightBounds.lean)
rewrites the ORIGINAL normalized coefficient as two finite Euler products.
The coefficients lie in `[0,1]`, and for `j<=N` their deficit from one is at
most `2 Q^(N-j+1)/(1-Q)`, where `0<Q<1`.
[`FiniteJacobiWeightConvergence.centeredWeight_abs_close`](lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean)
provides a computed cutoff uniform over each specified finite band `j<=J`.
The base and band are explicit; no infinite-product denominator is assumed.
Three focused checks passed: 25 gates inside `{propext, Quot.sound}`, no new
holes. The whole-polynomial comparison and both on-box identities are now
proved above. These coefficient estimates are not a coupling-uniform physical
gap or an original-action positive floor.

**Preceding analytic result: the finite symmetric Jacobi identity is proved.**
[`FiniteJacobiIdentity.Ppart_eq_finiteJacobi`](lean/YMGap/Continuum/FiniteJacobiIdentity.lean)
identifies the ORIGINAL full theta product with its Euler-normalized finite
Gaussian/Chebyshev series, for every finite cutoff, rational `0<q<1`, and
rational `x`. The proof combines two q-Pascal orientations with the Chebyshev
recurrence, including the center's factor of two and both finite endpoints.
It uses the actual q-binomial weights, not bare theta coefficients.
Four focused checks passed: 31 gates inside `{propext, Quot.sound}`, no new
holes. Coefficient convergence, whole-polynomial comparison and the
undifferentiated and differentiated on-box identities are now proved above.
They supply heat nonnegativity, but not the positive original-action floor below.

**Latest original-action result: a retained channel bounds the full interacting action.**
[`BF4ExactSlabAllExtentRetainedVacuumChannel.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentRetainedVacuumChannel.lean)
proves `Z_K >= lowerActionValue_K^2` at every finite cutoff, odd slab and
`w >= 0`. An explicit path retains the actual trivial-representation interface
channel, whose weight is one; other nonnegative square channels are discarded.
The lower-half Haar integral keeps its full spatial interactions and shared links.

[`BF4ExactSlabAllExtentLowerActionFloor.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentLowerActionFloor.lean)
uses the lower-product tail modulus: if one tail-certified anchor has absolute
integral at least `b + epsilon`, with `b > 0`, then the full original action
limit is at least `b^2`. Either sign of that lower amplitude is allowed.
This constructs the existing full-action certificate and proves the actual
completed full unit nonzero, given those finite lower-half data.

**The required family of lower-half margins remains open.** No universal
positivity, normalization, stationary physical vacuum, strict gap or
continuum/Clay result is claimed. Three focused monitored checks passed:
35 axiom gates within `{propext, Quot.sound}`, no new sorry. No large
certificate computation or full-tree build/audit/guard was run.

**Preceding result: a finite exact criterion certifies non-nullness of the ORIGINAL full unit.**
[`BF4ExactSlabAllExtentActionFloorCertificate.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentActionFloorCertificate.lean)
supplies a proof-producing finite check: `epsilon > 0`, `b > 0`, a cutoff
beyond the original tail modulus, and `b + epsilon <= Z_K` for the ORIGINAL
interacting Haar integral. Accepted data give a positive floor for the same
action limit, with an explicit eventual approximation index. Conversely, a
supplied positive limit floor produces finite data with a computed cutoff and
quarter-floor budget; the criterion adds no analytic assumption.
[`BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.lean)
uses the norm/action identity to prove that a successful certificate makes
the ACTUAL completed full unit nonzero.

**Successful certificates for the full coupling/slab family are not yet
constructed.** A failed check does not prove zero. This closes the finite-floor
to non-nullness implication, not unconditional positivity, normalization or
physical vacuum identification. Next is a lower estimate for the original
finite integral at a tail-certified cutoff. Physical slab compatibility,
time/transfer, strict gap and continuum/Clay remain open. Two focused monitored
checks passed: 17 axiom gates within `{propext, Quot.sound}`, no new sorry.
No large certificate computation or full-tree build/audit/guard was run.

**Preceding result: the completed full unit's squared norm is the ORIGINAL action integral.**
[`BF4ExactSlabAllExtentActionLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentActionLimit.lean)
constructs the full interacting action-integral limit with an explicit Cauchy
modulus, for every rational `0<w<1` and odd slab. Its nonnegativity follows
from the original reflection-positive quadratic, not a decoupled model.
[`BF4ExactSlabAllExtentHeatUnitActionComparison.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitActionComparison.lean)
bounds the discrepancy between the code norm's computed interface cutoff
and the equal-cutoff action integral. The original boundary product bounds
rescale an explicit interface-remainder modulus.
[`BF4ExactSlabAllExtentHeatUnitNormAction.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitNormAction.lean)
then proves `completedHeatUnit_norm_action` by constructive limit uniqueness.

The normalization question is now pinned to this SAME action integral.
A strictly positive lower bound is still open; nonnegativity alone does not
give non-nullness. Physical unit/vacuum identification, compatible slabs,
time/transfer, strict gap and continuum/Clay remain open. All moduli retain
`w` and slab dependence. Three focused monitored checks passed: 29 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: the growing full heat unit is GNS-Cauchy in the ORIGINAL slab space.**
[`BF4ExactSlabAllExtentHeatUnitCauchy.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitCauchy.lean)
constructs the actual all-label sequence, its explicit squared-distance
modulus, and its class in each original slab completion, for rational
`0<w<1`. The convergence bound retains explicit thresholds for both the
boundary cutoff and the supplied limit representative's index.

The proof combines cutoff-independent original face bounds with the
shared-variable telescoping polynomial in
[`PolynomialProductRemainder.lean`](lean/YMGap/Continuum/PolynomialProductRemainder.lean).
[`BF4ExactSlabAllExtentHeatProductTail.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatProductTail.lean)
computes the full-product remainder modulus.
[`BF4ExactSlabAllExtentHeatUnitIncrement.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitIncrement.lean)
pins the actual code difference's original GNS norm to the two boundary
remainders and the original interface. If its coefficient bound is `B`,
make the upper remainder at most `1` and the lower at most `epsilon/(B+1)`.
This directly controls the squared norm, without a square root or assumed
independence of plaquettes.

This constructs a **full-unit completion class**, not a stationary physical
vacuum. Its non-nullness/normalization, physical interpretation and
compatibility between slabs still require proofs. Physical time/transfer,
strict gap, volume/spacing/QFT and all-group Clay remain open; the modulus
depends on `w` and the slab. Five focused monitored checks passed: 50 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: the full heat-unit pairing and explicit original plaquette tails.**
[`BF4ExactSlabAllExtentHeatUnit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnit.lean)
resums the all-label boundary coefficients into the ORIGINAL heat products.
Its completed pairing retains three separate cutoffs: left boundary, interface
and right boundary. At equal finite cutoffs, the quadratic is exactly the
full original slab action integral. This identifies the growing sequence;
fixed-anchor stabilization does not establish its convergence.

[`SU2HeatCharacterPolynomialMajorant.lean`](lean/YMGap/Continuum/SU2HeatCharacterPolynomialMajorant.lean)
bounds the actual character polynomial's coefficient sum by
`(2*L1(p)+1)^s`, retaining the exact dimension/Casimir heat coefficient.
[`SU2HeatCharacterPolynomialTail.lean`](lean/YMGap/Continuum/SU2HeatCharacterPolynomialTail.lean)
supplies a starting label and tolerance modulus for every rational `0<w<1`.
Both depend explicitly on `w` and the polynomial; its eventual factor `1/2`
is a representation-tail estimate, **not a spectral-gap rate**.
[`BF4ExactSlabAllExtentFaceHeatTail.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentFaceHeatTail.lean)
applies this to each original plaquette: a later heat prefix literally equals
the earlier prefix plus a computed remainder with small coefficient norm and
Haar integral. No pointwise-to-Haar limit bridge is assumed.

Subsequent discharge above: full-product remainders, the moving-anchor GNS
Cauchy modulus and completed full unit. Non-nullness, compatible slabs,
physical transfer and stationary vacuum, strict gap, volume/spacing/QFT and
all-group Clay remain open. Four focused monitored checks passed: 49 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: a non-null normalized code and exact centered pairings at every odd extent.**
[`BF4ExactSlabAllExtentVacuumNormalization.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumNormalization.lean)
proves that the constant insertion has exposed degree zero. The full original
interface therefore stabilizes at cutoff zero and has Haar value one. This
gives the trivial-representation boundary code norm one at every odd extent
and cutoff, retaining the original heat weights.

[`BF4ExactSlabAllExtentVacuumCodeGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumCodeGNS.lean)
proves this code is non-null in the completed space. Centering by its own
rational mean stays inside the finite-boundary carrier. The completed centered
pairing equals the original finite bilinear minus the product of its two
original code means, beyond one explicit common cutoff stage.

This is a **code-relative covariance**, not yet a physical-time connected
correlator: the code is not identified with the all-label heat-dressed unit
or a stationary physical vacuum. Slab compatibility, physical unit/vacuum and
time evolution, strict gap, volume/spacing/QFT and all-group Clay remain open.
Two focused monitored checks passed: 27 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. No full-tree audit.

**Preceding result: one original-law cutoff-limit completion at every odd slab extent.**
[`BF4ExactSlabAllExtentAnchoredCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentAnchoredCutoffLimit.lean)
proves exact stabilization of the FULL original signed bilinear on fixed
finite boundary observables. The same zero extension retains both boundary
polynomials, and the computed maximum of the anchor and interface degree
bound supplies the cutoff modulus and rational `CReal` limit.

[`BF4ExactSlabAllExtentBilinearGram.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentBilinearGram.lean)
proves the full mixed channel-product identity and symmetry for w >= 0,
retaining both observables and all original interactions. Combined with
positivity and common finite cutoff stages, this constructs every form law in
[`BF4ExactSlabAllExtentCutoffLimitForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentCutoffLimitForm.lean).
[`BF4ExactSlabAllExtentCutoffLimitGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentCutoffLimitGNS.lean)
then constructs a completion for each slab: all its finite cutoff anchors
embed into the same carrier, with inner products equal to the original
finite/limit pairings. Specified Cauchy representatives and the outer
convergence rate remain data; no quotient representatives are chosen.

Subsequent discharge above: all-extent code normalization/non-nullness and
centered pairing pins. Next: compatibility between these slabs, then physical
time/transfer and a stationary vacuum.
A family of completed slab spaces is not yet one physical positive-time
realization. Its strict gap, volume/spacing limits, QFT axioms and all-group
Clay target remain open. No slab-uniform modulus or beta/spacing-uniform
spectral rate is claimed. Seven focused monitored checks passed: 58 axiom
gates within `{propext, Quot.sound}`, final error/warning free. No new sorry,
analytic premise, raised proof limit or numerical oracle; no full-tree audit.

**Preceding result: exact cutoff removal for the ORIGINAL interface at every odd extent.**
[`BF4ExactSlabAllExtentExposedLinkDegree.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentExposedLinkDegree.lean)
proves structurally that each crossing face has an exposed lower spatial link
absent from every other crossing face. Their full character product has
degree zero in that link, regardless of its other spins.
[`SU2QuaternionFourBlockExposure.lean`](lean/YMGap/Continuum/SU2QuaternionFourBlockExposure.lean)
constructs four explicit coordinate swaps; the original ordered character,
every insertion and the full Haar carrier are retained by
[`BF4ExactSlabAllExtentSelectedFaceSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentSelectedFaceSelection.lean).
No slab-size scan or independent replacement kernel is used.

[`BF4ExactSlabAllExtentInterfaceCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentInterfaceCutoffLimit.lean)
proves `interfacePairing_stable`: with a fixed supported polynomial P, all
original crossing-face heat factors can vary together and the pairing is
EXACTLY unchanged above the computed `interfaceBound half P`.
`interfacePairingLimit` returns the rational `CReal` limit;
`interfacePairingLimit_exact` supplies its exact cutoff modulus.
The statement holds at every finite odd extent and every rational w.
The bound depends on P and the slab, and can inherit parameter dependence
through P. This is not a beta/spacing-uniform spectral estimate.

Subsequent discharge above: larger-slab fixed-boundary recoding and the
common cutoff-limit form/completion. Compatibility and physical positive-time
realization remain open. Physical time/transfer,
stationary vacuum, strict completed gap, volume/spacing/QFT and all-group
Clay remain open. Seven focused monitored checks passed: 57 axiom gates
within `{propext, Quot.sound}`, final error/warning free. No new sorry,
analytic premise, proof-limit increase or numerical oracle; no full-tree audit.

**Preceding result: ORIGINAL signed-law reflection positivity at every odd slab extent.**
[`BF4ExactSlabAllExtentPlaquetteReflection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentPlaquetteReflection.lean)
proves literal time-link conjugation and the oriented plaquette-reflection
identity for every extent and spin. A general four-quaternion cyclic-inverse
scalar identity replaces the old extent-one face scan; no quaternion factors
are commuted and no unit-norm assumption is needed for this identity.
[`BF4ExactSlabAllExtentObservableReflection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableReflection.lean)
then proves `lowerObservable_reflection`: the original upper observable is
the literal reflection of the original lower observable, retaining every
heat weight and signed coefficient on the same padded carrier.

[`BF4ExactSlabAllExtentReflectionPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentReflectionPositivity.lean)
proves the assembled lower observable is lower-local and joins these facts
with the original spatial-Gram Haar identity. `originalQuadraticExpansion`
constructs the actual finite square channels; `exact_quadratic_eq_squareValue`
identifies the ORIGINAL `exactCorrectedSlabReflectedKernel` quadratic with
their weighted sum of rational squares. `exact_quadratic_nonnegative` proves
it nonnegative for every odd extent, every finite K, every w >= 0 and
arbitrary signed boundary coefficients. Shared link variables are retained.
This is reflection positivity, not a strict spectral estimate.

Subsequent progress above supplies the interface cutoff limit, larger-slab
boundary recoding and common cutoff-limit completion. Slab compatibility still
precedes the physical positive-time carrier and geometric transfer; physical vacuum stationarity,
a strict completed gap, volume/spacing limits, QFT and all-group Clay remain open.
Four focused monitored checks passed: 10 + 11 + 4 + 7 = 32 axiom gates
within `{propext, Quot.sound}`, final error/warning free. These include the
locality module's existing gates and its new all-extent character consumer.
No full-tree audit was run; no new sorry, analytic premise or proof-limit increase.

**Preceding result: the COMPLETE original signed bilinear has its spatial-Gram Haar form at every odd extent.**
[`BF4ExactSlabAllExtentWeightedFactorization.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentWeightedFactorization.lean)
keeps the existing signed dual term and factors its complete heat-weighted
network into lower, fixed and upper pieces. Face indexing and partition
associativity are proved structurally, without an extent-specific scan.
[`BF4ExactSlabAllExtentObservableHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableHaarForm.lean)
moves all signed boundary sums under the same Haar integral and resums the
actual central label carrier into the product of face heat polynomials.

[`BF4ExactSlabAllExtentTemporalImages.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalImages.lean)
pins the complete observable's image to the independent temporal assignment.
[`BF4ExactSlabAllExtentTemporalHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalHaarForm.lean)
checks all polynomial support before using Haar invariance.
`exact_bilinear_eq_spatialGramHaar` proves, for every odd extent, finite K,
rational w and signed boundary coefficients,
`B(left,right) = Haar(L_left * H_Gram * U_right)`, where B is the ORIGINAL
`exactCorrectedSlabReflectedKernel` bilinear and both boundary polynomials
are unchanged. No replacement law or positivity premise is used.

The subsequent result above proves `U_right = theta(L_right)` and assembled
lower-half locality at arbitrary extent, closing original-law reflection
positivity for every odd slab. Slab compatibility and physical time remain open.
Four focused monitored checks passed: 16 + 12 + 13 + 11 = 52 gates within
`{propext, Quot.sound}`, no errors or warnings. No full-tree audit was run.

**Preceding result: positive temporal-gauge crossing interfaces on every odd slab.**
[`BF4ExactSlabLocalSquareExpansion.lean`](lean/YMGap/Continuum/BF4ExactSlabLocalSquareExpansion.lean)
stores actual finite reflected-square channels, their polynomial equality,
carrier support, lower-half locality and nonnegative weights. Products keep
shared variables. `haar_eq_squareValue` identifies the original Haar value
with the explicitly computed sum of squared channel integrals.

[`BF4ExactSlabAllExtentSpatialGramPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentSpatialGramPositivity.lean)
constructs these expansions from the actual central crossing-face list,
spatial-link representation columns and heat coefficients at every odd
extent and finite cutoff. `temporalInterface_haar_gram` identifies the
complete temporal-assigned crossing interface with its Gram product under
every insertion. `temporalInterface_eq_squareValue` and
`temporalInterface_nonnegative` apply to any supported lower-half polynomial,
without discarding its spatial interactions. `original_quadratic_pin`
recovers the previously proved ORIGINAL signed quadratic at extent one.

The COMPLETE original-law/observable change-of-variables pin, literal
upper/lower reflection and locality at arbitrary extent are now proved above.
Compatibility, geometric time, stationarity and a gap remain separate.
Two focused monitored checks passed: 12 + 15 = 27 axiom gates within
`{propext, Quot.sound}`, no errors or warnings. No full-tree audit was run.

**Preceding result: ONE completed original cutoff-limit carrier for all finite anchor observables.**
[`BF4ExactSlabFiniteBoundaryObservable.lean`](lean/YMGap/Continuum/BF4ExactSlabFiniteBoundaryObservable.lean)
stores each coefficient function with an explicit finite cutoff witness.
Addition takes the maximum of two witnesses. Every original finite-anchor
coefficient function has a specified image in this common carrier.
[`BF4ExactSlabCutoffLimitForm.lean`](lean/YMGap/Continuum/BF4ExactSlabCutoffLimitForm.lean)
proves the pairing independent of cutoff witnesses and transports
bilinearity, symmetry and positivity from the ORIGINAL finite forms at
explicit common stages. `cutoffLimitGNSData` contains all finite anchors,
with no fixed representation cutoff parameter.

[`BF4ExactSlabCutoffLimitGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabCutoffLimitGNS.lean)
constructs its null-quotient completion. `cutoffLimitEmbed_anchored_pairing`
pins every original finite observable's completed inner product to its
previously proved anchored cutoff limit; `cutoffLimitEmbed_finite_pairing`
pins it to every sufficiently late original finite form. Completeness uses
explicit representative families and moduli, without choosing arbitrary
quotient representatives. The single vacuum-code vector agrees with the
original vacuum delta on every finite carrier, has norm one, and is non-null
in the common completion. Physical stationarity is not asserted.

**Next:** extend cutoff-limit control beyond extent one and prove larger-slab
compatibility, then positive-time realization, a physical transfer and a
strict gap on its own completed vacuum complement. This completion's scope
is the extent-one boundary-coefficient observable family, not the canonical
continuum positive-time root. Finite-cutoff positivity now holds on every
odd slab; volume/spacing limits, QFT axioms and all-group Clay remain open.
Three focused monitored checks passed: 36 axiom gates within
`{propext, Quot.sound}`, no new sorry, analytic premise or proof-limit increase.
No full-tree audit was run.

**Preceding result: the ORIGINAL fixed-observable slab bilinear has an exact cutoff limit.**
[`BF4ExactSlabBoundaryCutoffRecoding.lean`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCutoffRecoding.lean)
keeps both heat-dressed boundary polynomials unchanged at every larger
cutoff, using a finite Boolean label test. Only the original interface varies.
[`BF4ExactSlabSelectedFaceDegreeSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabSelectedFaceDegreeSelection.lean)
proves selected-face annihilation with the other twenty-three characters
retained at arbitrary spins. Their degree in the selected exposed link is
zero, so only the fixed observable determines the selection bound.

[`BF4ExactSlabInterfaceCutoffSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfaceCutoffSelection.lean)
takes the explicit maximum of the twenty-four degree bounds and kills every
above-bound term, retaining all original heat coefficients.
[`BF4ExactSlabAnchoredCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAnchoredCutoffLimit.lean)
then proves `interfacePairing_stable` by exact filtering of the original
enumeration. `exactCutoffPairing_stable` and `exactCutoffPairingLimit_exact`
pin the ORIGINAL signed bilinear to its computed rational CReal limit at
every cutoff beyond `exactCutoffPairingModulus`.
`exactCutoffPairingValue_nonnegative` proves the quadratic limit nonnegative
for w >= 0. Scope: extent one and each fixed finite boundary observable.

The common completed cutoff-limit carrier is now constructed above.
Geometric physical time/transfer and a strict gap on its own vacuum
complement remain open. Finite-cutoff positivity now holds on every odd slab;
volume/spacing limits, QFT axioms and the all-group Clay target remain open.
The four modules have 50 clean axiom gates within `{propext, Quot.sound}`
from focused monitored checks; no new sorry, analytic premise or proof-limit
increase. No full-tree audit was run.

**Preceding result: exact degree selection for a single original heat insertion.**
[`SU2QuaternionHarmonicDegreeSelection.lean`](lean/YMGap/Continuum/SU2QuaternionHarmonicDegreeSelection.lean)
proves that a head-homogeneous harmonic of degree n has zero partial Haar
pairing with every lower-degree polynomial, retaining all tail coefficients.
The proof combines the existing Gaussian integration-by-parts/Euler identity,
induction on the multiplier's degree and the explicit sphere radial factor.
[`SU2QuaternionHeadDegreeDifferential.lean`](lean/YMGap/Continuum/SU2QuaternionHeadDegreeDifferential.lean)
provides computable degree-lowering derivative representatives, proved
coefficientwise equal to the original derivatives.

[`SU2QuaternionExposedHeatCutoffSelection.lean`](lean/YMGap/Continuum/SU2QuaternionExposedHeatCutoffSelection.lean)
applies this to the ACTUAL all-spin four-link character on the original
116-link Haar carrier. `exposedCharacter_haar_zero` kills every spin above
the explicit `headDegreeBound P`. `exposedHeatPairing_stable` proves the
actual heat-packet pairing is exactly unchanged for every larger K, with
P fixed, at every rational w and all sixteen orientations.
`exposedHeatPairingLimit` is its explicitly evaluated rational value in CReal;
`exposedHeatPairingLimit_exact` supplies the stabilization pin.

At that checkpoint, boundary recoding and joint interface stabilization
remained open. They are now proved above. A common completed limit carrier,
physical time/transfer, its strict completed gap and continuum/Clay remain open.
Three focused monitored checks passed: 25 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. No full-tree audit.

**Preceding result: reflection positivity and a completed carrier for the ORIGINAL signed form.**
[`BF4ExactSlabAllCutoffReflectionPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllCutoffReflectionPositivity.lean)
proves `exact_quadratic_eq_squareSum` and `exact_quadratic_nonnegative`:
`Q(c) = sum_j a_j (Haar P_j)^2 >= 0`, at extent one, every cutoff K,
`w >= 0`, and arbitrary signed boundary coefficients. The actual channels
are lower-local; product Haar factors across disjoint quaternion blocks by
its explicit monomial moments, without an independence axiom. This closes
the finite-slab positivity step for the same signed law.

[`BF4ExactSlabFiniteCutoffGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabFiniteCutoffGNS.lean)
then constructs `exactGNSData` with its bilinear field definitionally equal
to the original reflected kernel form, and `exactCompletion` for each K.
`exactEmbed_pairing` pins the completed dense inner product to that form.
The vacuum-code vector has norm one and is non-null, including after
completion. Limits use the existing explicit-modulus representative-family
API; no representatives of arbitrary quotient-valued sequences are selected
by choice. This does not assert vacuum stationarity or a transfer operator.

**Next:** a cutoff-compatible carrier and geometric physical time/transfer
for this exact law, followed by a strict bound on that same completed vacuum
complement. Arbitrary-volume positivity, thermodynamic/continuum control,
QFT axioms and the all-group Clay target remain open.

Six focused monitored checks passed: 57 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. This is not a
full-tree build or audit.

**Preceding result: the SAME signed quadratic has an explicit global reflected-square expansion.**
[`BF4ExactSlabReflectedSquareHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedSquareHaarForm.lean)
proves `Q(c) = Haar(sum_j a_j theta(P_j) P_j)` for the ORIGINAL extent-one
signed slab form, every cutoff K, rational heat parameter w and signed
boundary coefficient function c. The finite tree stores all weights and
channels as computable data; its weights are nonnegative when `w >= 0`.

The proof uses literal spatial-link reflection of the actual representation
columns, then expands products into all cross-terms on the SAME carrier.
[`BF4ExactSlabReflectedSquareGluing.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedSquareGluing.lean)
retains shared links, original heat coefficients and the full signed
observable. Explicit 116-link support licenses the final Haar identity.
No independent-face assumption, numerical oracle or positivity premise is used.

The subsequent result above proves lower-half locality, reflected Haar
factorization and extent-one slab positivity. The square expansion alone
was not a positivity theorem. Physical time/transfer, the exact-law
completed gap and continuum/Clay remain open.

**Preceding result: the SAME signed quadratic has a spatial reflected-Gram interface.**
[`BF4ExactSlabTemporalGaugeHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeHaarForm.lean)
proves `Q(c) = Haar(F_c * H_spatialGram * theta(F_c))` for the ORIGINAL
extent-one signed slab form, at every spin cutoff, rational heat parameter
and signed boundary coefficient function. The lower observable and its
literal reflection are unchanged. Each interface factor is now a heat sum
of Gram kernels of an original spatial link and its actual reflected mate;
the fixed-time links have been removed from those arguments.

[`BF4ExactSlabTemporalGaugeObservableImages.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeObservableImages.lean)
extends the full-chain link/word pin through the actual character recurrences,
heat products and signed observable sums. Its target evaluates the independently
defined common assignment, not the chain itself. All heat coefficients,
physical face IDs and reflected labels are retained.
[`SU2QuaternionTranslationPolynomialImages.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationPolynomialImages.lean)
provides the coefficient-sensitive algebra and supported Haar bridge.

This closed the same-observable temporal change of variables. The algebraic
global square expansion, lower-half locality, Haar factorization and
extent-one slab reflection positivity are now proved above.

**Preceding result: the full upper-link image and original plaquette words.**
[`BF4ExactSlabTemporalGaugeUpperCoordinates.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeUpperCoordinates.lean)
proves that the WHOLE original chain sends every upper link to
`g_start^-1 U g_end`. The target link's two endpoint shears produce that word;
every other link batch preserves it because its selected coordinate is
different and all endpoint gauges are fixed. Absent endpoints remain the
existing identity fallback. Together with the lower/fixed theorem, this
identifies the common assignment on EVERY actual physical link, at arbitrary
extent and half-plane. `temporalLedger_plaquette_word` then identifies the
image of every ORIGINAL oriented plaquette holonomy with the previously
defined common temporal face word.

[`SU2QuaternionTranslationWordComposition.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationWordComposition.lean)
supplies coefficient-sensitive chain composition, ordered multiplication,
conjugation and constant preservation. Explicit common padding covers empty
chains; no Haar integration or sphere relation is used to erase a discrepancy.
The full observable identity and global reflected-square gluing are now
proved above, as are lower-half factorization and extent-one positivity.

**Preceding result: literal temporal ledger and its full fixed-coordinate frame.**
[`BF4ExactSlabTemporalGaugeLedger.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeLedger.lean)
generates the actual upper-link shear chain at every slab extent: left-inverse
by the starting fixed-time link, then right-direct by the ending fixed-time
link. An absent endpoint contributes no step, matching the existing identity
fallback without adding variables. Index bounds and distinctness are proved
structurally. The chain preserves the SAME full product-Haar integral for
every supported polynomial, with no degree bound or scan hypothesis.

[`BF4ExactSlabTemporalGaugeFixedCoordinates.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFixedCoordinates.lean)
identifies the WHOLE chain with the common assignment on every actual lower
or fixed link. Every emitted multiplier is a fixed-time link, and the chain
leaves these coordinates unchanged. The coefficient version uses explicit
common padding and covers empty ledgers. The new theorem above completes the
upper-link image.

**Preceding result: all four shear images, with full coefficient equality.**
[`SU2QuaternionCoordinateConjugation.lean`](lean/YMGap/Continuum/SU2QuaternionCoordinateConjugation.lean)
identifies the original coordinate-sign substitution with quaternion
conjugation on precisely its named block. It fixes all other blocks and
preserves ordered products. The conjugate--translate--conjugate construction
in [`SU2QuaternionInverseTranslationCoordinates.lean`](lean/YMGap/Continuum/SU2QuaternionInverseTranslationCoordinates.lean)
then proves the actual coordinate image of every left/right, direct/inverse
shear, at arbitrary valid indices. Every non-selected link, including the
multiplier, is unchanged.

[`SU2QuaternionTranslationCoordinateCoefficients.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationCoordinateCoefficients.lean)
upgrades those prefix identities to full coefficient-probe equality against
the correctly padded original quaternion product. This is the equality
consumed by the existing word/product composition theorems, without finite
coordinate scans. The full-chain link and plaquette-word identification is
now supplied by the latest result above.

**Preceding result: structural direct selected-link substitution.**
[`SU2QuaternionHeadSubstitutionPrefix.lean`](lean/YMGap/Continuum/SU2QuaternionHeadSubstitutionPrefix.lean)
proves that the actual head substitution replaces its four variables by the
supplied quaternion and fixes every tail variable, respecting finite-coordinate
prefix equivalence even across different trailing-zero padding.
[`SU2QuaternionSelectedTranslationCoordinates.lean`](lean/YMGap/Continuum/SU2QuaternionSelectedTranslationCoordinates.lean)
then proves the actual direct left/right shear's ordered product image for
arbitrary carrier size and selected/multiplier indices. Every other coordinate
is unchanged. Arbitrary subsequent direct/inverse shear chains preserve these
prefix identities. No enumerated coordinate certificate is assumed.

**Preceding result: temporal gauge cancellation on the literal slab faces.**
[`SU2QuaternionHaarGaugeCancellation.lean`](lean/YMGap/Continuum/SU2QuaternionHaarGaugeCancellation.lean)
proves ordered vertex-gauge cancellation under every polynomial Haar
insertion. Hamilton factors are not commuted. In a crossing word
`A B C^-1 D^-1`, substituting `C := D^-1 C B` cancels both fixed-time links
and leaves `A C^-1`.

[`BF4ExactSlabTemporalGaugeFaces.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFaces.lean)
uses ONE vertex field from the actual fixed-time link coordinates, acting
only on upper links. Lower faces are unchanged, upper characters are
preserved at every spin, and crossing faces reduce to their actual reflected
spatial-link Gram kernel at every odd slab extent. All spectator insertions
remain available, including overlapping face factors.

**Next:** combine the literal spatial reflected-Gram channels into the SAME
slab form's global square decomposition. The full observable change of
variables is proved; slab positivity is not. Physical time,
the completed physical gap and continuum/Clay construction remain open.

The three new modules passed focused monitored one-worker 20 GiB checks: 53
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: all-degree Haar translation, without polynomial scans.**
[`SU2QuaternionTranslationHaarMoments.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationHaarMoments.lean)
converts the closed Gaussian formula to the ORIGINAL exact sphere moments,
retaining every tail coefficient. Even degrees use an explicit positive
radial denominator; odd degrees vanish before tail integration.

[`SU2QuaternionAllDegreeHaarTranslation.lean`](lean/YMGap/Continuum/SU2QuaternionAllDegreeHaarTranslation.lean)
then proves that the original selected left/right substitutions preserve
the full product-Haar value for every supported polynomial. The support and
distinct-block guards remain; the executable scan premise is gone.
[`SU2QuaternionAllDegreeHaarTranslationChain.lean`](lean/YMGap/Continuum/SU2QuaternionAllDegreeHaarTranslationChain.lean)
includes inverse multipliers and arbitrary finite chains. Its concrete
consumer proves Haar preservation for the existing 139-step BF4 tree-gauge
ledger at every polynomial degree.

The common temporal assignment's face algebra is now proved above. Its
identification with these Haar-preserving shears and the SAME slab form's
reflected-square gluing remain open, as do slab positivity, physical time,
the completed physical gap and continuum/Clay construction.

Four new modules passed focused monitored one-worker 20 GiB checks: 22
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: closed all-degree Gaussian moments for the actual translations.**
[`SU2QuaternionTranslationGaussianMoments.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationGaussianMoments.lean)
proves `translatedHeadMonomial_gaussian_closed` for the ORIGINAL left/right
quaternion translation polynomials, at every exponent quadruple. Their
partial Gaussian integral is the existing exact `gaussianMoment4` coefficient
times the retained radius to half the total degree. Equality retains every
tail coefficient; no unit-radius or moment-equality premise is assumed.

The proof pulls head-independent factors through the partial integral,
compresses equal-label contractions to their exact count, and inducts by
removing two coordinate factors. Unmatched labels vanish without division.
Constructive count/length lemmas replace generic erase lemmas whose axiom
dependencies fail this project's gate.

Sphere/radial conversion and unconditional selected Haar translation are now
proved above. Shared-link reflected-square gluing, slab positivity, physical
time, the completed physical gap and continuum/Clay construction remain open.

Three new modules passed focused monitored one-worker 20 GiB checks: 17
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: an all-degree recurrence for the actual quaternion translations.**
[`SU2QuaternionHeadGaussianIBP.lean`](lean/YMGap/Continuum/SU2QuaternionHeadGaussianIBP.lean)
proves polynomial-valued Gaussian integration by parts while retaining
every tail coefficient: `E[u_i P] = E[partial_i P]`, for arbitrary degree.
Its Euler/gradient identity yields the corresponding directional-derivative
formula for head-linear harmonic polynomials.

[`SU2QuaternionTranslationGaussianStein.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationGaussianStein.lean)
applies that theorem to the ORIGINAL products `a*u` and `u*a`. Their
gradient Gram matrix is the retained radius `|a|^2` times the identity.
`translatedWord_gaussian_recursion` therefore gives the exact Wick
contraction recurrence at every word length. `translatedHeadMonomial_eq_word`
pins it coefficientwise to the existing four-exponent translation API.
The induction is unbounded; only the small four-coordinate algebra uses
finite kernel certificates. No larger table of moment checks is required
by this recurrence.

The closed Gaussian and Haar moments and unconditional selected translation
are now proved above. Shared-link reflected-square gluing remains open.
This is not slab reflection positivity or a mass-gap estimate.

Both new modules passed focused monitored one-worker 20 GiB checks: 22
printed axiom gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: the original slab quadratic uses its literal path channels.**
[`BF4ExactSlabPlaquettePathGram.lean`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePathGram.lean)
proves the ordered plaquette identity `a b c^-1 d^-1 = (a b)(d c)^-1`
coefficientwise. Both actual paths have Haar-unit radius, so the all-spin
character Gram identity applies under every insertion on the original link
carrier. This works at every slab extent and spin. On a crossing face, the
paths are lower-then-fixed and fixed-then-upper: shared time links remain.

[`BF4ExactSlabInterfacePathGram.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfacePathGram.lean)
retains the original `coeffW` heat weights and composes the local identities
across all 24 interface faces. `exact_quadratic_eq_pathGramHaar` identifies
the ORIGINAL signed quadratic with this path-channel product between the
same lower observable and its literal reflection, at extent one for every
rational heat parameter and cutoff. No independent-link model is substituted.

**Next:** integrate the shared time links into a global reflected-square
decomposition. This equality does not yet prove slab reflection positivity.
The selected Haar-translation lemmas still require an explicit polynomial
check; their cached moment certificate covers degree five, not all spins.
The all-degree Gaussian recurrence above is now proved, but its conversion
to an unconditional Haar-translation theorem remains open. Physical
time/transfer, the completed physical gap, continuum QFT and all-group Clay
remain open; no canonical frontier atom was closed.

Both new modules passed focused monitored one-worker 20 GiB checks: 23
printed axiom gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: actual all-spin character kernels have explicit Gram channels.**
[`SU2QuaternionSymmetricPowerKernelGram.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerKernelGram.lean)
proves that the ORIGINAL polynomial trace of `Sym^n D(conj(p)*q)` is a sum
of Hermitian pairings of the actual representation columns. The weights are
the explicit positive rationals `1 / C(n,k)`. The proof retains every
coefficient, so it is valid before evaluation or Haar integration; it needs
no diagonalization, eigenvector choice or square-root normalization.

[`SU2QuaternionPolynomialGramPositivity.lean`](lean/YMGap/Continuum/SU2QuaternionPolynomialGramPositivity.lean)
proves the finite quadratic is the corresponding weighted sum of Hermitian
squares for arbitrary complex polynomial coefficients. The existing Haar
square-positivity theorem then gives `characterKernelQuadratic_haar_nonneg`
for the ORIGINAL BF4 character kernel. Its explicit conditions are Haar-unit
radii for the input words and finite-coordinate support for their column
syntheses, all on the same Haar carrier. Pairwise product radii are derived,
not supplied as another premise.

The path-pair realization and same-law heat-product consumer above now pin
these kernels to the crossing geometry. Shared-link reflected-square gluing
is still open; the local positivity theorem alone does not supply it.

Four new modules passed focused monitored one-worker 20 GiB checks: 70
printed axiom gates, all within `{propext, Quot.sound}`, no errors/warnings.
No new sorry, analytic premise, rate estimate or raised proof limit; no
full build/audit. These combinatorial basis weights are not a mass-gap bound.

**Retained result: the actual trace is the original character under Haar.**
[`BF4ExactSlabSymmetricPowerHaarTrace.lean`](lean/YMGap/Continuum/BF4ExactSlabSymmetricPowerHaarTrace.lean)
proves `slabPlaquette_trace_haar_character` for every slab extent and spin.
The real trace component equals the ORIGINAL plaquette character under
every polynomial insertion in the same product-Haar integral; the imaginary
component vanishes there. The ordered link word and its signs are unchanged.

The proof has two inputs. First,
[`SU2QuaternionSymmetricPowerHaarTrace.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerHaarTrace.lean)
identifies the literal matrix trace coefficientwise with the solid-zonal
polynomial of its actual radius, at every degree. Second, quaternion norm
multiplicativity and the existing Haar sphere relation prove that the
ORIGINAL slab plaquette has Haar-unit radius. These inputs discharge the
radius premise and permit the existing solid-zonal character theorem to
apply under arbitrary spectator insertions. Pointwise equality is never
silently passed through integration.

**Next:** positive reflected channels of the literal interface heat kernels
AND their link-local gluing. The new identity is not positivity of the
reflected slab form. The physical time/transfer pin, completed physical gap,
volume/spacing control, continuum QFT and all-group Clay target remain open.

All four new modules passed focused monitored one-worker 20 GiB checks:
52 printed axiom gates, all within `{propext, Quot.sound}`, no errors/warnings.
No new sorry, analytic premise, numerical oracle, rate or raised proof limit;
no full build/audit. The original signed-Haar law remains distinct from the
positive multiplicity-product model.

**Retained result: the actual all-degree trace is the original character.**
[`SU2QuaternionSymmetricPowerTrace.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerTrace.lean)
proves `trace(Sym^n D(q)) = U_n(q.r)` for every degree and every rational
unit quaternion, with zero imaginary part. The trace is the sum of the
actual action's diagonal entries. A two-row coefficient identity, summed
along the diagonal, gives the trace recurrence; the actual quaternion norm
supplies its determinant-one relation. No eigenvalue choice or
diagonalization is needed.

[`SU2QuaternionSymmetricPowerPolynomial.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerPolynomial.lean)
constructs every literal polynomial matrix entry and proves that evaluation
recovers the same action. Its diagonal sum evaluates to the ORIGINAL BF4
`characterPolynomial` whenever the evaluated quaternion has unit norm.
All raw spectator coefficients remain in the constructed polynomials.

These two modules establish evaluation identities. The new modules above
supply the separate coefficient-probe and sphere-ideal proofs needed for
Haar use. Local character Gram channels are now proved above. Their physical
interface realization, link-local gluing, the physical operator gap and
continuum passage remain open.

Both new modules passed focused monitored one-worker 20 GiB checks: 33 printed
axiom gates, all within `{propext, Quot.sound}`, no errors/warnings. No new
sorry, analytic premise, numerical oracle, or raised proof limit; no full audit.

**Retained algebraic component: actual symmetric-power representations.**
[`SU2QuaternionTensorPowerAction.lean`](lean/YMGap/Continuum/SU2QuaternionTensorPowerAction.lean)
lifts the existing Hamilton-quaternion fundamental matrix to every finite
tensor degree. Composition, identity, inverse and the adjoint identity are
proved; rational unit quaternions preserve the explicitly positive Hermitian
form. The full tensor power is not presented as an irreducible character.

[`SU2QuaternionSymmetricPowerAction.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerAction.lean)
proves that this action preserves symmetric tensors and reconstructs every
such tensor from its `n+1` explicit complex coefficients. The resulting
`symmetricAction` is complex-linear, obeys actual quaternion multiplication,
and preserves its inherited Hermitian form. These are structural proofs for
every degree, with no large assignment enumeration or binomial square roots.

The trace identification is now proved at evaluation and arbitrary-insertion
Haar levels above. Resolution and gluing of the literal interface kernels
remain open. The representation is over rational unit quaternions; it does
not itself supply compact-group completion. Neither slab reflection positivity
nor a physical spectral gap is claimed. The original signed-Haar law is unchanged.

Both new modules passed focused monitored one-worker 20 GiB checks: 42 printed
axiom gates, all within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full audit.
The dependency target also completed. Its first invocation inherited an old
32 GiB repository default; the target was then repeated with an explicit
20 GiB override. The new-module checks used 20 GiB throughout.

**Retained direct-route result: the original form uses the literal reflected
observable.**
[`BF4ExactSlabReflectedObservableHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedObservableHaarForm.lean)
proves `Q(c) = Haar(F_c * (H * theta(F_c)))` for the ORIGINAL signed slab
quadratic. Here `F_c` is the heat-dressed lower observable, `H` is the product
of the 24 actual face heat polynomials, and `theta` permutes the physical
link blocks and inverts the time links. The bilinear version also allows
different arbitrary signed coefficients on the two sides.

`lowerObservable_reflection_insert` proves the upper/lower reflection pin
with every spectator polynomial supported on the same 116 links retained.
The proof transports each all-spin plaquette word and its heat coefficient,
then the whole lower face list, then the observable sum. Scope: every
rational w and every cutoff K, extent one. It does not assume positivity.

**Next:** a positive reflected-channel resolution of the actual interface
heat kernels and its composition on the literal link geometry. The displayed
Haar identity is not itself a positivity theorem. Exact-law physical time,
the completed gap and volume/spacing/continuum control remain open.

Verification: the new module passed seven axiom gates. The two small API
additions in each dependency were checked too: 15 gates in the reflection
module and 11 in the factorization module. All three focused monitored
one-worker 20 GiB checks passed without final errors/warnings, within
`{propext, Quot.sound}`. No new proof hole, analytic premise, numerical oracle
or raised proof limit; no full build/audit.

**Retained direct-route result: the interface sum is an exact local heat
product.**
[`BF4ExactSlabInterfaceHeatProduct.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfaceHeatProduct.lean)
proves finite distributivity over the existing bounded label enumeration.
`interfaceHeatInsertion_eq_product` identifies the original global
interface insertion with the product of its 24 face heat polynomials,
each retaining the actual plaquette holonomy and `coeffW w spin` weights.
The proof works symbolically at every cutoff; it does not enumerate the
`(K+1)^24` global boundary states.

`observableIntegrand_eq_product` retains arbitrary signed lower and upper
observables before integration. `exact_bilinear_eq_productHaar` and
`exact_quadratic_eq_productHaar` then give the ORIGINAL signed forms with
this exact local heat product. Scope: every rational w, every spin cutoff,
extent one. There is no new rate or positivity claim.

The next substantive step is a positive reflected-channel resolution of
these local face kernels and its composition on the actual slab geometry.
Neither positive heat coefficients alone nor the finite product identity
asserts reflection positivity. Physical time, the completed exact-law gap,
volume/spacing control, continuum QFT and the all-group target remain open.

The new module passed all 10 printed axiom gates; the small fold API addition
in its factorization dependency was also checked (9 gates in that module).
Both focused monitored one-worker 20 GiB checks passed without errors or
warnings, within `{propext, Quot.sound}`. No new proof hole, analytic premise,
rate constant, numerical oracle or raised proof limit; no full build/audit.

**Retained direct-route result: every signed boundary form is a literal
action-side Haar integral.**
[`BF4ExactSlabWeightedFaceFactorization.lean`](lean/YMGap/Continuum/BF4ExactSlabWeightedFaceFactorization.lean)
proves coefficient-probe equality between the original heat-weighted
72-face network and its lower/interface/reflected-upper polynomial
product, retaining all 116 link coordinates. The equality survives every
additional polynomial insertion. All original heat coefficients and
signed Haar contractions are retained.

[`BF4ExactSlabObservableHaarForm.exact_bilinear_eq_haar`](lean/YMGap/Continuum/BF4ExactSlabObservableHaarForm.lean)
then sums arbitrary signed boundary coefficients into the lower and upper
polynomials. The ORIGINAL exact slab bilinear form is precisely
`Haar(lowerObservable * (interfaceHeatInsertion * upperObservable))`.
`exact_quadratic_eq_haar` specializes to the same observable on both sides.
This holds for every representation cutoff and every rational heat
coordinate, at extent one. It is algebraic, not a coupling-uniform estimate.

This is a proved connection within the signed-Haar law, not an identity
with the positive conditional model. Reflection positivity of the displayed
integral, a physical time operator and its completed gap still require
proof. The next algebraic step is to resolve the literal interface heat
insertion into reflection-positive channels while keeping these observable
and link-coordinate identifications.

Both new modules passed focused monitored one-worker 20 GiB checks, with
all 15 printed axiom gates within `{propext, Quot.sound}` and no final
errors or warnings. No new proof hole, analytic premise, rate constant,
or raised proof limit; no full build/audit/guard run.

**Retained obstruction: the discrepancy survives cutoff removal and completion.**
The literal six-face cube row supplies the explicit floor
`delta(w) = (coeffW w 1)^6 / (1 + (coeffW w 1)^6) > 0` for every `w>0`.
The signed-Haar vacuum-delta quadratic is exactly `1`, while the positive
normalized value is at most `1-delta(w)` for EVERY representation cutoff
`K>=1`. The new
[`BF4ExactPhysicalCutoffLimitSeparation.lean`](lean/YMGap/Continuum/BF4ExactPhysicalCutoffLimitSeparation.lean)
passes this bound to the original normalized `CReal` limit for `0<w<1`;
[`BF4PhysicalCubeExactActionFence.lean`](lean/YMGap/Continuum/BF4PhysicalCubeExactActionFence.lean)
pins it to the literal root's squared norm in the existing reflected
completion at `w=1/400`. That root cylinder is not the stationary vacuum.
The floor is cutoff-independent but explicitly coupling-dependent.

The physical frontier requires an exact-law construction or a separately
proved nonidentity observable/norm comparison, with physical time pinned
to that same law. No such replacement follows from the conditional gap or
from this obstruction. Volume, spacing, continuum QFT and all-group
passage remain open. Neither cutoff removal nor completion repairs the
literal identity.

Both new modules passed focused monitored one-worker 20 GiB checks, with
all 17 printed axiom gates within `{propext, Quot.sound}`. The untrusted
exact-rational pilot checked 404 algebraic implications; Lean separately
proves the physical bound and the displayed anchor constant. No new proof
hole, analytic premise, or raised proof limit; no full build/audit/guard run.

**Retained conditional result: decay and uniqueness for the same operator.**
At `w=1/400`, extent one, the completed reflected conditional operator
has strict norm contraction, correlation decay, and vacuum isolation.
For every completed `x` orthogonal to the constructed stationary vacuum,
Lean now proves

```text
||T^n x||_E^2 <= (q*q)^n ||x||_E^2
(1-q) ||x||_E^2 <= ||x||_E^2 - <T x,x>_E,   1-q > 0.
```

Completed Cauchy--Schwarz gives squared-correlation decay, including a
direct bound on the existing `centeredCubeCorrelator` with its exact
conditional-moment identity. A fixed vector in the vacuum complement must
be zero; two fixed vectors with the same vacuum pairing coincide. Thus the
constructed positive-norm vacuum is uniquely stationary at its own vacuum
pairing. This does not assume a unit vacuum or construct an arbitrary-real
scalar decomposition of every vector.

The proof applies the marginal gap at `P x`, obtaining
`M(Px,P^2 x) <= q M(Px,Px) <= q^2 M(Px,x)`, then uses the original reflected
pairing and the already explicit approximation rates. No operator or norm
is replaced. See
[`BF4PhysicalCubeCompletedReflectedDecay.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedDecay.lean)
and [`BF4PhysicalCubeVacuumIsolation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeVacuumIsolation.lean).
Both focused monitored checks passed all 15 printed axiom gates within
`{propext, Quot.sound}`. No new proof hole or analytic premise; no full
build/audit/guard run.

**Input: the constructed rate survives both completions.**
`BF4PhysicalCubeCompletedMarginalGap.cofinalSectorGap` supplies the existing
sector-only limit interface on the explicit schedule `max(request,K0(w))`.
For every fixed `0<w<=1/2`, the resulting completed marginal form gap and
conditional-iterate norm decay use the original `q(w)`.

At `w=1/400`, extent one, positivity gives
`||P x||_M^2 <= q(w) <P x,x>_M`. The exact comparison identities identify
these quantities with the reflected transfer form and reflected norm.
`BF4PhysicalCubeCompletedReflectedGap.completed_reflected_form_bound`
therefore proves

```text
<T x,x>_E <= q <x,x>_E,   0 < q < 1,
for EVERY x in the completed reflected vacuum complement.
```

There is no supplied gap, vector-dependent prefactor, or rate loss. The
argument uses the actual vacuum sector, never the reducible full carrier;
it does not pretend the marginal and reflected norms are equal.
See [`BF4PhysicalCubeCompletedMarginalGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedMarginalGap.lean)
and [`BF4PhysicalCubeCompletedReflectedGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedGap.lean).
Both focused monitored checks passed all 13 printed axiom gates within
`{propext, Quot.sound}`. No new analytic premise or proof hole was added;
the full build/audit/guard was not run.

**Input: a constructed cutoff-uniform strict centered form bound.**
At extent one, for every fixed `0<w<=1/2`, Lean constructs a rational
`q(w)` and an explicit onset `K0(w)` such that

```text
0 < q(w) < 1
|P_K(f)| <= q(w) * N_K(f)
    for EVERY K >= K0(w) and EVERY stationary-mean-zero f.
```

`P_K` is the original physical matrix quadratic and `N_K` its original
stationary squared norm. For the fixed head B=1404, the existing persistent
edge floor F(w) and loop-free path scale S(w) give the computed constant
`C(w)=S(w)/F(w)`. The new proof controls the head by the original full
energy; summing costs only the stationary mass <=1. The previous tail
absorption then gives `N_K(f)<=(1+3*C(w))*E_K(f)`, and exact rational
algebra produces `q(w)=(1+6*C(w))/(2+6*C(w))`.

The rate and onset **depend on w**. This is not a coupling-, volume-, or
lattice-spacing-uniform physical gap. It supplies the completed result
above. Exact action/geometric time, the continuum vacuum and QFT,
thermodynamic/continuum passage and Clay remain open.
See [`BF4PhysicalCubeAnchoredHeadBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeAnchoredHeadBound.lean)
and [`BF4PhysicalCubeCutoffUniformGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGap.lean).
Both focused monitored checks passed all 20 printed axiom gates. The exact
untrusted path/algebra pilot passed 1,089 rooted bounds and four rate identities;
no numerical BF4 spectral oracle was used.

**Input: a fixed-head, root-anchored energy inequality.**
At extent one, for every `0<w<=1/2`, every spin cutoff `K>=1404`, and
every coefficient `f` of zero stationary mean, Lean proves

```text
N_K(f) <= E_K(f) + 3 * N_K(head_1404(f - f(vacuum)))
```

Here `N_K` is the original stationary squared norm and `E_K` is the
original directed physical Dirichlet energy, exactly twice `N_K-P_K`.
The proof establishes an **uncentered** tail rate `1/4`, absorbs the
mixed block by Gram positivity, and subtracts the root value without
changing the energy. Neither unit sector mass nor a strict head rate is
assumed. The head cutoff stays fixed while K grows.

The previously missing fixed-head constant is now supplied by the result
above. This absorption theorem alone does not supply it. See
[`BF4PhysicalCubeTailAbsorption.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTailAbsorption.lean).
The focused monitored Lean check passed all 12 printed axiom gates;
the exact untrusted algebra pilot passed 29,141 positive-block checks.

**Input: the actual centered new-tail form is uniformly small.**
For any positive rational epsilon, take the explicit old cutoff
`B=1400+epsilon.den`. At extent one, for every `0<w<=1/2` and every later
cutoff K>=B, Lean proves

```text
exactCenteredNewTailTrace(B,K) <= epsilon
centeredGram_K(tail,tail) <= epsilon * stationaryNormSquared_K(tail)
```

The second bound holds for **every** literal new-tail coefficient vector,
not just a probe. The proof injects each radius-M shell into `(M+1)^6`
six-label codes and partitions the original conditional diagonal sum
exactly by radius. Genuinely new indices have radius greater than B,
so the Gaussian radial estimate below bounds the existing old/new-block
trace. Its centered stationary subtraction only decreases that trace.

This discharges the trace input of the existing head--tail compiler.
That earlier compiler still gives rate `q+epsilon` from a sufficient
centered head rate q. The newer anchored route above now proves a strict
full rate without needing that comparison.
Exact action/geometric time, vacuum uniqueness and
volume/spacing/continuum passage also remain open. See
[`BF4PhysicalCubeHighLabelTrace.lean`](lean/YMGap/Continuum/BF4PhysicalCubeHighLabelTrace.lean)
and [`BF4PhysicalCubeNewTailTraceBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNewTailTraceBound.lean).
Both focused monitored checks passed, all 18 gates within
`{propext, Quot.sound}`; no new sorry or full-tree audit.

**Input: Gaussian suppression of actual high-label self-return.**
At extent one, every member of the original vacuum sector whose largest
cube label is M>=1400 satisfies, for every admitting cutoff and `0<w<=1/2`,

```text
P_K(source,source) <= 4096*(M+1)^6*w^floor(M^2/72)
```

The theorem concerns the existing `centralPhysicalConditionalKernel`;
cube support and parity are derived from canonical sector membership.
The proof combines the complete boundary comparison below with an exact
six-dimensional heat factorization and the quadratic Casimir decrease.

The degree-12 radial envelope
`R_w(M)=4096*(M+1)^12*w^floor(M^2/72)` also has a proved successor ratio at
most 1/2 beyond 1400. Every finite tail starting at N>=1400 is at most
`2*R_w(N)`. The explicit threshold `N(epsilon)=1401+epsilon.den` makes
every such tail at most epsilon, uniformly for `0<=w<=1/2`.
The six-label counting/trace connection is now proved above. Sufficient
head control remains open; scalar summability or a small tail alone is not
an all-vector spectral gap. See
[`BF4PhysicalCubeGaussianReturn.lean`](lean/YMGap/Continuum/BF4PhysicalCubeGaussianReturn.lean).
All 21 gates passed in its focused monitored check; the reused heat-product
module was also checked. No new sorry or full-tree audit.

**Input: full boundary summation and an actual diagonal/row
comparison.** At extent one, for every representation cutoff and explicitly
for `0 <= w <= 1/2`, Lean proves

```text
boundaryOverlap(source,target) <= 4096 * boundaryHeat(difference(source))
```

The proof factors an upper estimate over the original 24-coordinate
enumeration: twelve active heat tails each cost at most 2, and twelve
inactive labels are forced zero. Combining this with the balanced physical
move below gives, for every bounded common-parity cube source and K>=2,

```text
H(balanced(source)) * P_K(source,source) <= 4096 * H(source)
```

Here H is the actual half-state heat product, and P_K is the original
normalized reflected joint divided by its own stationary marginal; the
common partition cancels exactly. This is not a replacement dynamics or a
state-uniform transition floor. The Gaussian return bound and radial
summability are now proved above; the actual trace connection and sufficient
centered head--tail control or weighted norm coverage remain open. Neither an all-vector
strict rate nor a geometric-time identification follows yet. See
[`BF4PhysicalCubeBoundarySumBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBoundarySumBound.lean).
The focused monitored check passed all 13 axiom gates within
`{propext, Quot.sound}`. No full-tree audit was run.

**Input: an all-state balanced physical move with quadratic Casimir
descent.** For a cube-supported common-parity state, let M be its largest
label. On each cube face replace s by
`2*(floor(2*floor(s/2)/3)+ceil(M/12))`. This computed target preserves every
minimal source difference-boundary channel, belongs to the actual vacuum
component, fits every original cutoff `K>=2`, and has a proved positive
entry in the original physical kernel. Its excess radius above 11 contracts
by `5/6`. Writing C for the sum of the six `c4(s)=s*(s+2)` values
(four times the SU(2) Casimir), Lean proves

```text
72*C(target) + M^2 <= 72*C(source)                 when M >= 1400
864*C(target) <= 863*C(source)                    when M >= 1400
```

The proof uses a sum-of-squares reserve at a maximal label to pay the
rounding and common offset. These are **label-energy rates, not operator
or mass-gap rates**. The boundary-sum and diagonal/row comparison is now
proved above; the resulting weighted norm or centered head--tail estimates
remain open. See
[`BF4PhysicalCubeBalancedDescent.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedDescent.lean)
and [`BF4PhysicalCubeBalancedCasimir.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedCasimir.lean).
Both modules passed focused monitored checks; all 46 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Retained route correction:** a **cutoff-uniform direct inward-mate transition
floor is impossible** at each fixed `0 < w <= 1/2`, including `w=1/400`.
In six-face coordinates, take

```text
source       (2k+14, 0, 0, 0, 0, 0)
inward mate  (2k+13, 1, 1, 1, 1, 1)
competitor   (2k+12, 2, 2, 2, 2, 2)
```

Both targets have the same complete boundary mask against the source.
Their SU(2) dimension/Casimir comparison gives, for every `K >= 2k+14`,
`P_K(source,mate) <= w^(4k+2)` for the **original normalized physical
conditional kernel**. The sources belong to the actual vacuum component;
an explicit cofinal tolerance modulus proves the no-floor theorem. See
[`BF4PhysicalCubeInwardMateCompetitor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateCompetitor.lean)
and [`BF4PhysicalCubeInwardMateNoUniformFloor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateNoUniformFloor.lean).
This does **not** refute a full-operator gap or the proved averaged traffic
bounds. The analytic frontier remains weighted norm coverage/Poincare,
without assuming a uniform probability for the single selected mate edge.
Both modules passed targeted monitored checks; all 28 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Previous positive result:** the constructed excitation has a **two-sided strict
relative response** for the SAME completed physical transfer:

```text
l * ||d||_E^2 <= <T d,d>_E <= q * ||d||_E^2,  l > 0, q < 1
```

The new full-space estimate is
`<x,test>_E^2 <= <T x,x>_E * ||test||_marginal^2` for every completed
reflected vector x and every finite cube test. It uses the original marginal
norm on the right, not the weaker reflected norm. Dense physical
Cauchy--Schwarz and the same-object pairing limits prove it without a gap
assumption. Dense tests then show that zero response forces x=0, so the
completed transfer kills no nonzero vector. These are not bounds away from
zero uniformly over vectors, nor bounds away from the vacuum eigenvalue one.

For `d = T root - root`, let delta be the existing positive probe-pairing
floor, C the computed marginal squared-norm ceiling of that probe, U the
existing squared-norm ceiling for d, and eta its proved positive deficit.
The displayed rates are explicit rational data:
`l = delta^2/(C*U)` and `q = 1 - eta/U`. They are proved for **this one
excitation**, not for every centered vector. See
[`BF4PhysicalCubeMixedTestBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeMixedTestBound.lean)
and [`BF4PhysicalCubeExcitationResponse.lean`](lean/YMGap/Continuum/BF4PhysicalCubeExcitationResponse.lean).
All 25 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. A common dense q<1,
a unit-normalized canonical geometric-time probe, vacuum uniqueness, and
volume/spacing/continuum control remain open.

**Completion bridge:** the **common dense form bound and the bound on the entire
completed reflected vacuum complement are equivalent, with exactly the same
rate `q`**. The dense side uses the original centered physical presentations;
the completed side is not restricted to the older marginal-sector image.
The proof passes both the norm and transfer pairings through the constructed
approximants, using explicit moduli and no choice of quotient representatives.
See `dense_form_bound_iff_completed` in
[`BF4PhysicalCubeDenseFormClosure.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDenseFormClosure.lean),
with represented pairing continuity in
[`GNSRepresentedApproximation.lean`](lean/YMGap/Continuum/GNSRepresentedApproximation.lean).
All 17 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. **No common `q < 1` is
constructed:** that dense analytic estimate, geometric-time identification,
and the volume/spacing/continuum passage remain open.

**Previous result:** a **strict, quantitatively nonzero excitation in the actual
completed vacuum complement**. Define `d = T root - root`; stationarity gives
`<Omega,d>_E = 0` exactly. If `delta = twoStepFloor` is the physical positive
pairing floor below, and `P,R` are computed squared-norm ceilings for the
fixed probe and root representatives, Lean proves

```text
alpha = delta^2 / P > 0
eta   = alpha^2 / (2R) > 0
alpha <= <d,d>_E <= 2R
<T d,d>_E + eta <= <d,d>_E
```

The short argument is quantitative Cauchy--Schwarz, self-adjointness and
`||T x - x||_E^2 <= 2 * (<x,x>_E - <T x,x>_E)` on the full completed
carrier. See
[`BF4PhysicalCubeDissipation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDissipation.lean)
and [`BF4PhysicalCubeStrictExcitation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeStrictExcitation.lean).
All 31 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is still fixed `w=1/400`, extent one. This is **one
vector's strict deficit**, not a uniform relative bound for every vector,
a normalized positive-response probe for the canonical geometric-time root,
vacuum uniqueness, or a continuum gap.

**Physical input:** the **actual completed physical transfer is not the
identity**. A three-state argument witnesses the movement:

```text
single-face twice-spin-two probe -> fundamental cube -> root
           positive edge floors at every cutoff K >= 2
direct probe--root entry = 0, by incompatible SU(2) triangles

<root, probe>_E = 0
<T root, probe>_E >= twoStepFloor > 0
therefore T root != root
```

The positive floor is an explicit product of heat weights and the actual
normalization floor, at fixed `w=1/400` and extent one. The proof retains
one source term in the marginal pairing of the two conditional images,
with independent action and pairing cutoffs, and passes through both
existing completion limits. The exact same-object moment identity then
gives the displayed reflected pairing. No new dynamics is introduced.
See [`BF4PhysicalCubeTransferNonidentity.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTransferNonidentity.lean),
with its physical inputs in
[`BF4PhysicalCubeThreeStatePath.lean`](lean/YMGap/Continuum/BF4PhysicalCubeThreeStatePath.lean)
and [`BF4PhysicalCubeTwoStepPositivePairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTwoStepPositivePairing.lean).
All 42 printed axiom gates passed in targeted checks; no full-tree audit
was run. Nonidentity is not a strict vacuum-complement bound, uniqueness
of the stationary vacuum, or geometric-time identification.

**Connected density result:** the actual centered physical images now approximate every
represented vector in the **whole completed reflected vacuum complement**,
with an explicit rate. This is at fixed `w=1/400` and extent one. The target
need not come from the old marginal-sector image: its only vector property
is orthogonality to the constructed stationary sector vacuum.

The proof combines the centering estimate below with Cauchy--Schwarz. Let
`U` and `R` be computed norm ceilings for the fixed vacuum and root, and set
`K = 2 * (1 + U*R/(64/65)^2)`. For any finite approximant `p` to `x`:

```text
||centered(p) - x||_E^2 <= K * ||p - x||_E^2
input tolerance = epsilon / K
output rate     = supplied Cauchy modulus(input tolerance)
```

[`BF4PhysicalCubeCenteredDensity.centeredDensity`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredDensity.lean)
returns the presentations, modulus and error proof as data. Each approximant
also has its existing explicit centered Cauchy representative. There is no
choice of representatives from arbitrary quotient points. The generic
[`ScaledGNSCompletionEstimates.lean`](lean/YMGap/Continuum/ScaledGNSCompletionEstimates.lean)
preserves the actual normalized pairing and squared-distance modulus.
Both modules passed targeted checks and all 39 printed axiom gates; no full
repository build/audit was run. This is density, not a strict spectral gap.

**Connected centering estimate:** centering has a proved, base-independent error bound in
the **actual reflected norm**. For any finite sector presentation `p`, let
`r` be the root cylinder, `C(p)` its existing limiting correction, and `Omega`
the constructed stationary sector vacuum. The new full-space pairing identity
gives

```text
<centered(p), y> = <p, y> - C(p) <r, y>     for every completed y
||centered(p) - p||^2 = C(p)^2 ||r||^2
(64/65)^2 ||centered(p) - p||^2 <= <Omega,p>^2 ||r||^2
```

The denominator is the same physical root weight for every presentation
base. Thus this estimate has no coefficient-count or growing-cutoff factor.
It remains at fixed `w=1/400` and extent one. See
[`BF4PhysicalCubeCenteringPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringPairing.lean)
and [`BF4PhysicalCubeCenteringControl.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringControl.lean).
The new density witness above supplies the explicit approximation assembly.

**Connected nonzero-vector result:** an explicitly centered single-face spin-two observable
has positive norm in the **actual reflected completion**. Its difference
boundary has zero root amplitude but positive probe amplitude, so one term
of the physical Gram sum-of-squares supplies a lower bound unchanged by
every rational root correction. The existing centered Cauchy sequence
passes that bound to the same completed vector. The witnessing rational is
`(64/65) * channelFloor(1/400) > 0`, where `channelFloor(w)` is an explicit
heat-weight product, not a coupling-uniform constant. This also proves
positivity of its connected conditional covariance at shifted index one
(reflected index zero). See
[`BF4PhysicalCubeSeparatedChannel.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSeparatedChannel.lean)
and [`BF4PhysicalCubeCenteredPositiveNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredPositiveNorm.lean).
A positive norm is not a strict transfer bound or a nonidentity theorem.

**Connected centering result:** the constructed sector vacuum's pairing equals the
original physical stationary mean on the **entire completed marginal
sector**. This identifies the existing moving rationally centered cylinders
with vectors in the new reflected vacuum complement. Their correlators are
proved equal to literal connected covariances under the original physical
law, using the same observable and conditional action, with the exact
one-insertion shift. See
[`BF4PhysicalCubeSectorCenteredRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCenteredRealization.lean).
This uses a rational head correction, not orthogonal projection along the
sector vacuum. Density now has the representative-supplied witness above;
the positive reflected norm is a separate physical-channel argument, not an
inference from a marginal lower bound.

**Connected vacuum result:** a stationary vector in the actual completed cube sector
is now constructed, with squared norm at least `64/65`. This is at fixed
`w=1/400` and extent one, not uniformly in the coupling. Finite component
indicators are zero/one observables with a common envelope; the original
physical tail modulus makes their prefixes Cauchy. Their global image is
exactly the cutoff-independent sector event, and finite stationarity passes
to the same completed transfer. The positive zero-labelled contribution and
partition ceiling supply the explicit norm floor. Self-adjointness then
makes this vector's orthogonal complement invariant, with the same positive
contractive operator. See
[`BF4PhysicalCubeSectorVacuum.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuum.lean)
and [`BF4PhysicalCubeSectorVacuumNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuumNorm.lean).
This stationary vector is neither asserted to have unit norm nor proved to
be the unique fixed direction; a norm floor is not a spectral gap.

**Connected transfer result:** the actual transfer is proved positive, self-adjoint,
rational-linear and contractive on the **entire raw and reflected cube
completions**, at fixed `w=1/400` and extent one. Joint continuity of the
pairing passes the dense squared-distance bound to all vectors with constant
exactly `1`, without a normalization loss. Nondegeneracy and self-adjointness
give the vector-level linearity laws.

The same full-space map now **intertwines the entire existing completed
marginal sector**. The proof tests against dense cube vectors and moves the
transfer across the pairing; no new recoding producer or analytic premise is
assumed. All its natural-power moments on sector images equal the original
physical conditional moments, with the exact extra insertion from the
reflected form. See
[`BF4PhysicalCubeCompletedTransferLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedTransferLaws.lean).

**Boundary of this earlier transfer construction:** constant `1` gives
nonexpansiveness, not a strict gap. The head/tail estimate and same-rate
completion theorem reported above now supply strictness on the reflected
vacuum complement. The nonzero root cylinder is not the stationary sector
event; its movement under the transfer is proved above. Identifying
conditional iterations with geometric Euclidean time and controlling
volume and spacing limits remain open. A Cauchy diagonal modulus is not
a physical decay rate.

**Connected completed-pairing result:** the comparison preserves the actual physical pairing
for **every vector in the completed marginal sector**, not only finite
presentations. The proof slows the existing shared sampler to pay the finite
cube admission cutoff and normalization modulus. Its admissibility is
preserved, so it still constructs the same physical conditional operator.
The two aligned finite forms are eventually equal and have the constructed
completed pairings as limits.

Consequently the mapped sector action is positive, self-adjoint and
E-contractive; its iteration moments equal the original physical moments
with exactly one extra operator insertion. See
[`BF4PhysicalCubeSectorCompletedPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCompletedPairing.lean).
That earlier `mappedTransfer` has the completed marginal sector as its domain;
the new `cubeTransfer` above acts on the whole reflected completion. Its full
rational-linear operator laws and marginal-sector intertwining are now proved,
as is the positive-norm stationary sector vector above. Geometric time and
a strict gap remain open. The result is at fixed `w=1/400`
and extent one; no continuum or coupling-uniform claim follows.

**Connected comparison result:** the existing completed marginal root sector maps to
the reflected cube completion at `w=1/400`, extent one. The map preserves
each finite presentation's literal observable and contracts squared distance
by the proved `E <= B` estimate; its representative Cauchy modulus is unchanged.
Conversely, every finite signed cube vector has a computed marginal-sector
preimage. A common spin cutoff, faithful state-code lookup and finite summation
produce it, including negative coefficients and repeated states. The preimage
has the same observable values on every state, and its reflected image is
exactly the original cube vector. See
[`BF4PhysicalCubeSectorComparison.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorComparison.lean)
and [`BF4PhysicalCubeSectorDensePreimage.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorDensePreimage.lean).

The physical pairing pin now holds on the whole completed source as described
above. The completed transfer map with actual dense agreement and whole-source
intertwining are now proved. A dense preimage is not an inverse between
these two completed spaces.

**Connected completion result:** the literal cube-cylinder image has its reflected-norm
completion at the fixed anchor `w=1/400` and extent one. Two constructed maps
are inverses between this completion and the existing raw cube completion.
They keep the same finite-span sequences; the forward Cauchy modulus is
unchanged and the inverse uses the supplied modulus at `(64/65)*epsilon`.
The full completed pairing is proved to be the limit of the same dense
physical reflected pairings. See
[`BF4PhysicalCubeReflectedCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeReflectedCompletion.lean).

An elementary two-triangle argument also removes an unnecessary obstruction:
the two existing Cauchy moduli compute a null modulus directly, without choice.
The older claim that the legacy completion could not support this inverse
has been corrected.

**Connected dense realization:** the all-spin cube form is identified with the actual
completed physical pairing on its literal observable image. For arbitrary
finite signed lists `u,v`, the map `J` uses the existing exact state cylinders,
and the kernel-checked equality is
`E(Ju,Jv) = lambda * rawCubeForm(u,v)`.
At the fixed anchor `w=1/400`, its squared norm lies between `64/65` and `1`
times the raw reflected squared norm. The map neither creates nor removes
zero-norm vectors for these two reflected forms. See
[`BF4PhysicalCubeCompletedReflectedRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedRealization.lean).

**Connected operator result:** after the spin cutoff is removed, the actual conditional
operator `P` is self-adjoint and satisfies `0 <= <Px,x> <= <x,x>` on every
vector of the existing marginal-norm completion. The proof aligns both
insertions at the same finite cutoff using the existing adaptive sampler.

The constructive-real cubic identity now proves that this **same `P`** is
positive, self-adjoint and contractive for `E(x,y)=<x,Py>`. The same stationary
vacuum has E-norm one; its pairings, and the exact one-insertion-shifted
moments, are preserved. These are unconditional fixed-nome, finite-volume
results for `0<w<1`, using the constructed source-tail moduli. See
[`BF4PhysicalCutoffReflectedFormLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffReflectedFormLaws.lean).

The new completed root-sector map agrees with the conditional operator on
dense inputs; full intertwining remains open, as do geometric time and a strict gap. The construction
does not assume marginal completeness implies E-completeness; its scope is
the explicit-representative Cauchy quotient and the existing raw completion's
representative-family completeness.
No identification of the entire reducible carrier with the cube sector is
asserted; the vacuum-labelled root cylinder is not the constant stationary vacuum.

**Connected normalization result:** the all-spin raw cube form has its actual physical
cutoff-limit normalization. A single constructed `CReal` factor `lambda`
satisfies `normalized kernel = lambda * raw kernel`; its approximations are
exactly the reciprocals of the original finite partitions. The same identity
holds for every finite signed term list, including repeated states, after a
computed common cutoff. All limit constructions carry explicit moduli.

At the fixed anchor `w=1/400` and extent one, the checked partition ceiling
gives `64/65 <= lambda <= 1`, hence the corresponding two-sided comparison
of raw and normalized reflected squared norms. This is not a strict transfer
bound and is not a comparison with the marginal norm. See
[`BF4PhysicalCubeNormalizedKernelLimit.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNormalizedKernelLimit.lean).

**Connected finite-transfer result:** the actual finite BF4 conditional operator acts on the
completion of its own reflected joint form, with a unit fixed stationary
vacuum. The proof uses the elementary identity
`P - P^3 = (I-P)P(I-P) + 2 P(I-P)P`: a positive contraction for the marginal
form `D` also contracts `E(a,b) = D(a,Pb)`. The latter is exactly the original
partition-normalized OS joint form; cancellation of the positive partition
also proves contraction of the full raw OS quadratic.

The canonical comparison `J` keeps the same Cauchy representatives and moduli,
decreases norms, intertwines the two completed actions, and preserves vacuum
orthogonality. Its exact moment identity is
`<Jx, P_E^n Jy>_E = <x, P_D^(n+1) y>_D`. This holds at each finite cutoff;
it neither asserts an inverse for `J` nor identifies macro iterations with
geometric time. See
[`BF4PhysicalJointFormTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalJointFormTransfer.lean).

**Connected all-spin result:** the cube-sector raw reflected form has a
constructive GNS completion. Its states are exactly the union of the finite
canonical vacuum components for positive `w`; each state has a computed
admission cutoff. Explicit finite lists retain arbitrary signed rational
coefficients and repeated states. Their complete form is the original physical
boundary Gram at a computed common cutoff, not an assumed positive model.

The completed basis inner products equal the same raw physical kernel entries
at every cutoff beyond their saturation threshold. The vacuum-labelled root
has squared norm at least one and remains nonzero after completion. Finite
approximations and diagonal-limit representatives carry explicit moduli.
Completeness uses representative families with a supplied outer Cauchy modulus;
it does not select representatives from arbitrary quotient-valued sequences.
See [`BF4PhysicalCubeCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletion.lean).

The kernel underlying this construction, at slab extent one, has an exact
heat-weight/Boolean-overlap formula. For each half, its 48 production
links reduce to twelve SU(2) triangle tests and twelve boundary-zero tests;
the fixed part contributes eight corner triangles. The original weights and
boundary enumeration are retained, with no auxiliary multiplicity left.

If both endpoint label bounds are `R`, the raw kernel entry stops changing
exactly at every cutoff `K >= 2R`. A computed cutoff gives each pair an explicit
stable rational entry. Every finite quadratic form of this single stable
kernel is realized by the original physical OS Gram at a computed common
cutoff and is nonnegative for `w >= 0`.

The repository already constructs a cutoff-removed conditional transfer on
the **marginal-norm completion**, using explicit stationary-source-tail data;
see
[`BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean).
It fixes that completion's stationary vacuum and preserves vacuum orthogonality.
The remaining operator bridge is to the **reflected cube completion** above,
not a missing conditional-transfer construction everywhere. The common
normalization identifies forms, and the new one-step laws control the existing
conditional action in E. They do not yet identify the two reflected carriers
or geometric time. A transfer-fixed vacuum on the raw cube completion,
a uniform strict gap,
thermodynamic/spacing limits and continuum reconstruction remain open. The
nonzero raw vacuum-labelled root alone does not prove vacuum isolation.

**Exact sector:** at slab extent one, every positive rational weight parameter
`w` and every spin cutoff `K >= 1`, the canonical vacuum sector is **exactly**
the bounded six-face cube labellings with common parity. The constructive
inward-mate orbit stays in that sector and reaches vacuum within `K + 1`
genuine positive OS moves.

The key construction puts `|a-b|` on the boundary face between cube labels
`a` and `b`. All source, mate and fixed-link multiplicities are exactly one;
the complete production summand becomes an explicit positive heat-coefficient
product below the original OS kernel. Together with the earlier singleton
pins and parity constraints, this proves both directions of the classification.
The sector sets are nested in `K` and unchanged by positive `w`; their weights
are not. Every mate-invariant observable on the sector is constant.

The edge weights depend explicitly on the state and `w`. Successful-source
traffic coverage and a cutoff-independent norm-to-move estimate remain open;
positive connectivity does not establish either. Sector-set nesting alone
also does not establish norm or operator compatibility across cutoffs; the
new raw-entry saturation theorem supplies a separate, strictly weaker result.

The preceding quantitative result remains: the normalized sector OS flow carries at
least `448/5525` total traffic. Exact source-block Fubini connects it to the
proved `7/85` raw sector-demand fraction. Together with the same-object sector
energy embedding, this gives the positive central-face-parity Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost)` on the exact vacuum component.
These estimates are uniform in spin cutoff `K >= 1` at fixed coupling `1/400`
and slab extent one.
The missing reverse estimate must control every centered sector norm by move
energy with a positive cutoff-independent floor.

The latest checked path is already on that actual OS object.  Every successful
six-face inward-mate source gives a supported two-edge path in the normalized
symmetric OS joint kernel.  Its selected source traffic has total mass at
least `41/425`; exact production-target fibers have congestion bounded by
`globalInwardMateTransportCost`; and all complete sources that forget to the
same first OS edge now inject into distinct literal boundary--intertwiner
summands of that edge.  Consequently their **aggregate** first-edge traffic is
at most the actual OS joint capacity, without a volume- or cutoff-cardinality
loss.  The second edge is now complete too: exact production-target classes
partition all selected source traffic, those classes partition again by their
actual second OS edge, and the resulting loads sum exactly to the original
traffic.  Each second-edge load is bounded by
`globalInwardMateTransportCost` times its OS capacity.

For one concrete observable the answer is now positive.  The parity of
central lower face zero is reversed by every selected inward mate, and because
the intermediate parity is also Boolean, exactly one of the two path edges
changes it.  Lean proves without a triangle-inequality loss that the two
selected parity-gradient energies sum to the selected traffic and are
therefore at least `41/425`.  The complete first-edge energy is now embedded
in the full physical OS Dirichlet form: exact first-edge fibers make the
parity gradient constant, their aggregate traffic is bounded by the matching
OS capacity, and distinct realized edges inject into the Cartesian half-state
square.  The second-edge energy is now embedded as well.  Its exact
production-target and OS-edge partitions contribute no loss; only the already
proved `globalInwardMateTransportCost` congestion factor remains.  The active
contraction is now complete: the explicit cutoff-independent positive floor

```text
(41/425) / (1 + globalInwardMateTransportCost)
```

is bounded by the full physical OS Dirichlet energy of central-face parity at
every cutoff `K >= 1`.  Lean now centers that same Boolean observable with its
exact stationary mean, proves that deleting zero-marginal rows and columns
does not change its Dirichlet energy, and applies the exact
Dirichlet/transfer identity.  The centered vector has a strictly positive
physical norm and obeys the explicit one-observable form estimate

```text
|<f,Tf>| <= q <f,f>,
q = 1 - (1/2) * (41/425) / (1 + globalInwardMateTransportCost),
0 <= q < 1.
```

This is a real cutoff-uniform strict channel of the actual finite physical
transfer, but it is not an all-vector Poincare inequality.  For arbitrary
observables, the selected source-to-target oscillation is at most
`2 * (1 + globalInwardMateTransportCost)` times the actual physical OS
Dirichlet energy.  The proposed Type-level full-carrier coverage input is now
proved impossible.  The XOR parity of central-cube faces `0` and `39` is
unchanged by every simultaneous six-face inward mate, but after exact
stationary centering it has strictly positive physical norm already at cutoff
one (vacuum value zero, proved transverse-face value one).  Its selected
endpoint energy is exactly zero.  Hence
`GlobalInwardMateUniformEndpointCoverage` has no inhabitant.

This obstruction cleanly repoints the proof.  The full positive-row carrier
is already known to be reducible at cutoff two.  Lean now proves the first
sector bridge: a positive raw OS edge cannot leave the exact finite vacuum
component, so whenever an inward-mate source endpoint is in that component,
its common hub and mate endpoint are there too.  A finite-support Boolean
classifier now filters the global source enumeration exactly to those paths;
the resulting Type-level list is duplicate-free and its membership theorem is
an iff, not an assumed selector.  Restricting the partition-normalized traffic
to this list preserves nonnegativity and both proved OS edge-capacity bounds,
including the second-edge congestion factor. The global `41/425` demand floor
does not follow merely by restriction; the new sector bound is `7/85`.
The branch decomposition has now been localized
at the right level: over the exact finite list of full physical fields whose
lower restriction is in the vacuum component, all-target mass plus
first-stretched mass equals the genuine BF4 physical mass exactly.  The
bad-target support argument now needs no equality of boundary labels: the raw
OS kernel sums over those labels, so each field supplies its own positive
boundary summand.  A target preserving the reflected upper state therefore
has a two-edge path from the source lower state.  A target preserving the
lower state stays in the sector directly.  The resulting exact decomposition is
`sector physical mass = successful mass + one-sided bad mass + two-sided bad mass`.
The two-sided residual changes both half-states and is contained in the older
boundary-or-upper crossing list; no strict positive mass reduction is claimed.
The weighted localization is now proved too: every nonnegative function of the
actual lowered target passes through the inverse-fiber and target/root/size
sums, preserving the factor `384/425`.  Taking the exact sector indicator
bounds all internal bad mass by `384/425` of sector physical mass.  Exact
branch conservation then proves
`(41/425) * sector mass <= successful mass + escaping bad mass`.
The escaping mass counts only sources in the sector whose lowered targets
leave it.  Every such source is proved two-sided; two-sided targets that
remain inside the sector are already covered by the contraction.
That escaping mass is now absorbed. The physical degree-thirteen face
majorant has successive ratio at most `2/15625` at the anchor, hence its
all-cutoff one-face sum is at most `15625/15623`. Exact finite Fubini and
the corrected slab's embedding in the 96-face ambient corner box give
`Z <= (15625/15623)^96 <= 65/64`. Since the weight-one vacuum lies in the
sector, outside physical mass is at most `1/64`. Applying the same weighted
contraction to the complementary target event gives
`escaping bad mass <= (6/425) * sector mass`. Subtracting this from the
previous demand bound proves
`successful mass >= (7/85) * sector mass > 0`.
This is a fixed-volume, fixed-coupling result, not uniformity in beta or
lattice spacing.

The sector Dirichlet embedding is now proved without recounting any fibers.
Zero extension of a sector observable adds no physical energy: the exact
component has no crossing OS kernel entries, and zero-marginal rows vanish.
The full half-state energy of this extension equals the already-defined
canonical indexed sector energy. On every restricted path, the extension
agrees with the original observable at all three vertices. Thus the first
edge, second edge, and endpoint estimates restrict with their original
factors `1`, `globalInwardMateTransportCost`, and
`2(1 + globalInwardMateTransportCost)`.

The exact normalization handoff is now proved as well. The sector test is
constant within each fixed-physical source block, so filtering commutes with
the complete-source Fubini sum. The existing production source weights agree
termwise with the raw source weights, yielding
`sector total traffic = successful sector mass / Z`. Thus the traffic is at
least `7/85` times the partition-normalized sector-event mass and, using
`sector mass >= 1` and `Z <= 65/64`, at least `448/5525` absolutely.
The Boolean parity identity says its two path-edge energies sum exactly to
this traffic, giving the sector Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost) > 0`, without a factor-two
triangle-inequality loss. No source list, physical kernel, or normalization
has been changed.

The geometric test now has a checked answer at cutoff two. In
[`BF4PhysicalVacuumSectorInwardMateOrbits.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateOrbits.lean),
`targetLower_eq_mate_sourceLower` identifies the literal source endpoint map;
`cubeInwardOrbit_even_eq_parityCore` proves its all-cutoff parity reduction;
`cubeInwardOrbit_rootTime_eq_zero` gives an explicit vacuum-hitting time for
cube-supported common-parity states. On the canonical cutoff-two sector at
coupling `1/2`, `canonicalCutoffTwo_mate_invariant_constant` proves every
potential-mate invariant is constant. This is a geometric statement, not a
new weighted OS estimate at the anchor coupling.

The all-cutoff physical support implication is now proved in
[`BF4PhysicalHalfCubeSupport.lean`](lean/YMGap/Continuum/BF4PhysicalHalfCubeSupport.lean)
and
[`BF4PhysicalVacuumSectorCubeContainment.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorCubeContainment.lean).
`sharedBoundaryOfKernelNeZero` returns a witnessing nonzero boundary as data.
`vacuumSector_cubeSupportedCommonParity` propagates the singleton pins and
relative parities along the actual canonical component.
`vacuumSector_inwardOrbit_reaches_zero` applies the existing orbit formula to
every sector state; `vacuumSector_cubePairParity_zero` eliminates the
pair-parity obstruction there for every cutoff. These are fixed-geometry
support statements for arbitrary nonnegative `w`, not uniform spectral bounds.

Next: establish physical support and successful-source traffic on the required
potential moves, then prove quantitative norm-to-move coverage at arbitrary
cutoff. The converse inclusion of the entire common-parity cube family in
the canonical sector is not proved here. The orbit formula alone does not
establish weighted coverage or congestion bounds.
The Poincare compiler's algebra remains useful: a correctly formulated
sector-local coverage theorem with floor `kappa > 0` produces the rate shape

```text
q_all = 4(1 + globalInwardMateTransportCost)
        / (4(1 + globalInwardMateTransportCost) + kappa) < 1
```

uniformly for every cutoff `K >= 1`.  No such sector-local uniform coverage
theorem is presently claimed.

See
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean).
The two-level second-edge partition is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean).
The exact Boolean observable identity is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean).
The checked first-edge Dirichlet embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean).
The checked two-level second-edge embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean).
The resulting explicit positive Dirichlet floor is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean).
The stationary centering, positive-norm certificate, exact transfer identity,
and strict one-observable form rate are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean).
The arbitrary-observable two-edge estimate and exact all-vector coverage
frontier are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean).
The conditional coverage-to-uniform-Poincare contraction is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean).
The exact XOR counterexample refuting its full-carrier coverage input is in
[`BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean).
Positive raw-edge closure of the exact vacuum component and its application to
both inward-mate path edges are in
[`BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean).
The exact finite-support classifier and duplicate-free sector-local source list
are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean).
The restricted partition-normalized traffic and its inherited first- and
second-edge capacity bounds are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean).
The exact physical-field sector event and its localized good-plus-bad branch
conservation identity are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean).
The stronger support theorem, allowing arbitrary boundary changes whenever
either half-state is preserved, is in
[`BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean).
The exact three-way mass identity and residual containment are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean).
The contraction against any nonnegative physical target function is in
[`BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean).
Its sector specialization and exact escaping-mass demand bound are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean).
The sharp physical partition ceiling is in
[`BF4PhysicalAnchorPartitionCeiling.lean`](lean/YMGap/Continuum/BF4PhysicalAnchorPartitionCeiling.lean).
The complementary-event comparison, leakage absorption, and positive `7/85`
sector demand are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemand.lean).
The exact zero-extension identity for the canonical indexed sector is in
[`BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean).
The three unconditional restricted observable-energy comparisons are in
[`BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean).
The exact raw-to-normalized traffic identity, positive traffic floor, and
sector-parity Dirichlet consequence are in
[`BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean).

The current verified frontier joins a multiplicity-exact finite enumeration
of the root-first SU(2) cube source to a fixed-target contraction for every
certified first-stretched strand source.  Lean compiles the complete two-root
component union into three finite words:

- one connected rooted `Z^4` animal word in a carrier of size `625^n`;
- one exact physical strand-multiplicity word in a carrier of size `4^n`;
- one complete auxiliary-drop row word in a carrier of size at most `4096^n`.

At fixed root, peel size `n`, and lowered presented target, those words
reconstruct the source physical field and raw auxiliary assignment.  Thus any
explicit duplicate-free fixed-target source family has at most
`10240000^n` members.  Combining that injectivity with the exact per-source
anchor payment `anchorFaceCoefficient^n = (1/32000000)^n` gives the checked
finite-fiber estimate

```text
source fiber weight <= (8/25)^n * target weight.
```

See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean),
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean),
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean).

The classifier domain is now also a literal duplicate-free heterogeneous
product over the twelve cube incidences.  SU(2) fusion-path permutation
invariance proves that every root-first local fiber has the same cardinality
as its production-order fiber.  Hence the complete function-valued source
enumeration, and its injective target-or-first-stretched image, have exactly
`cubeInwardMateSourceBoundaryProduct K physical` members.

The target and first-stretched branches are now extracted as separate
duplicate-free lists whose lengths add back to the exact production
cube-boundary multiplicity.  The off-cube completion no longer starts from a
full background that would later discard twelve cube coordinates.  Instead,
it explicitly filters the complete slab-link list to the complement of the
twelve cube links, enumerates only those production fibers, and combines them
piecewise with the certified root-first cube data.  Cube and off-cube lookup
laws prove that every coordinate comes from exactly its intended source.

The remaining immediate bridge is to enumerate the Cartesian product of the
first-stretched list and this off-cube list injectively, partition the result
by common lowered target, root, and peel size, and sum those fibers.  The
Cartesian family itself is now explicit, duplicate-free, and has exact length

```text
first-stretched cube count * off-cube production multiplicity.
```

Every member canonically compiles to a complete presented source and its raw
auxiliary payload.  That compiler is now proved injective on the enumerated
family: equality on cube coordinates recovers the certified classifier input,
while equality off the cube reconstructs the complement assignment.  The
resulting physical/raw source list remains duplicate-free.  The active edge is
now to attach each member's deterministic lowered target, root, and peel size,
then partition this list into the fixed fibers consumed by the existing
`(8/25)^n` contraction theorem.  That attachment is now explicit and
duplicate-free: every entry retains its upstream source as an injective key,
projects the existing flat inverse record, and has peel size at least two.
Reapplying the older defensive cube override is also proved to leave the raw
complete source unchanged.  The live edge is the actual dependent target/root/
size partition and its fixed-fiber witness compiler.  The lossless decidable
partition key is now proved: it records the root, size, lowered physical word,
every local face-order word, and every local lowered-auxiliary word.  Equal
keys reconstruct literal equality of the lowered physical function and
heterogeneous equality of the dependent presented assignment.  The live edge
was therefore the realized representative fibers and their
`PresentedAdaptiveRemovalWitness` compiler.  That compiler is now checked as
well: each realized fiber is duplicate-free, has size at most
`10240000^n`, and its complete anchor weight is at most `(8/25)^n` times
the representative's lowered-target weight.  The live edge is the exact
representative-fiber Fubini sum followed by contraction of the resulting
distinct lowered-target weights against the pure mate product.  The exact
Fubini step is now checked and the full first-stretched source weight is
bounded by the strict-rate-weighted sum of its realized lowered targets.  The
live mathematical edge is the target-side congestion/injection that contracts
this distinct target sum against the pure mate product.
The theorem does **not** yet give a physical transfer minorization, a
posterior-variance fraction, an OS transfer gap, or a continuum result.

Earlier in the same causal chain, the Casimir/heat payment for an inward mate
at the physical nome `w = 1/2` established that a parity-uniform six-face cube
has a non-vacuum even source heat product at most `64` times its inward mate's
heat product, while an odd source is at most `1/4096` times its inward mate.

These are
`sixHeatProduct_evenInwardMate_le_sixtyFour` and
`sixHeatProduct_oddInwardMate_le_oneOver4096` in
[`BF4PhysicalVacuumSectorInwardMateHeatBound.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateHeatBound.lean).

The local SU(2) fusion debt is now also exact and kernel-checked. Lowering two
positive incident labels preserves their Clebsch--Gordan ladder except for
its stretched top channel. At the production link-multiplicity level, every
source path is bounded by the inward-mate path count plus one explicit
stretched-channel continuation. See
[`BF4PhysicalVacuumSectorInwardMateFusionSupport.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionSupport.lean).

The local comparison now also transports across arbitrary physical incident
spin orderings, provided the two geometric permutation witnesses are supplied.
This is
`explicitValenceMultiplicity_physical_inwardMate_of_permutations` in
[`BF4PhysicalVacuumSectorInwardMateFusionReordering.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionReordering.lean).
The generic finite-box incidence step is now closed as well:
`incidentPhysicalSpinsTwoFacePermutations` constructively moves any two
distinct incident plaquette IDs to the front of the source and mate words with
one shared residual word, and
`incidentPhysicalSpinsTwoFaceInwardMateLeAddStretched` immediately feeds
those witnesses into the production multiplicity inequality. See
[`BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean).

The cube-specific geometry is now closed too.  The twelve-entry production
table is compiled into exact corrected-slab numerical incidence: at every
cube-boundary link the two recorded selected face IDs occur, are distinct, and
exhaust the selected six-face support.  Thus the global six-face mate restricts
to the proved local two-face mate, yielding the actual corrected-slab
multiplicity bound with one explicit stretched continuation.  See
[`BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean).

Those twelve local certificates now form one explicit global debt profile.
Lean proves that every link outside the cube boundary is unchanged and that
the boundary products obey
`product(source) <= product(mate + stretchedDebt)`.  See
[`BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean).
This deliberately does not absorb the debts independently.

That finite product is now expanded exactly over Boolean words aligned with
the twelve attached links.  The all-target word is the pure mate product; all
nonempty stretched words sum to the named
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean).

Every summand in that remainder now has a canonical constructive root.  Lean
computes the first stretched choice, proves its index lies in the attached
twelve-link incidence list, returns the corresponding geometric incidence as
data, and proves the root bit is `true`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean).

The natural-number remainder is no longer opaque cardinality either.  Each
stretched local factor is the length of a literal accepted SU(2) auxiliary
fiber; Boolean words choose target or stretched fibers link by link; and the
flattened finite carrier has length exactly
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean).

The raw expansion has now been sharpened at its mathematical source.  The
SU(2) ladder proof shows that if either changed face label is zero, every
source channel survives and the additive debt is exactly zero.  The active
remainder therefore retains a stretched fiber only when both incident cube
faces are positive; it again has an exact finite-carrier cardinality theorem.
See
[`BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean).

Every member of that active carrier now retains its assignment-membership
certificate, its first active position, the actual auxiliary labelling stored
there, and proofs that both incident physical face labels are positive.  Thus
the root required by the strand compiler is Type-level data rather than a
propositionally extracted witness.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean).
The two positive root faces are now also realized as distinct literal
slot-zero strand-copy vertices on their common recorded link; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean).
For the stretched SU(2) vertex itself, the canonical resolution is now exact:
no strand joins the two input legs, while their strands occupy two disjoint
segments of the summed internal leg.  See
[`SU2StretchedTrivalentStrandContinuation.lean`](lean/YMGap/Continuum/SU2StretchedTrivalentStrandContinuation.lean).
The cube-root specialization now sends both literal face copies through those
canonical mates to distinct summed-channel ports and certifies the stored
auxiliary on the exact collapsed word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean).
The resulting collapsed auxiliary can now be lifted constructively back across
the stretched vertex.  For every source word of length at most six,
`stretchedFusionWitnessLift_mem` inserts the forced first channel, shifts the
remaining internal coordinates, and proves that the resulting auxiliary is
accepted on the ordered source word; see
[`SU2StretchedFusionWitnessLift.lean`](lean/YMGap/Continuum/SU2StretchedFusionWitnessLift.lean).
That compiler is now specialized to every active cube-root carrier:
`rootSourceAuxiliary_mem_orderedSourceSpins` provides the literal accepted
source auxiliary, and `rootProductionSpins_perm_orderedSourceSpins` retains
the exact permutation from the physical production order; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean).
The corresponding root-first order of literal plaquette IDs is now retained
as data as well.  It is duplicate-free, permutes the production incidence
list, and maps exactly to the accepted ordered spin word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean).
The canonical ordered-chain termination and fixed-point-free terminal mate now
work for any such certified face presentation.  The generic compiler reindexes
every terminal to a literal incident plaquette and proves its mate lies on a
different face; see
[`CompactDualSlabOrderedLinkPhysicalStrandPairing.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkPhysicalStrandPairing.lean).
The one-element physical half-edge fiber now gives a constructive terminal at
any specified face position and strand slot.  At the active cube root this
produces two literal slot-zero terminals whose occurrences are exactly the two
previously named positive root copies; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean).
Those selected terminals are now identified as full dependent ports at the
first canonical trivalent vertex, not merely by face ID.  The first channel is
proved to carry exactly the SU(2) stretched spin sum; its strand counts are
`ab = 0`, `bc = right`, and `ca = left`.  Consequently the two selected local
mates both land on the third leg but in distinct slots (`right` and `0`).  See
[`CanonicalLinkFirstVertexPorts.lean`](lean/YMGap/Continuum/CanonicalLinkFirstVertexPorts.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean).
The outgoing channel is now constructively classified as physical at valence
three or genuinely internal at valence four through six.  Both root strands
are fed to the exact stop-or-same-slot-advance compiler; their complete paths
to physical endpoints are retained as data, and those endpoints are proved
distinct.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean).
Those endpoint terminals are now reindexed to the presentation-independent
global `(faceId, slot)` carrier.  Each root copy is proved to be the exact
source of a global strand edge, and the two retained path endpoints remain
distinct as literal global copies.  See
[`CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean).
The global edge compiler now also accepts a different certified face order and
fusion witness at each link.  It enumerates every local physical terminal,
forgets every endpoint to the common global carrier, and concatenates the
result into one heterogeneous edge list.  Replacing the root entry of any
explicit complete background assignment by the actual root-first witness puts
both retained root edges literally in that list.  See
[`CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean).
An ordinary accepted source assignment now embeds canonically into this
presented interface.  More generally, a rooted component of any heterogeneous
presented graph pulls back to exact partner closure at each ordered link.  For
the active debt root, Lean constructs the two rooted components generated by
the left and right stretched-channel strands and takes their Boolean union.
That union contains both literal root copies and is closed across every edge,
without asserting that the two components coincide.  See
[`CompactDualSlabPresentedFaceStrandSeedComponent.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandSeedComponent.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean).
That ordered partner closure now compiles all the way through the existing
Kirchhoff strand-removal theorem.  At every link, the canonical edge drop is
proved equal to the global selected-copy count on the literal face occupying
that ordered position.  Consequently the two-root union constructs one common
lowered physical field and a complete accepted heterogeneous auxiliary
assignment over it; both distinct root-face labels decrease strictly.  See
[`CompactDualSlabPresentedFaceStrandComponentDrop.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDrop.lean).

The source-side local decomposition is now witness-faithful rather than only
an inequality of natural-number dimensions.  For any root-first ordered word
through valence six, Lean reads the actual first SU(2) channel of an accepted
source witness.  If it survives the inward mate, the same auxiliary is
accepted in the mate fiber.  Otherwise Lean deletes the unique stretched
first vertex, retains the resulting accepted collapsed witness and both
positive-spin proofs, and proves that reinsertion recovers the source exactly.
The resulting `inwardMateFusionWitnessPartition` is injective.  See
[`SU2InwardMateFusionWitnessPartition.lean`](lean/YMGap/Continuum/SU2InwardMateFusionWitnessPartition.lean).

That abstract partition is now specialized to every literal cube-boundary
link.  One certified face order exposes the two incident cube faces first; its
residual literal faces are proved unchanged by the global six-face mate.  Lean
therefore maps the actual ordered source fiber injectively into either the
actual ordered mated fiber or an accepted collapsed stretched witness, and it
packages every surviving target as a presented mated-link witness.  Exact
recovery still returns the original auxiliary.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean).

The dependent twelve-link product is now constructed too.  A complete source
is a function whose coordinate type is the accepted root-first fiber of that
literal incidence.  Lean classifies all coordinates, recovers all original
auxiliaries pointwise, proves the complete classifier injective, and packages
the original tuple as one accepted presented cube family.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean).

That product now has a constructive global dichotomy.  A structural scan either
returns all twelve accepted mated witnesses or the first stretched incidence
with its actual positive two-face debt witness.  Forgetting the branch
reconstructs the complete classified assignment, so the source-to-branch map
remains injective.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean).

The classifier's source-image invariant is now explicit rather than implicit
in its construction.  Every local output retains proof that its exact decoder
is accepted in the source fiber; the dependent product reconstructs a common
presented cube source.  The strengthened first-stretched branch keeps this
entire certified product and proves that its root output is exactly the stored
debt witness.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean).

The certified cube family now extends to a complete slab presentation whenever
an explicit accepted full-slab background for the same physical field is
supplied.  A constructive finite lookup finds the unique recorded incidence
of each cube link, overwrites exactly those twelve entries with the certified
source witnesses, and leaves all off-cube entries unchanged.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean).

At the certified first-stretched incidence, the retained positivity data now
constructs slot-zero terminals on the first two faces of that same root-first
witness.  Their terminal-pair edges have exactly the two literal cube-face
copies as sources, and both edges are proved members of the single completed
presented slab graph.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean).

Those two edges now seed a complete accepted peel.  Lean takes the Boolean
union of their constructive rooted components, proves it closed under the
actual partner at every independently presented link, and compiles the common
selection to a lowered physical field plus a complete accepted presented
assignment.  Both root-face labels decrease strictly; no connectivity claim
between the two roots is assumed.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean).

That accepted drop now has an exact physical serialization and pointwise
weight payment.  Every endpoint of the heterogeneous presented graph is
proved to lie on a displayed physical face; the selected-copy multiplicities
form a legal repeated-face peel with an exact physical left inverse; and the
certified two-root word has length at least two.  At the production anchor,
the actual completed source entry is bounded by one
`anchorFaceCoefficient` factor for every word letter.  See
[`CompactDualSlabPresentedFaceStrandComponentWeight.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentWeight.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean).

The auxiliary drop is now serialized as well.  The lowered target retains each
certified face order, so the finite code pays no extra order coordinate.  Its
physical word plus link-local internal-drop words reconstruct the complete
source `(physical, raw auxiliary)` entry exactly, and every local word has
width at most three independently of cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDropCode.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean).

Zero internal-drop rows can now be erased and recovered exactly.  Every
retained row is charged injectively to a selected physical strand copy and one
of its four boundary links, so there are at most `4 * peelSize` nonzero rows.
More sharply, the complete volume-indexed row table inhabits a link-adaptive
Cartesian carrier: local conservation bounds every entry by the selected
physical mass incident on that link, all widths are at most three, and the
total incident mass is exactly `4 * peelSize`.  Consequently the auxiliary
carrier has size at most `4096^peelSize`, uniformly in slab volume and spin
cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean),
[`CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean),
and
[`CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean).

The physical geometry, multiplicity, and auxiliary inverse are now joined in
one adaptive code.  Its fixed-target injectivity and weighted fiber contraction
are checked, including component overlap without double counting.  What is
still open is the global regrouping: construct the actual finite enumeration
of certified first-stretched routes, partition it by the common lowered target,
root, and peel size, and sum those fibers into a cutoff-independent multiple
of the pure mate product.  The older coarse mixed target/debt Cartesian carrier
still does not itself provide a common accepted source presentation and is not
used as one.  Closing this regrouping would feed a genuine physical
mate-transition floor and then a rooted-subtree Hardy--Poincare or posterior
conditional-variance estimate.

An earlier plan tried to bound the whole new-cutoff self-return trace by a
small constant. Exact exploratory computation found that plan false already
at cutoff four: a single state has self-return about `0.71428`, and six
symmetric copies make the positive trace exceed four. This computation is a
route-selection diagnostic only; no floating-point value enters a theorem.

For the detailed live dependency map, see [`work_plan.md`](work_plan.md).
For the source-based group audit, see
[`audits/AUDIT-GROUP-DEPENDENCE.md`](audits/AUDIT-GROUP-DEPENDENCE.md). That
audit found that the strand machinery is hard-coded to the SU(2)
Clebsch--Gordan rule and that no source dependency bridge currently connects
the component chain to the generic `singleStep` obligation. Accordingly, this
README makes no claim that group dependence is closed.

## Trust and constructivity rules

The Lean development is intentionally stricter than ordinary Lean code:

- no Mathlib dependencies;
- no `Classical.choice`, excluded-middle shortcut, or `native_decide` in
  load-bearing proofs;
- constructive reals carry explicit Cauchy moduli;
- witness-bearing existence claims use data-bearing structures or sigma
  types;
- load-bearing declarations are inspected with `#print axioms`; the permitted
  project gate is `propext` and `Quot.sound` only;
- unproved obligations and conditional interfaces are recorded in
  [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md), rather than being described
  as completed physics.

Python and Rust may perform expensive searches or generate compact exact
certificates. They are **untrusted producers**: Lean must parse the resulting
finite data and independently check every semantic condition and inequality.

Read [`lean/AGENTS.md`](lean/AGENTS.md) before modifying any Lean file.

## Repository guide

| Path | Role |
| --- | --- |
| [`lean/`](lean/) | Lean 4 formalization and constructivity/axiom gates |
| [`lean/YMGap.lean`](lean/YMGap.lean) | Root import aggregator |
| [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md) | Open obligations and milestone evidence |
| [`work_plan.md`](work_plan.md) | Current causal roadmap and status |
| [`docs/outline.md`](docs/outline.md) | Technical specification |
| [`docs/context.md`](docs/context.md) | Mathematical motivation and constructive rationale |
| [`audits/`](audits/) | Read-only source audits of important claim boundaries |
| [`computations/`](computations/) | Untrusted Python/Rust exploration and certificate generation |
| [`tests/`](tests/) | Tests for computational tooling |
| [`formal/`](formal/) | Human-readable LaTeX development |
| [`visualizations/`](visualizations/) | Generated diagrams and exploratory figures |

## Building safely

Lean is pinned by [`lean/lean-toolchain`](lean/lean-toolchain). Builds must use
the monitored launcher; bare `lake build` and bare `lake env lean` bypass the
repository's crash safeguards.

```bash
# Full monitored Lean build
make lean-build

# Narrow target (preferred while developing)
python3 scripts/safe_lean_build.py --jobs 1 -- +YMGap.Continuum.ModuleName:olean

# Check one source and emit only its importable olean (parent directory exists)
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ModuleName.olean

# Monitored axiom audit
make lean-audit
```

See [`docs/lean-build-safety.md`](docs/lean-build-safety.md) for memory and
worker limits.

The auxiliary Python tools require Python 3.11 or newer:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
make test
make lint
```

Other common targets are `make figures` and `make paper` (the latter requires
a working LaTeX installation with `latexmk`).

## How to evaluate a claim in this repository

Check all four of the following:

1. the exact theorem statement and its parameter range;
2. its printed axiom dependencies;
3. whether its hypotheses have concrete inhabitants, rather than only a
   conditional compiler;
4. whether the next bridge in [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md)
   is still open.

A finite-cutoff theorem, a fixed-coupling clustering estimate, or a compiler
of the form “if certificate `C`, then gap” is valuable progress, but none is
by itself a continuum Yang--Mills mass-gap theorem.
