# Positive time anchoring in the original physical bond completion

The existing normalized Wilson-square excitation now has explicit positive-time
rows in the original physical bond completion, together with a quadratic
increment estimate uniform in nome and width. These checked constructions
supply continuity control for an anchored integer-grid route. They do not
produce a nonzero continuum limit. The unchanged Clay target remains OPEN.

## The original transfer has a quadratic increment bound

Let T(n) and B be the EXISTING all-nome completed transfer and inner form,
and D=I-T(1). The actual finite sum telescopes as

    sum(p=0,...,j-1) T(p)T(n)Dx = T(n)x-T(n+j)x.

The existing defect-tail estimate is
`timeDefect_bound`, `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:122`:

    B(T(n)Dx,T(n)Dx) <= B(x,x)/(n+1)^2.

Contraction controls every summand by this same norm. The existing finite
sum norm bound supplies the factor j^2. Symmetry of squared distance gives

    distance(T(n+j)x,T(n)x) <= (j/(n+1))^2 * B(x,x).

Here distance is SQUARED norm, not norm. This holds for every actual x,
integer n,j including zero, every strict nome 0<w<1 and every width.
It is polynomial smoothing, not an exponential decay or mass-gap estimate.

For the literal constructed dyadic unit excitation u, B(u,u)=1. The
assigned geometric parameters obey side(k)*spacing(k)=1. At n>=side(k),
1/(n+1)<=spacing(k), so

    distance(T(n+j)u,T(n)u) <= (j*spacing(k))^2.

The computed radius delta(epsilon)=min(epsilon,1) is positive for epsilon>0.
If j*spacing(k)<=delta(epsilon), the squared distance is at most epsilon.
The radius depends on epsilon alone, not nome, width, scale or lag. There is
no comparison of different completed carriers or different unit states.
Geometric spacing has not been identified with physical YM lattice spacing.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `positiveLag_increment_sum` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:55` | Exact original signed telescope |
| `positiveLag_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:67` | Quadratic squared-distance bound |
| `invSucc_le_spacing` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:101` | Geometric reciprocal comparison |
| `dyadicUnit_positiveLag_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:124` | Literal original unit-state instance |
| `dyadicUnit_positiveLag_spacing_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:133` | Uniform assigned-time bound |
| `incrementRadius`, `incrementRadius_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:143`, `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:145` | Computed positive radius |
| `dyadicUnit_positiveLag_increment_small` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean:175` | Uniform integer-grid small increment |

## Anchored states inhabit the existing physical bond completion

At scale k define the value of the anchored bond point x_i to be

    bondValue(x_i) = T(side(k)+i)u.

This is not a new abstract carrier or an assumed physical realization.
`unitRepresentative` returns the actual original Cauchy rows of u, including
its computed real normalizer and QCauchy data. Advancing these rows by
side(k)+i-1 gives an explicit preimage. Because side(k)>=1, the existing
`TimeSector.fromTime` constructor returns exactly T(side(k)+i)u with its
original time-range witness. The existing `fromSectorRep` then computes
finite physical bond-source rows and their own all-tail modulus.
Its exact limit pin is `fromSectorRep_limit` at
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSCompletion.lean:260`.

The supplied preimage matters: applying the direct bond image to T(m)u
would introduce its sqrt(T) factor. The existing inverse range realization
used here instead gives exactly T(m)u. No inverse transfer, arbitrary
representative selection, new completion or kernel deletion is used.

The same actual unit response R gives every Gram entry:

    B_bond(x_i,x_j) = R(2*side(k)+i+j).

In particular, the squared anchor norm is R(2*side(k)). Its original vacuum is
orthogonal to x_i, and the existing physical positive integer-time action
sends x_i to x_(i+j) for j>0. Transporting the quadratic increment bound
through the exact original bond-value isometry requires no extra factor.
It includes j=0 and gives the same positive tolerance radius on these actual
bond points, uniformly in nome and width at assigned geometric time.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `unitRepresentative`, `unitRepresentative_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:64`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:70` | Explicit rows of SAME u |
| `anchoredPreimage`, `anchoredSector`, `anchoredSector_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:74`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:79`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:83` | Supplied exact T(1) preimage and range witness |
| `anchoredBondRows`, `anchoredBondExcitation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:91`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:95` | Original finite physical bond rows and point |
| `anchoredBond_value`, `anchoredBond_pairing` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:100`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:106` | Exact value and SAME response Gram pins |
| `anchoredBond_vacuum_orthogonal`, `anchoredBond_time` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:114`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:121` | Original vacuum and time action |
| `anchoredBond_increment_bound`, `anchoredBond_spacing_bound`, `anchoredBond_increment_small` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:129`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:139`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:148` | Actual bond-distance estimates and radius |
| `anchoredBond_norm_floor`, `anchoredBond_norm_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:158`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:169` | Positive norm ONLY at fixed parameters |

## Remaining forward backward join

The anchored integer-grid continuity estimate does not require continuity
of the raw changing-family unit states at time zero. It DOES require the
original norm-one preimages; renormalizing a possibly vanishing anchor would
not preserve this uniform constant without a proved usable norm floor.
The finite floor r^(2*side+2*i)>0 proves fixed-parameter nonzero norm, not a
positive all-scale lower bound or a nonzero limiting state.

The retained backward criterion is already exact at m=2*side:
m*e(u)-C_m(u)<=1-gamma iff gamma<=R(m), from
`dyadicUnit_response_lower_iff` at
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:210`.
A useful common positive gamma on a justified changing family is still
OPEN. The original signed overlap route remains available; no source
independence or favorable alignment is inferred from the recurrence.

Cross-scale scalar/joint-functional convergence with explicit moduli,
nonzero limiting anchor norm and an identified common continuum carrier
remain OPEN. These results do not instantiate the canonical reflected
half-space structure or its essential-surjectivity requirement:
`PositiveTimeOSRoot` at `lean/YMGap/Continuum/CanonicalOSRoot.lean:268`.
They do not identify renormalized local YM fields, physical time/mass,
full SAME QFT axioms or every compact simple gauge group. No real-time
continuum semigroup is constructed from this integer-grid bound alone.
No exact canonical chart node is closed by these supporting results.

## Verification boundary

Both final focused checks passed with one monitored worker and an explicit
20-GiB ceiling. Fresh process, memory-pressure and swap checks preceded
each launch. The eight increment gates and sixteen anchor gates use only
allowed propext and Quot.sound; the radius and its positivity are axiom-free.
Accepted logs have no errors or warnings. Independent Sol mathematical
review and Luna evidence review passed. No new sorry, axiom, classical
shortcut, analytic premise or weakened field is introduced.
Root imports both modules, but root/tree, broad audit/guard and progress
metric were NOT run. CI and the canonical chart remain unchanged.

The first increment check is REJECTED: two uses of nonexistent Q'.le_refl
were repaired by the existing reflexive eqv order fact. The first anchor
check is REJECTED: local notation projected a seminorm through a parameter
macro; spelling out its existing setoid repaired elaboration. The second
anchor check passed its initial thirteen gates; the final third check is
the accepted expanded sixteen-gate target. Statements, guards and resource
limits were not weakened to repair either rejected check.

Accepted SHA256 evidence:

| Artifact | SHA256 |
| --- | --- |
| `lean/YMGap/Continuum/BF4WilsonAllNomePositiveLagIncrement.lean` | `dfbe9ab4ff97884d694b354727290905a411d076ca080215876a7813d88f4948` |
| `/tmp/ym-positive-lag-increment-20261002-second.log` | `3b813b863a6cd9f0d666188bc560c45d34add45828f2a77c503c320f8a840c64` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean` | `d52e919693ef6ce2fcc2813e0d9632405517a695941f5d9e38ed77147c7444af` |
| `/tmp/ym-dyadic-bond-anchor-20261002-third.log` | `3f0289f1cb08721a2e626ed592bf75c5f79efa36af499ff2cc0b27b6163e5bec` |
