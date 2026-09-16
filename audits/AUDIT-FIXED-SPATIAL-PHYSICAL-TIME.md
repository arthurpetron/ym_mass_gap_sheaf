# Original physical time: contraction and the reflected Cauchy carrier

Date: 2026-09-16. Classification: PROGRESS after `200e12b`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian mass gap for
every compact simple group, on the SAME theory, within the constructive
axiom gate. This checkpoint concerns the selected fixed-width SU(2) action,
not completion of that target.

## Mathematical result

Fix rational 0<w<1, spatial width and retained heat cutoff
K=headCutoff(w)+stage. Let B be the already constructed intrinsic reflected
pairing on finite signed spatial-probe spans. Let S^n increment every
natural-number distance from the reflection plane by n. The new results are

    B(SX,Y) = B(X,SY),
    B(S^r X,S^s Y) = B(X,S^(r+s)Y),
    0 <= B(S^n X,S^n X) <= B(X,X),
    0 <= B(X,S^(2n)X).

Equalities of the constructed CReals mean CReal.Equiv, not equality of their
approximation indices. All physical-face guards are retained. This is the
actual physical advance of the original observables, not chart enlargement
or a Markov/heat-bath update.

The squared distance d2(X,Y)=B(X-Y,X-Y) supplies an actual SquaredSeminorm.
Physical advance is nonexpansive for this distance and therefore acts on
the existing quotient of explicit-modulus Cauchy data. The induced maps
satisfy the time-zero and addition laws, agree exactly with literal advance
on embedded presentations, and preserve every supplied Cauchy modulus.
The original unit, with B(1,1)=1, gives a fixed element distinct from embedded
zero. The completed inner product and Hilbert-space laws are NOT supplied
by this checkpoint.

## Causal argument: expansion and contraction

Expansion exposes three independent inputs on the SAME pairing: exact
time balance, actual reflection positivity, and a computed lag-independent
scalar cap. Contraction composes them into the nonexpansive bound and then
uses the existing choice-free Cauchy construction.

1. Literal advance preserves physical faces and commutes with signed span
   addition/scaling. The mixed-product time-balance pin is proved in a
   common enclosing window, using supported padded congruence and the
   original right/left padding laws. Iteration gives the sum-of-times law.
2. Relabeling times changes exponent lists but leaves the RAW coefficient
   list unchanged. Its polynomial cap is therefore invariant. The actual
   normalized full-window bracket bounds the reflected ratio, and its
   existing time limit inherits that bound. Time-erased polynomials are
   used only to compute the coefficient cap; their VALUES are not identified
   with the original observable or expectation.
3. Set a_n=B(S^n X,S^n X). Exact time balance identifies a_n with
   B(X,S^(2n)X). RP of X-S^(2n)X gives 2*a_n<=a_0+a_(2n).
   The actual scalar cap bounds every a_n. The existing bounded-midpoint
   doubling theorem now proves a_n<=a_0, without division by the norm,
   a strict-gap hypothesis, or an ordinary-L2 substitute.
4. Apply the same bound to signed differences. This gives genuine
   squared-distance nonexpansiveness and preservation of null presentations.
   Site RP gives positivity at EVEN physical advances; positivity of a
   one-step operator is not inferred.
5. Signed-difference algebra, symmetry, positivity and radical annihilation
   prove all laws of the squared-seminorm instance. In particular,
   its triangle field is d2(X,Z)<=2*d2(X,Y)+2*d2(Y,Z), and null replacement
   uses the original reflected pairing in both arguments.
6. Apply the nonexpansive map termwise to each Cauchy representative. Its
   stored modulus is unchanged, as is the modulus for close representatives.
   The existing quotient construction descends the map. Literal time laws
   give the semigroup laws and the embedded-original-presentation identity.
7. The literal unit is fixed. Equality of embedded constants in this quotient
   forces their original distance to be zero. B(1,1)=1 then distinguishes
   the completed unit from embedded zero, without asserting an excitation
   beyond the unit or an isolated vacuum sector.

## Declaration evidence

All module paths in the following table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `pairing_unit_unit`, `unit_not_null` | `BF4ExactSlabFixedSpatialIntrinsicUnit.lean:42`, `:47` | Original unit normalization and non-nullity. |
| `pairing_difference_left`, `pairing_difference_right` | `BF4ExactSlabFixedSpatialIntrinsicDifference.lean:54`, `:63` | Signed subtraction in the same pairing. |
| `pairing_midpoint_bound` | `BF4ExactSlabFixedSpatialIntrinsicDifference.lean:129` | Actual RP of a difference gives the midpoint inequality. |
| `advanceSpan`, `advanceSpan_physical` | `BF4ExactSlabFixedSpatialPhysicalTimeShift.lean:52`, `:106` | Literal advance and preserved physical-face guard. |
| `mixedProduct_time_balance` | `BF4ExactSlabFixedSpatialPhysicalTimeShift.lean:191` | Original polynomial translation/padding identity. |
| `pairing_time_balance`, `pairing_time_sum` | `BF4ExactSlabFixedSpatialPhysicalTimeShift.lean:209`, `:245` | Actual same-form time balance and its iteration. |
| `coefficients_sourceSpan` | `BF4ExactSlabFixedSpatialUniformProbeCap.lean:149` | Exact raw coefficient ledger under time erasure. |
| `uniformCap`, `uniformCap_relabel` | `BF4ExactSlabFixedSpatialUniformProbeCap.lean:173`, `:180` | Computed ceiling and explicit relabel invariance. |
| `windowRatio_bounds` | `BF4ExactSlabFixedSpatialUniformProbeCap.lean:201` | Bound for the actual normalized full-window ratio. |
| `pairing_bounds`, `pairing_relabel_bounds` | `BF4ExactSlabFixedSpatialUniformProbeCap.lean:245`, `:257` | Same returned CReal bounds, uniform over both time relabelings. |
| `timeNorm_bounded`, `timeNorm_midpoint` | `BF4ExactSlabFixedSpatialPhysicalTimeContraction.lean:48`, `:55` | Actual hypotheses for bounded midpoint doubling. |
| `timeNorm_le_anchor`, `pairing_advance_contraction` | `BF4ExactSlabFixedSpatialPhysicalTimeContraction.lean:70`, `:79` | Contraction with constant one. |
| `difference_contraction`, `advance_preserves_radical` | `BF4ExactSlabFixedSpatialPhysicalTimeContraction.lean:86`, `:95` | Same reflected-distance bound and null descent. |
| `pairing_even_nonnegative`, `pairing_unit_invariant` | `BF4ExactSlabFixedSpatialPhysicalTimeContraction.lean:105`, `:117` | Even-time positivity and unit-pairing stationarity. |
| `distSq_triangle`, `distSq_null_congr`, `seminorm` | `BF4ExactSlabFixedSpatialIntrinsicSeminorm.lean:121`, `:169`, `:184` | Actual squared triangle/null congruence and proved squared-seminorm instance. |
| `timeNonexpansive`, `timeSemigroup` | `BF4ExactSlabFixedSpatialCompletedPhysicalTime.lean:49`, `:55` | Actual original-distance nonexpansive semigroup. |
| `Completion`, `completedTime` | `BF4ExactSlabFixedSpatialCompletedPhysicalTime.lean:71`, `:78` | Choice-free Cauchy quotient and induced time maps. |
| `completedTime_zero`, `completedTime_add` | `BF4ExactSlabFixedSpatialCompletedPhysicalTime.lean:82`, `:87` | Proved semigroup laws on this carrier. |
| `completedTime_embedSpan`, `time_cauchy_modulus` | `BF4ExactSlabFixedSpatialCompletedPhysicalTime.lean:94`, `:100` | Original-observable pin and exact modulus preservation. |
| `completedUnit_fixed`, `completedUnit_ne_zero` | `BF4ExactSlabFixedSpatialCompletedPhysicalTime.lean:116`, `:144` | Fixed unit distinct from embedded zero. |

The generic bounded-midpoint consumer is
`bounded_midpointDoubling_leEv_anchor` at
`lean/YMGap/Continuum/BoundedMidpointDoublingEventual.lean:55`.

## Parameters, operator and open boundary

`uniformCap width xs ys` depends on width and the signed, ordered spatial
face-word presentations. It does not depend on physical lags, enclosing
window, boundary buffers, nome or late cutoff. `pairing_relabel_bounds`
explicitly quantifies both relabelings, 0<w<1 and cutoff stage. The finite
ratio theorem explicitly requires a valid late cutoff. This is a scalar
ceiling, not a norm-relative strict gap.

The proved norm contraction has constant ONE, for each of the named fixed
parameters. It is not a q<1 estimate on the vacuum complement and yields
no positive Hamiltonian mass gap. A beta-independent non-strict contraction
does not assert a beta-uniform mass gap. No physical lattice-spacing
calibration, spectral logarithm or passage to a Hamiltonian occurs here.

The map advances original physical time and is not a link-variable sampling
dynamics. Nevertheless, this checkpoint constructs only the actual squared
seminorm, Cauchy quotient carrier and its induced maps. Completed scalar
pairing, vector operations/laws, positive definiteness, metric completeness
and a physical Hilbert/OS root still need proof. The fixed unit alone does
not establish a nonconstant excitation, uniqueness or isolation of vacuum.

The observable domain remains the real rational span of scheduled spatial
face-character products for the selected fixed-width SU(2) chain action.
It is not an established complete gauge algebra or the full growing-box
action/marginal. Joint cutoff/time passage, spatial thermodynamic and
continuum control, the strict vacuum-complement bound with physical mass
normalization, continuum QFT axioms and every compact simple group remain
open. No canonical field, literal hole or analytic hypothesis was changed.

## Next causal frontier, reviewed but not yet proved

Construct the completed inner product for THIS reflected Cauchy carrier.
No generic completed-inner-product producer for arbitrary SquaredSeminorm
was located in the reviewed completion modules. The next bounded estimate
is quantitative continuity of the actual intrinsic pairing. Generic scalar
tools `smallTolerance`, `smallTolerance_budget`, `signed_small_of_square`
and `pairingTolerance` are at
`lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingContinuity.lean:29`, `:36`,
`:44`, `:94`. Its old model-specific `pairing_close` is not an instance for
the new form. Use the new sharp CS and difference laws to prove the estimate
with delta=epsilon^2/[8*(B+1)].

For a Cauchy representative X, the proposed explicit anchor is
iX=X.modulus 1. The computed coefficient cap CX of X.seq iX and the actual
`pairing_add_bound` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntrinsicSeminorm.lean:94`
give the candidate eventual diagonal ceiling BX=2+2*CX. Prove that bound,
then use the maximum of both anchor indices and both delta-moduli for the
outer pairing sequence. No modulus monotonicity or supplied norm ceiling
should be assumed.

The actual pairing unfolds to ofQ'CauchySeq. Generic
`ofQ'CauchySeq_family_regPred` at
`lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion.lean:39`
supplies its inner regularity. `completeLimitFromRate` at
`lean/YMGap/Constructive/CRealCompleteRate.lean:335` is the constructive
limit consumer. Representative-limit well-definedness and Quotient.lift2
in `lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedInner.lean:66` and
`:83` are templates, not interchangeable concrete instances.

After proving continuity, constructing that limit and descending close
representatives, the existing `completedTime_embedSpan` supplies the
time-correlator embedding pin. Completed linear/Hilbert laws and metric
completeness remain further obligations, not automatic consequences of
having named a Cauchy quotient Completion.

## Verification

Seven focused checks used the monitored launcher, one worker and a 20 GiB
hard worker ceiling, with a fresh process/swap preflight before each check.
All 101 public axiom gates report only {propext, Quot.sound} or no axioms.
Final logs contain no sorryAx, classical dependency, error or warning.
No root build, full-tree check or full axiom audit was run. Seven imports
are added to the selective root; that is not a claim that the root was checked.

| Module suffix | Gates | `/tmp/<full module name>.log` SHA-256 |
|---|---:|---|
| `IntrinsicUnit` | 7 | `9a531267dc34231e680b1e5cad788c9bf832cec1bd791e53c780a0ea95f8cfbb` |
| `IntrinsicDifference` | 10 | `46a106b86f916f3c391ddb85b1bf6d350f179e2384928af6cec6587181339ee3` |
| `PhysicalTimeShift` | 19 | `806f42a187e63bbe122a3911551a889f36b160075f5ebf31fb714aa9eee33ac2` |
| `UniformProbeCap` | 23 | `1e8ceba6f3f97bc160b5296bf5f1e1dfc96a486e1e88ca1f156a41e04f402ee1` |
| `PhysicalTimeContraction` | 11 | `e1f0cf32940bf4f189ea9bc8c4e9c775ea2cba497382dc39a14ef3161b98d85e` |
| `IntrinsicSeminorm` | 12 | `8416ac58833e225c1dfacf1fdd5c947b759c8bf4ec50d0dc3e4ad06eaba3d63d` |
| `CompletedPhysicalTime` | 19 | `1325d2cf11aff17781d6f1de859b5d74959d623378b0d4c99c318a1ab4305cd5` |

Each suffix has prefix BF4ExactSlabFixedSpatial. Parallel agents supplied
independent proofs and read-only reviews; only the main agent compiled,
serially. Independent final review found no defect in coefficient-only
invariance, original reflected contraction, subtype guards, squared
triangle/null congruence, composition order, exact modulus preservation or
unit non-nullity. No new literal holes, axioms, classical input, raised
limits, CI change or routine literature scan.
