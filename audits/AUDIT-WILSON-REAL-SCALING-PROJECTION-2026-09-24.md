# SAME Wilson real scaling, vacuum projection and connected correlations

Date: 2026-09-24 UTC. Scope: the EXISTING all-nome Wilson completion at
fixed 0<w<1 and fixed width. The continuum Yang--Mills / physical mass-gap
goal for every compact simple group remains OPEN.

## Mathematical construction

For an actual Cauchy representative X and real scalar s with supplied
Type-level QCauchy data, the sequence s.approx(n)*X.seq(n) has a computed
squared-distance modulus. The estimate splits a*x-b*y through a*y. A
computed scalar ceiling controls the vector change; a computed pairing
ceiling controls the coefficient change. The sqrt-free triangle combines
the two quarter-tolerance bounds. No modulus is extracted from the legacy
propositional `CReal.cauchy` field.

Pairing convergence proves exact homogeneity. Positive definiteness then
proves scalar-value, modulus and vector-representative independence, so
the action descends to the SAME completed quotient. The scalar addition
and multiplication laws reuse the existing generic computed QCauchy
arithmetic. Time is the existing completed physical-time map, not a new
operator or bare heat substitution.

The mixed pairing against the constant unit representative supplies both
the real vacuum coefficient and its explicit modulus. Scaling the unit
stream constructs P(x)=B(x,U)*U and proves quotient descent without selecting
representatives. The map is additive, self-adjoint, idempotent, norm-
contractive, fixes U and commutes with actual time. C(x)=x-P(x) lands in
the existing VacuumComplement and satisfies, for arbitrary completed x,y,

    B(C(x),C(y))    = B(x,y)    - B(x,U)*B(U,y),
    B(C(x),T(n)C(y)) = B(x,T(n)y) - B(x,U)*B(U,y).

The new map agrees EXACTLY with the previously constructed centeredVector
on embedded dense Wilson expressions, and the corresponding vacuum-
complement subtype values agree. This equality is proved by pairing limits
against arbitrary completed tests, not inferred from equal norms. The
original dense mean and the projection's completed coefficient have
different approximation streams; `completedInner_embed` supplies the
explicit scalar-value pin.

## Declaration evidence

All paths below are relative to the repository root.

| Declaration | Source | Content |
|---|---|---|
| `BF4WilsonAllNomeRealScalarCauchy.distSq_scalar_difference` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarCauchy.lean:67` | Exact coefficient-square identity. |
| `.realScalarRate` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarCauchy.lean:100` | Computed stream modulus. |
| `.realScalarCauchy` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarCauchy.lean:151` | Actual Wilson Cauchy stream. |
| `BF4WilsonAllNomeCompletedRealScalar.completedRealSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedRealScalar.lean:85` | Choice-free quotient action. |
| `.completedInner_realSmul_left` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedRealScalar.lean:95` | SAME pairing homogeneity. |
| `.completedRealSmul_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedRealScalar.lean:105` | Scalar-value/modulus independence. |
| `.completedTime_realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedRealScalar.lean:129` | ORIGINAL time commutation. |
| `BF4WilsonAllNomeRealScalarLaws.completedRealSmul_addScalar` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarLaws.lean:48` | Scalar addition with computed modulus. |
| `.completedRealSmul_mul` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarLaws.lean:59` | Scalar product with computed modulus. |
| `.vacuumComplementRealSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarLaws.lean:76` | Existing complement preserved. |
| `BF4WilsonAllNomeUnitProjection.unitCoefficientCauchy` | `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:61` | Actual pairing coefficient modulus. |
| `.unitProjection` | `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:87` | Constructed projection for every completed vector. |
| `.unitProjection_norm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:150` | Constant-one norm contraction. |
| `.centeredState` | `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:204` | Actual existing complement as codomain. |
| `.centeredPart_time_pairing` | `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:231` | SAME-operator connected correlation. |
| `BF4WilsonAllNomeCenteringPin.centeredPart_embed` | `lean/YMGap/Continuum/BF4WilsonAllNomeCenteringPin.lean:75` | Exact equality with prior dense centered vector. |
| `.centeredState_embed` | `lean/YMGap/Continuum/BF4WilsonAllNomeCenteringPin.lean:83` | Corresponding subtype equality. |

## Causal residue

The existing dyadic centered variance and loss estimates apply to this same
state by the proved equality, with unchanged constants. No useful new
changing-scale bound follows. A03 still needs complete signed cost relative
to SAME interacting centered variance, or direct response, on a justified
scaling family. The iterated worst-case channel floor remains a pruned
normalization strategy.

J02 has additional actual algebra and projection, not full Hilbert/OS/QFT
closure. No complex scalar structure, arbitrary quotient-row representative
selection, full QFT/YM fields or UV identification is supplied. SAME
thermodynamic/continuum passage, nontrivial survival, physical Hamiltonian
and mass calibration, EVERY-state scaling and all-group extension remain
open. B01--B03's recorded face-span carrier is not replaced or identified
with the Wilson completion.

## Verification

Five final serialized narrow checks exited zero. All 56 printed gates
stay within {propext, Quot.sound}. Each used `scripts/safe_lean_build.py
--jobs 1 --check` with explicit output olean, 2 GiB worker cap, default
elaboration limits and unchanged 12 GiB OS reserve. Projection check 2
was refused and check 3 stopped at the reserve; memory/process state was
remeasured before resumption without weakening thresholds. Draft notation
collision, explicit RC rational-scaling identification, unit-normalization
representation and rewrite-order errors were repaired before acceptance.
No source hole, new axiom, analytic premise or canonical-field change.
Independent source/scope reviews passed. No full-root/tree build, axiom
audit or guard was run.

| Final local log | Gates | SHA-256 |
|---|---:|---|
| `/tmp/ym-gap-wilson-all-nome-real-scalar-cauchy-check-2.log` | 7 | `1848ff6dbec999338bf4318ebad7db906039e536cd656b3808285fdd6abe2940` |
| `/tmp/ym-gap-wilson-all-nome-completed-real-scalar-check-2.log` | 14 | `acbcf1bde23efa943be79141a70ff1f8ff4710cc90d2e2517e91d46c8a3a2f00` |
| `/tmp/ym-gap-wilson-all-nome-real-scalar-laws-check-1.log` | 5 | `679cc418d156379304f70b3492c468c1e8bacf79ba3ba3a1b070955fbdc52eb8` |
| `/tmp/ym-gap-wilson-all-nome-unit-projection-check-5.log` | 27 | `9751112e45600f8fe717b322144a7cabb7f0445d81a97200f54f6e9f7705c609` |
| `/tmp/ym-gap-wilson-all-nome-centering-pin-check-1.log` | 3 | `539e967ab6017e28c7233c9cad93975600a179097cec1ec5968a14bbbd0810f5` |

Two semantic-root imports include all five leaves transitively. Schema 1
snapshot 22 records partial J02 evidence only. The exact canonical chart
block, permanent labels/scopes and every goal-node marker remain unchanged.
