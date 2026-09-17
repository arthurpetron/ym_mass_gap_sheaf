# Original Wilson expectations: joint lattice-regulator limits

Date: 2026-09-17 UTC. Previous turn `42ff5fa`: **PROGRESS**, committed and
pushed. The unchanged whole-project goal is constructive continuum Yang--Mills
existence with nontriviality, the required QFT axioms and a positive physical
Hamiltonian gap for every compact simple gauge group. That goal is **OPEN**.

## Result and causal connection

Actual finite signed expressions of closed spatial Wilson-loop characters
now have a constructed CReal limit as spatial margin, heat cutoff and external
time depth recede. The original selected-chain action, observable and partition
are retained. The previous fixed-width joint time/cutoff limits converge to
this SAME spatial limit. Complete signed reflected products remain nonnegative.

This is a fixed-spacing, small-nome SU(2) lattice result. The individual
limits and positivity have not yet been assembled into a consistent full
OS state, radical quotient/completion, full observable realization or a strict
bound on the enlarged carrier. The old plaquette-generated completed gap does
not transfer merely because these new observables also have limits.

EXPANSION separated two mathematical inputs: an explicit two-index time/cutoff
modulus, and a spatial comparison of the actual original action. The latter
required literal ordered-word translation, a placement-independent cap and a
fixed containing box. CONTRACTION uses these proved inputs at one computed
spatial pivot to return the original three-index limit and its modulus.
No time modulus uniform across all spatial widths was assumed.

All modules in the following table are under `lean/YMGap/Continuum/`.

| Actual result | Declaration and source |
| --- | --- |
| Cutoff Cauchy data for the original scalar at one fixed time | `windowCutoffCauchy`, `BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:36` |
| Stage-independent time pivot and cutoff threshold at that pivot | `jointTimeThreshold`, same file:46; `jointCutoffThreshold`, same file:52 |
| Independently late heat stages and symmetric time depths | `originalJoint_rectangle`, same file:87; `originalJoint_approx`, same file:131 |
| Constructed original joint limit and retained reflected positivity | `originalJointLimit`, same file:118; `originalJoint_reflected_nonnegative`, same file:160 |
| Ordered Wilson words/all-spin characters under the actual slab embedding | `word_pin`, `BF4ExactSlabTranslatedWilsonWord.lean:35`; `character_pin`, same file:52 |
| Actual closed source loops and expressions recentered with explicit width room | `recenterLoop`, `BF4ExactSlabFixedSpatialWilsonRecenter.lean:80`; `recenterExpression`, same file:92 |
| Successive recenters compose; the full placed expression has an exact prefix pin | `recenterExpression_comp`, same file:138; `placed_pin`, same file:174 |
| Shared/repeated-link ordered words have Haar-unit norm and a computed character cap | `word_unit`, `BF4ExactSlabSpatialWilsonControl.lean:113`; `character_interval`, same file:122 |
| Complete signed expression cap and literal placed interval | `windowCap`, same file:130; `placed_interval`, same file:160 |
| Literal recentered expression is supported on one fixed translated link box | `placed_recenter_local`, `BF4ExactSlabFixedSpatialWilsonBoxLocality.lean:96`; `boxCarrier`, same file:105 |
| Same polynomial under aligned charts; same scalar under raw and centered charts | `aligned_chartInsertion_pin`, `BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:95`; `chartScalar_original_pin`, same file:127 |
| Actual original normalized spatial difference, with cap/locality discharged | `chartScalar_spatial_bound`, same file:186 |
| Constructed three-regulator Cauchy data and its exact stored modulus | `spatialCauchy`, `BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:62`; `spatialCauchy_modulus`, same file:70 |
| Same limit for raw diagonal and previous joint expectations | `spatial_diagonal_converges`, same file:78; `jointLimits_spatial_converge`, same file:85 |
| Independently late spatial/heat/time indices approach its actual representatives | `spatial_approx`, same file:100 |
| Complete signed reflected products remain positive after all three regulators | `spatial_reflected_nonnegative`, same file:123 |

## The short cap argument and the fringe correction

The interval proof does not enumerate coefficients of a long loop. Existing
Haar norm multiplicativity proves unit norm of the literal right-associated
ordered quaternion word, retaining shared links and every spectator. Its scalar
square certificate feeds the existing character interval construction. The
resulting cap is `2*16^spin`, independent even of word length, ambient size,
placement, width, nome and cutoff. The expression cap uses 1 for the unit,
sum/product for the corresponding operations and `(c*c+1)*cap` for signed
rational scaling. It remains observable-dependent and is not an OS norm bound.
These are `character_interval`, `windowCap` and `placed_interval` cited above;
`windowCap_recenter`, comparison module:66, preserves it under spatial shifts.

Source slice links allow coordinates equal to the source width. Their fixed
box must therefore have side `max(base+1,L+1)`, not the old face-only
`max(base,L+1)`. `boxSize`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonBoxLocality.lean:39`,
retains this fringe. `placedLinks_recenter_subset`, same file:69, proves the
literal inclusion before any polynomial-locality argument. Its returned
connected carrier has support size `6*n^4` (`boxCarrier_size`, same file:109).

## Parameters, normalization and limits

For source base `base`, chart half-window `H` and spatial margin `r`, the
actual spatial width is `base+2*r+2`. The chart is the existing even slab
`chartExtent base r H t`, its selected action is `chartIds base r H t`, and
the expression is spatially shifted by `r+1` and placed at
`base+2*r+2+1+t`. `chartScalar`, comparison module:120, uses the original
`finiteValue` at heat cutoff `headCutoff w+stage`.

Increasing r by d translates the old chart by d spatially and 2*d temporally.
The exact observable prefix pin identifies the filtered larger action with
the smaller action through the existing same-stage reciprocal theorem. It
does not identify the FULL larger action with the smaller one. The existing
signed action comparison separately bounds their difference by

`(cap(e)+cap(e))*boxAmplitude(w,n) * rho(w)^(r+1-6*n^4)`,

where `n=max(base+1,2*H+1)` and
`rho(w)=entropyRate 625 (adjustedCoreRate w hd)`. This is uniform in stage,
symmetric external time depth t and enlargement d, not in nome, source base,
window or expression. Natural subtraction truncates the exponent; eventual
decay begins beyond the fixed support loss. The theorem retains `0<base`,
`0<w<1`, `heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and `rho(w)<1`.
The positive-base guard was not silently removed; the general zero-base
promotion is not supplied in this checkpoint.

The raw time scalar need not be reflection centered. `chartScalar_original_pin`
uses the common compact window ratio to compare it with the centered chart
at the SAME cutoff and partition. A time pivot at epsilon/4 controls all
heat stages; cutoff control is then required at that one fixed original
time/ambient. A spatial pivot subsequently selects one row's joint modulus.
`spatialCauchy_modulus` displays the resulting explicit nested threshold.
The diagonal is the unmodified `chartScalar n n n`, and `spatial_approx`
separates all three raw indices from the CReal representative index.

No physical spacing varies. No beta-uniform physical gap is asserted. Full
spatial symmetry, changing-scale original-action control, physical time/mass
calibration, continuum survival and actual all-group producers remain open.
The small-nome AF obstruction and canonical OS fields are unchanged.

## Next bounded consumer

Prove rational linearity, normalization and polynomial-representation
congruence for THIS spatial limit at a common H, then define the mixed form
`B_H(e,f)=spatialLimit H (.mul (mirror H e) f)` and prove reflected symmetry.
Existing arbitrary-polynomial finite laws are `windowRatio_congr`,
`windowRatio_one`, `windowRatio_add`, `windowRatio_smul`, in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowFunctionalLaws.lean:81`,
`:89`, `:100`, and `:120`. The existing finite symmetry consumer is
`originalChain_finiteValue_reflected_symm`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReflectedSymmetry.lean:252`.
These are source-reviewed inputs, not new limiting-form theorems here.

The completion consumer `SquaredSeminorm`,
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:39`, requires symmetry,
triangle and radical descent (`null_congr`, same file:50); positivity alone
does not fill those fields. For intrinsic-time chart compatibility, increase
H AND shift offsets together. Changing H alone changes reflected separations.
The old exact analogue is `form_centered_inclusion`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReflectedForm.lean:247`.
No existing completed-carrier strict estimate is extended by these plans.

## Verification and independent review

Seven focused final module checks exited 0; all 65 public gates report only
{propext, Quot.sound} or no axioms. Final logs have no errors, warnings,
`sorryAx`, classical choice or native-reduction dependency. Early attempts
needed function-composition simplification, explicit structure projections,
controlled unfolding and an equivalence-direction correction. No statement
or resource limit was weakened or raised.

All checks used the safe-build procedure, one worker and 20 GiB, with fresh
process/swap inspection. Swap was 6901.19 MiB in these preflights. Root imports
were added; no root/full-tree build, full audit or guard run was performed.
No old proof, sorry, axiom, analytic guard or canonical field changed. CI stays
manual-only and no routine literature scan ran. Parent and three agents worked
on independent translation, control, geometry, integration and source review;
compilation stayed serialized. Independent reviews checked the two pivot
arguments, same-action normalization, fringe support and reflected positivity.

Final logs are in `/tmp/`; hashes are SHA-256.

| Module | Gates | Log | SHA-256 |
| --- | ---: | --- | --- |
| BF4ExactSlabFixedSpatialWilsonWindowJointCauchy | 11 | `ym-wilson-joint-20260917.log` | `a9c87b0a76e8784d59ff80f6c054d35598c63d8e74278d5280a3b5c7e24ec2b6` |
| BF4ExactSlabTranslatedWilsonWord | 2 | `ym-translated-wilson-word-20260917.log` | `71aed1911d0b88bdb90ff1a53caf80019c98dd7965db197d53e09410ef4d5c8d` |
| BF4ExactSlabFixedSpatialWilsonRecenter | 10 | `ym-wilson-recenter-final-20260917.log` | `5f863ed8756b1278b884847a6a4716c37b2c79e1970c5ecd5bd20b72747c1aca` |
| BF4ExactSlabSpatialWilsonControl | 11 | `ym-wilson-control-20260917.log` | `103b671f8143204c533e40f5f4e9f3cf08dc1a4b066bd07deee64ce407abe7ae` |
| BF4ExactSlabFixedSpatialWilsonBoxLocality | 6 | `ym-wilson-box-locality-20260917.log` | `06036e81866844fcb70c6bba178937f87eabecc81ede236b2a4716bb66225193` |
| BF4ExactSlabFixedSpatialWilsonSpatialComparison | 16 | `ym-wilson-spatial-comparison-final-20260917.log` | `19196b88bd9e9ad0d90ebd720783da607fcc74ee679016cf6efea0a6c6da0454` |
| BF4ExactSlabFixedSpatialWilsonSpatialLimit | 9 | `ym-wilson-spatial-limit-verified-20260917.log` | `c0628e4e503eb3704e06c4ef0095d9d87238b34bcccb5c84c434f2549c6f3013` |
