# Original-partition fusion cutoff boundary

Date: 2026-09-17 22:33 UTC. Parent source baseline:
`bcc466f468c3032ff8d9f256b8c78c77efb1b063`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated vacuum
and a strictly positive finite physical Hamiltonian mass gap. OPEN.

This checkpoint proves the full-source finite fusion identity and its
relative cutoff-boundary estimate. It does NOT prove a signed bulk bound,
temporal decay, a scaling limit or the Clay target.

## 1. Exact source and connected determinant

Write c_j=(j+1)*w^(j*(j+2)), chi_j for the twice-spin-label-j character,
V=H_K(p)*R_p for the ORIGINAL spatial action, and g_m=T^m(1), T=Kinetic(V*.):

    bulk = sum_{j=1}^K (c_(j-1)+c_(j+1)-c_1*c_j)*chi_j
    edge = c_K*chi_(K+1) - c_(K+1)*chi_K
    (chi_1-c_1)*H_K = bulk + edge

This coefficient identity holds for every rational w and every K, including
zero: `heat_fusion_residual`,
`lean/YMGap/Continuum/SU2QuaternionHeatFusionResidual.lean:137`.
The bulk and edge polynomials are `bulkResidual` and `boundaryResidual`,
same file at lines 41 and 46; `fusionCoeff` is at line 37.

Define U=Tg_m, F=T(g_m*chi_1), B=Kinetic(R_p*g_m*bulk),
E=Kinetic(R_p*g_m*edge). For any physical selected spatial face,

    F-c_1*U = B+E
    D(F,U) = D(B,U)+D(E,U)
    D(h,U) = J(h)*Z(U)-Z(h)*J(U).

Here J and Z are the ORIGINAL right-window `inputNumerator` and
`inputPartition`, retaining their action, probe and terminal message.
These are `originalFusion_message` and `originalFusion_determinant`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFusionIdentity.lean:113`
and `:159`. All terms use the SAME original U and normalization. No
independence of the interacting source R_p*g_m is assumed.

## 2. Physical relative boundary estimate

For 0<w<1, K>=headCutoff(w), and an actual right-window interval certificate
with cap c, put h=headFloor(w) and

    cap(w,K) = c_K*(K+2)+c_(K+1)*(K+1).

`fusionBoundary_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFusionBoundary.lean:72`, proves

    h*abs(D(E,U)) <= 2*c*cap(w,K)*Z(U)^2.

The signed E is NOT assumed positive. `inputNumerator_signed_bound`,
`inputPartition_signed_bound` and `inputCovariance_relative_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedInputBound.lean:60`,
`:118`, `:168`, use both certified positive comparisons d*v+E and d*v-E.
The final lemma also uses U-h*v positive to eliminate the auxiliary mass.

Their physical inputs are constructed, not left as new analytic premises:
`spatialWeight_split`, `remainderSource_certificate`,
`remainderMessage_lower`, `remainderMessage_upper`, `originalMessage_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceRemainder.lean:80`,
`:114`, `:201`, `:213`, `:248`. The full remaining spatial product and
actual terminal message stay inside the original kinetic integral.

The sharp two-edge interval and explicit tail modulus are `boundaryInterval`,
`boundaryCutoff`, `boundaryCap_small`,
`lean/YMGap/Continuum/SU2QuaternionHeatFusionBoundaryTail.lean:50`,
`:104`, `:108`. The cap is `boundaryCap` at line 40 of that file.

## 3. Explicit cutoff and direct consumer

The Type-level cutoff data are `boundaryTolerance` and
`relativeBoundaryCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFusionBoundary.lean:113`
and `:117`:

    tolerance = epsilon*headFloor(w)/(2*c+1)
    cutoff = max(headCutoff(w), boundaryCutoff(w,tolerance)).

For epsilon>0 and every K>=cutoff, `fusionBoundary_small` (same file:151)
proves abs(D(E,U))<=epsilon*Z(U)^2. The direct joined consumer,
`originalFusion_bulk_error` (same file:188), proves

    abs(D(F,U)-D(B,U)) <= epsilon*Z(U)^2.

For fixed w and a fixed certified cap c, the cutoff is independent of
spatial width, left and right boundary depths, and right-window length.
The denominator 2*c+1 includes the c=0 case. There is no uniformity claim
as w approaches 1. The action, messages and Z(U) may all vary with K;
only the relative error is controlled, not a raw unnormalized limit.

The signed bulk determinant D(B,U) remains unbounded by this checkpoint.
The next useful input is a cancellation-preserving estimate on that SAME
interacting quantity, followed by the all-time original Wilson-orbit
estimate with spatial/regulator control. Fundamental-face algebra does
not supply arbitrary products, spins or offsets. The improved-domain
limiting form, physical calibration, continuum/QFT and all-group joins
remain open; see `AUDIT-TRANSFER-ORBIT-CONSUMER.md` and `work_plan.md`.

## 4. Verification boundary

All six new modules passed focused serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`,
with process/swap preflight before each check. All 39 printed public gates
are within {propext, Quot.sound}; five are axiom-free. No sorry introduced
or discharged, new analytic oracle, canonical frontier-field edit, resource
change or CI change. Independent read-only mathematical/source review passed
the signs, K=0 case, full retained source, original normalization, factor
two and explicit-cutoff dependence. The final joined consumer also passed.

Six semantic-root imports were added. Root/full-tree/full audit/guard/progress
were NOT run; these focused checks are not a current full-tree audit.

Final compiler logs and SHA-256:

| Log in `/tmp/` | SHA-256 |
|---|---|
| `ym-signed-input-bound-20260917.log` | `ea2d8be4a4360cc0d5307df1f8df9e4c12f4178d4e3a5da6a137e87cd64153b4` |
| `ym-face-remainder-20260917.log` | `b8dd0276085df3f724f655682428e60c1f182b55b4841510d09aa4ae150aa03e` |
| `ym-heat-fusion-residual-20260917.log` | `ce09628e120b58333f2827b51c6fa1aef8c318518842e2c361517ccf7a13f565` |
| `ym-fusion-boundary-tail-20260917.log` | `cb08950ab2da8bc96bba8ecd266327cf0d6f49236ee7ed190d9e43c7c41f559b` |
| `ym-physical-fusion-identity-20260917.log` | `c5cbf9744016d33caf8ee5aeff8627d6db62afd3690ecf7462de97c479a268d7` |
| `ym-physical-fusion-boundary-20260917.log` | `c272dccbc9300f8c704bd80de0c5ff16f76f4477d836c284131eae1eb179f92f` |
