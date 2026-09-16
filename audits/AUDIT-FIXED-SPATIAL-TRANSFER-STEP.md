# Original weighted step and exact finite-chain identities

Date: 2026-09-16. Classification: PROGRESS after `370dc74`.

Whole-project goal: constructively build nontrivial continuum Yang--Mills
on R^4 with the required QFT axioms and a positive physical Hamiltonian gap
for each compact simple gauge group, on the SAME theory. This increment
does not establish a stationary OS transfer or a mass gap.

## Actual mathematical increment

On the width-only spatial carrier with N quaternion blocks, let V be the
previous original spatial weight. Construct K on two ordered copies using
the original lower spatial link times the conjugate upper spatial link.
Every temporal face and finite heat-character term is retained. Exact
placement identifies K with the original swept kinetic heat.

The explicit finite map is

    (T f)(y) = integral_x K(x,y) V(x) f(x) dH(x).

It returns a supported polynomial on the SAME N-block carrier. The proved
original swept pairing is

    H_ambient[K_t V_t E_lower(f) V_(t+1) E_upper(g)]
      = H_N[(T f) V g].

Here equality means the project's exact rational setoid equality. Each
endpoint spatial weight occurs once. No normalization, positivity, T1=1,
stationary vector, bounded operator or spectral estimate is asserted.

Two further identities are proved, separately:

1. An ordered chain obeys `C_0(g)=Vg`,
   `C_(n+1)(g)=K V lift_N(C_n(g))`, and
   `H_((n+1)N)[f C_n(g)] = H_N[(T^n f) Vg]`.
   The proof is finite Haar Fubini and arbitrary-N polynomial pull-out.
2. A complete chronological list of the original physical faces has no
   duplication. One common temporal gauge sweep of its original action,
   with the same signed spatial-face probes, gives
   `V0*K01*V1*...*K(n-1,n)*Vn` on ambient coordinates.

The arbitrary-length carrier placement connecting (1) to (2) is OPEN.
The one-step result is not a proof of that missing general connection.

## Declaration evidence

Paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `relative` | `BF4ExactSlabFixedSpatialKineticHeat.lean:64` | Actual lower-times-conjugate-upper order. |
| `kineticWeight` | `BF4ExactSlabFixedSpatialKineticHeat.lean:68` | One width/nome/cutoff-only kinetic polynomial. |
| `relative_pin` | `BF4ExactSlabFixedSpatialKineticHeat.lean:94` | Original temporal relative quaternion. |
| `heatFace_pin` | `BF4ExactSlabFixedSpatialKineticHeat.lean:133` | Complete heat sum preserved. |
| `kineticWeight_pin` | `BF4ExactSlabFixedSpatialKineticHeat.lean:149` | Original kineticHeat placement, including multiplicities. |
| `kineticWeight_supported` | `BF4ExactSlabFixedSpatialKineticHeat.lean:193` | Two-slice support. |
| `kineticWeight_haar` | `BF4ExactSlabFixedSpatialKineticHeat.lean:203` | Original kinetic pairing for supported source insertions. |
| `BlockEmbedding.polynomial_liftBoundary` | `SU2QuaternionHaarBlockEmbeddingPlacement.lean:110` | Literal equality for consecutive-block placement. |
| `BlockEmbedding.polynomial_head_placement` | `SU2QuaternionHaarBlockEmbeddingPlacement.lean:125` | Head-placement specialization. |
| `partialHaarHeads_mul_lift` | `SU2QuaternionHeadChainComposition.lean:51` | Exact pull-out of retained polynomial coefficients. |
| `step` | `SU2QuaternionHeadChainComposition.lean:75` | Computed finite map for supplied K and V. |
| `step_supported` | `SU2QuaternionHeadChainComposition.lean:85` | Same-carrier support. |
| `step_pairing` | `SU2QuaternionHeadChainComposition.lean:97` | One-step identity with arbitrary later-slice insertion. |
| `chain_pairing` | `SU2QuaternionHeadChainComposition.lean:180` | Exact finite-chain iteration, not an original-action pin by itself. |
| `transferStep` | `BF4ExactSlabFixedSpatialTransferStep.lean:51` | Actual original K/V instance. |
| `transferStep_supported` | `BF4ExactSlabFixedSpatialTransferStep.lean:54` | Actual step returns to the same spatial carrier. |
| `swept_step_pairing` | `BF4ExactSlabFixedSpatialTransferStep.lean:77` | Original ambient weighted one-step pairing. |
| `chainIds` | `BF4ExactSlabFixedSpatialChainGeometry.lean:29` | Original chronological physical face list. |
| `chainIds_mem_iff` | `BF4ExactSlabFixedSpatialChainGeometry.lean:35` | Exact time/width/plane membership. |
| `chainIds_nodup` | `BF4ExactSlabFixedSpatialChainGeometry.lean:91` | Every shared spatial slice counted once. |
| `chainIds_two` | `BF4ExactSlabFixedSpatialChainGeometry.lean:121` | Previous two-layer list is the literal special case. |
| `chainIds_faces_mem_iff` | `BF4ExactSlabFixedSpatialChainGeometry.lean:126` | Raw-face completeness under containment. |
| `chainFaces_perm` | `BF4ExactSlabFixedSpatialChainGeometry.lean:167` | Canonical placed faces permute the original list. |
| `originalChainAction` | `BF4ExactSlabFixedSpatialChainAction.lean:45` | Same original heat action on that selected region. |
| `ambientChain` | `BF4ExactSlabFixedSpatialChainAction.lean:49` | Original V/K factors on ambient coordinates. |
| `swept_chain_factorization` | `BF4ExactSlabFixedSpatialChainAction.lean:82` | One complete common sweep gives the chronological factorization. |
| `original_chain_pairing` | `BF4ExactSlabFixedSpatialChainAction.lean:102` | Original action and signed spatial probes share that sweep. |

## Scope and remaining obligations

- K and the one-step pairing require width<=extent and start+1<=extent.
  Original-chain completeness requires width<=extent+1 and start+n<=extent;
  its action identity also holds for the explicit clipped list. Nome w,
  cutoff K, width, extent and time parameters remain visible. No numerical
  rate, coupling-uniform bound or continuum limit was added.
- Source support is essential in placement identities: coordinates outside
  the source carrier cannot silently be discarded. Inclusive fringe links
  remain. Arbitrary source probes can depend on unused action coordinates,
  so those coordinates are not automatically spectators in a pairing.
- The original sweep is applied once to the full finite action and signed
  spatial-face probes. It does not prove that intermediate T^j f is an
  unchanged original gauge-invariant observable under a new sweep.
  Its probes may lie anywhere physically present in the ambient slab,
  not only on window endpoints. A compact endpoint-chain application must
  prove the appropriate probe placement or handle extra variables explicitly.
- Next finite proof: construct the ordered (n+1)-slice embedding, verify
  its head/tail subplacements, and pin the whole action and endpoint
  insertions before using `chain_pairing`. Existing consecutive-placement
  equality provides the algebra needed by that still-unproved construction.
- Stationary normalization, completed reflected OS identification,
  quantitative original-Haar contraction or signed-response control,
  cutoff-dependent message limits, nome/volume/spacing passage, continuum
  QFT/nontriviality and the all-group physical mass gap remain open.
  No canonical frontier field or literal hole was changed or discharged.

## Parallel review and verification

Independent branches supplied head-chain composition, chronological geometry
and exact embedding/lift compatibility. The parent constructed the original
kinetic, one-step and common-sweep action pins. Independent source review
found no orientation, omitted-factor or endpoint-weight defect in K/step;
it explicitly checked the probe and fringe limitations above.
Another source review checked the arbitrary-chain action, its cut guard,
endpoint count and unrestricted physical spatial-probe scope, with no defect found.

All six new modules passed focused one-worker/20 GiB checks through
`scripts/safe_lean_build.py`; all 45 public gates are within
{propext, Quot.sound}. Process/swap preflights preceded checks. Verification
paused for a separately owned broad test suite and resumed only after its
specific PID exited and a fresh global preflight was clear. No user process
was stopped. Initial namespace/projection/support inference errors were
corrected before acceptance. An abstract product/map rewrite removed a
kinetic-pin elaboration timeout without increasing heartbeat, memory or
worker limits. No warnings remain in the six final logs.

Six root imports were added. Root/full-tree verification and the full axiom
audit were NOT run. CI remains manual-only. Local terminal-log hashes:

| Log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialKineticHeat.log` | `60bd2a867120a86df4672d987254e405378612b5be88cdc8e0ba5e6eb735b18e` |
| `BF4ExactSlabFixedSpatialChainGeometry.log` | `5b5a9c10b343564b466d59e5ceb91e7ea1a2105b720a20ffe6b05cfb402ae39a` |
| `SU2QuaternionHaarBlockEmbeddingPlacement.log` | `15e8c6a0467bb7c0a8954981804fb3ccefffbd1b2d696bd1b76b775941f9e0e2` |
| `SU2QuaternionHeadChainComposition.log` | `24426513ee478e56ea3d32b146821c9e98978193fb14548064cf54322361ba49` |
| `BF4ExactSlabFixedSpatialTransferStep.log` | `9ac30e9bb1c8bf256b2011f03c508ea12c20508529c5378b0833a3b13e32e218` |
| `BF4ExactSlabFixedSpatialChainAction.log` | `495b16ae4b24fa985aff57f321285ac3e91159f7d86b4ea7d1fc222d88a6c47a` |
