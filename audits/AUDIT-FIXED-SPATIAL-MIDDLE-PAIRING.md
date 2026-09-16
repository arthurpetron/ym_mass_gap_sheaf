# Actual weighted symmetry and finite middle pairing

Date: 2026-09-16. Classification: PROGRESS after `1c981db`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the
required QFT axioms and a positive physical Hamiltonian gap for each compact
simple group, in the SAME theory, within the constructive witness/axiom gate.
This increment is finite SU(2) algebra at fixed spatial width, not that goal.

## Mathematical contraction

Write N for the complete source-slice link count, T for the existing
partial-Haar transfer with actual kinetic K and spatial V, ell(h)=H[V*h],
and u_j=T^j1. The explicit permutation swaps all N lower blocks with all N
upper blocks, including unused fringe coordinates. Under this permutation,
lower*conj(upper) becomes upper*conj(lower). Their scalar parts are the same
quaternion dot product; quaternion multiplication is NOT made commutative.
Every original character, heat coefficient and temporal face is retained.

Fubini writes ell(g*T f) as the double integral of K(x,y)V(x)V(y)f(x)g(y).
The checked swap therefore proves ell(g*T f)=ell(f*T g), and finite
iteration gives the same identity for T^n. Support guards protect the
complete carrier. No positivity is needed for these signed identities.

For 0<w<1 and K>=headCutoff(w), every u_j has a square certificate and
positive ell mass. The existing constant transfer floor, multiplied by a
certified message, proves ell(u_m*u_n)>0. This is NOT inferred merely from
the positivity of the two separate masses. Zero lengths reduce to the
existing positive spatial mass. Multiplying any relative bracket by a
certified terminal message preserves its endpoints and hence bounds the
normalized pairing whenever the actual product denominator is positive.

The finite chronological chain with a probe p inserted at slice m contracts
exactly to ell(T^n(u_m*p)). Weighted symmetry then gives ell((u_m*p)*u_n).
There are m+n+1 spatial weights in the chain; the middle V occurs exactly
once in ell. The chain partition is ell(u_(m+n))=ell(u_m*u_n), and is
strictly positive under the same original nome/cutoff guards.

IMPORTANT: `terminalProbeRatio` has numerator ell(u_m*T^n p). It is an
evolved endpoint probe, not the interior numerator ell((u_m*p)*u_n).
The new `middleRatio` keeps these objects distinct. Neither definition
asserts a stationary vacuum or two-sided convergence.

## Declaration evidence

All module paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Actual content |
|---|---|---|
| `swap`, `lower_prefix`, `upper_prefix`, `haar` | `SU2QuaternionTwoSliceSwap.lean:30`, `:118`, `:130`, `:149` | Explicit complete-slice involution, supported lift pins and Haar invariance. |
| `relative_scalar_swap`, `character_swap`, `heatFactor_swap`, `kineticWeight_swap` | `BF4ExactSlabFixedSpatialKineticSymmetry.lean:95`, `:110`, `:134`, `:163` | Symmetry of the original relative scalar through the entire kinetic product. |
| `transferStep_weighted_symmetric`, `iterateStep_weighted_symmetric` | `BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`, `:128` | Original V-weighted symmetry of T and every power. |
| `multiplyBracket`, `terminalMassRatio_bounds` | `BF4ExactSlabFixedSpatialTerminalBracket.lean:50`, `:68` | Certified multiplication preserves actual relative endpoints. |
| `weightedMass_product_floor`, `weightedMass_pair_transfer_positive` | `BF4ExactSlabFixedSpatialTerminalBracket.lean:78`, `:104` | Quantitative product floor, then strict product positivity. |
| `terminalMessage`, `terminalMessage_certificate`, `terminalPair_positive` | `BF4ExactSlabFixedSpatialTerminalBracket.lean:118`, `:126`, `:149` | Actual finite u_j and proved positive pair denominator. |
| `terminalProbeRatio`, `terminalProbeRatio_bounds` | `BF4ExactSlabFixedSpatialTerminalBracket.lean:171`, `:182` | Endpoint-probe pairing in the existing interval; NOT an interior estimate. |
| `liftBoundary_add`, `chain_middle_pairing` | `SU2QuaternionHeadChainMiddleInsertion.lean:36`, `:62` | Exact lift composition and ordered contraction retaining the interior probe. |
| `iterateStep_add`, `terminalPair_total` | `BF4ExactSlabFixedSpatialMiddlePairing.lean:47`, `:63` | Exact iteration composition and pair mass equals total-chain mass. |
| `middle_pairing` | `BF4ExactSlabFixedSpatialMiddlePairing.lean:80` | Actual chronological numerator equals ell((u_m*p)*u_n), with supported p. |
| `chain_partition_pairing`, `chain_partition_positive` | `BF4ExactSlabFixedSpatialMiddlePairing.lean:102`, `:116` | SAME chronological partition, with constructed strict positivity. |
| `middleRatio` | `BF4ExactSlabFixedSpatialMiddlePairing.lean:125` | Interior scalar with its positive denominator; no limit is supplied. |

## Remaining causal frontier

The chronological source carrier has not yet been pinned to an original
ambient-lattice insertion at slice start+m. The reviewed finite route uses
the middle-block embedding identity, the existing source-probe pin and
original chain action pin, with width<=extent, start+m+n<=extent, and
membership of every probe face in spatialFaces(width). The signed algebra
above does not discharge these geometric guards or its reciprocal pin.

The next quantitative comparison must initialize the generic relative
bracket on (u_m*p,u_m), multiplying the existing source interval by the
certified u_m. The specialized endpoint-probe bracket is not that theorem.
Two-sided boundary-forgetting estimates and explicit bulk Cauchy moduli are
NOT yet checked. This paragraph records the next proof argument, not a
new hypothesis or a claimed theorem.

The inherited contraction rate depends on nome and spatial width, though
not on the late heat cutoff. No width- or spacing-uniform rate is proved.
Multi-insertion consistency, shift invariance, connected correlations,
physical reflected OS/vacuum identification, completed cutoff-limit
operator power/moment compatibility, thermodynamic/continuum construction
and the all-group physical gap remain open. Finite weighted symmetry is
neither unweighted-Haar-completion symmetry nor physical OS self-adjointness.

## Verification boundary

Six focused serialized one-worker/20 GiB checks passed all 34 public axiom
gates within {propext, Quot.sound}; liftBoundary_add uses only propext.
Each check had a fresh process/swap preflight; no competing Lean/Lake/test
process was found and recorded swap stayed at 7085.19 MiB. A base-case
Nat.zero_add simplification fixed the sole failed middle-contraction check;
only the successful final logs are claimed here. No heartbeat/memory/worker
limit was raised. The swap check has one unused-variable warning.

Independent read-only reviewers checked chronology, original K/V factors,
zero-length cases and the endpoint/interior distinction. Six selective-root
imports were added; root/full-tree/full axiom audit was NOT run. No old
declaration, frontier field, literal hole, axiom or analytic premise changed.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| SU2QuaternionTwoSliceSwap | 7 | `52f8de24be9cdfc9adaffd205e7e90d69a46a099fdb196649775b0c26d224e72` |
| BF4ExactSlabFixedSpatialKineticSymmetry | 6 | `02e257c11207e38ed5627f0a49d38eb647a22e7e4a0993aa45190f0b7c582bdf` |
| BF4ExactSlabFixedSpatialTransferSymmetry | 2 | `f9ae958de02eb2b465a80f56af09c0fd0f42c3ad79a80a4258beee06816c5d9f` |
| BF4ExactSlabFixedSpatialTerminalBracket | 11 | `aef499bc67531a02c01253a5ff8f503284bee55704075a22f92d6143dbc20de6` |
| SU2QuaternionHeadChainMiddleInsertion | 2 | `04f214da47eef98cbccba464d34c2805b688f0ae903a236157c7f77fe7c72e48` |
| BF4ExactSlabFixedSpatialMiddlePairing | 6 | `e38b7a3891dfac4bf090a3388937b04783be8682a0f7d729af418ddf121596b9` |
