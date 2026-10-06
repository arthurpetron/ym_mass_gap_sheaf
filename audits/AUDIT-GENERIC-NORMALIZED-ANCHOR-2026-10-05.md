# Generic normalized-anchor A03 consumer; bridge-free path theorem for Y_j; B04l w -> 1 characterization

One final focused check passed. This step ports the A03 normalized-anchor
consumer from the dyadic unit excitation to ANY normalized vacuum-complement
state with a macro ratio. It then instantiates the port with the smoothed
coherent state `Y_j` of the P6 trajectory. It proves no new estimate: H1
(`PathEpsBound`) remains OPEN, and so does the new characterization Prop
`PathPhysicalContractionBand`. The unchanged whole-project goal is still
continuum Yang--Mills on R^4 for every compact simple group, with same-theory
QFT axioms and a positive physical mass gap.

New file: `lean/YMGap/Continuum/BF4WilsonAllNomeGenericNormalizedAnchor.lean`.
No original file or statement was edited.

## Mathematical increment

### The A03 target and the downstream chain

The backward A03 consumers named by
`audits/AUDIT-SCALING-CERTIFICATE-OBSTRUCTIONS-2026-10-03.md` ("Forward and
backward meeting point") are:

- `normalizedAnchorResponse_block_floor`
  (`BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`);
- `normalizedBond_geometric_real_floor`
  (`BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival.lean:148`).

The downstream chain from line 132 consists of:

- `halfAnchorPreimage_norm_cleared:115`;
- `normalizedMesh_increment_bound`;
- `normalizedBond_geometric_real_increment:300`;
- `..._forward_increment:322`;
- `normalizedBond_geometric_real_floor:148`.

`rg` finds no other consumer of these theorems. The remaining importers of
`NormalizedMacroRatio` (WindowSignedCost, SmoothedCoherentState,
CompletedLogConvexity, DyadicSmoothedTrajectory) produce `hratio`; they do not
consume it.

### Exactly what is unit-specific

Reading every proof in the chain, the ONLY unit-specific inputs are:

1. **Concrete norm representative.** A CONCRETE `CReal` `N` with Type-level
   `QCauchy N.approx` and the pin `B(x,T(2s)x) = [N]`. The normalizer
   `PositiveCRealNormalizationScalar.scalar` needs Cauchy data, and
   `CReal.cauchy` is only a Prop.
2. **Positive floor.** A positive rational `q <= N`. It is used only to build
   the inverse square root, and the bound `q <= N` is needed only for
   `normalizes`.
3. **Range witness.** A `TimeSector.State` with value `T(s)x`. The bond carrier
   (`ofState`) and the real-time `incrementRows` use it.
4. **Scalar facts about s.** `s/2+s/2=s`, `0<s`, and a rational spacing with
   `s*sp ≈ 1`.

No locality, support, cube carrier, source sign or spectral input appears.
`NormalizedAnchorData` packages items 1-3 (fields `base`, `block`, `norm`,
`normCauchy`, `norm_pin`, `floor`, `floor_pos`, `sector`, `sector_pin`). Item 4
is passed as explicit hypotheses only where it is used.

### Generalized theorems

Each takes `d : NormalizedAnchorData hw0 hw1 width`, `hfloor : leEv (ofQ' d.floor) d.norm`,
and the RC-level macro ratio

```lean
def MacroRatio (kappa : Q') : Prop :=
  RCle (RCscale kappa (B d.base.val (T d.block d.base.val)))
    (B d.base.val (T (2*d.block) d.base.val))
```

The normalized vector is `z = alpha * T(s) x`, defined by
`d.normalized := vacuumComplementRealSmul ... (vacuumComplementTime d.block d.base)`.

- `response_pin n : B(z,T n z) = [alpha]*([alpha]*B(x,T(2s+n)x))`.
- `normalized_norm hfloor : B(z,z) = 1`; `bond_norm`.
- `halfPreimage_norm_cleared kappa heven hfloor hratio :
  RCle (RCscale kappa (B h h)) (Rq 1)`.
- **`block_floor kappa hkappa hfloor hratio j :
  RCle (Rq (kappa^j)) (B z (T (j*d.block) z))`** (generalized line 132).
- `mesh_increment_bound kappa hkappa heven hfloor hratio p k ht`.
- `real_increment kappa hkappa hs heven hfloor hratio sp hsp epsilon he time ht`.
- `real_forward_increment ...` (same hypotheses, two times).
- **`real_floor kappa hkappa hs hfloor hratio sp hsp j time ht :
  RCle (Rq (kappa^(j+1))) (bondCompletedInner d.bondExcitation (action time d.bondExcitation))`**
  (generalized line 148).

Two RC lemmas carry the CReal-level algebra of the originals: monotonicity of
multiplication by a nonnegative real (`ga_mul_mono`), and commutation of real
with rational scaling (`ga_mul_scale`).

### Old theorems as corollaries (originals untouched)

`unitAnchorData` instantiates the structure with the LITERAL original data:

- `base := dyadicUnitExcitation`;
- `block := side scale`;
- `norm := anchorNorm`, `normCauchy := anchorNormCauchy`, with
  `norm_pin := dyadicUnitResponse_pin (2*side scale)`;
- `floor := anchorNormFloor`;
- `sector := anchoredSector 0`.

Its `normalizer`, `normalized`, `normalizedSector`, `bondExcitation` and
`halfPreimage` are definitionally the original `anchorNormalizer`,
`normalizedVacuumExcitation`, `normalizedSector`, `normalizedBondExcitation`
and `halfAnchorPreimage`. `unit_macroRatio` converts the original CReal
`hratio` (by two `dyadicUnitResponse_pin` rewrites). Each corollary below
carries the ORIGINAL statement verbatim and is a one-term application of the
generic theorem with `anchorNorm_floor`, `ga_side_halves` and
`spacing*side = 1`:

- `unit_halfAnchorPreimage_norm_cleared`
- `unit_normalizedAnchorResponse_block_floor`: also rewrites with
  `normalizedAnchorResponse_pin`
- `unit_normalizedMesh_increment_bound`
- `unit_normalizedBond_geometric_real_increment`
- `unit_normalizedBond_geometric_real_forward_increment`
- `unit_normalizedBond_geometric_real_floor`

### Constructing the data for the smoothed state Y_M

Items 1 and 3 are CONSTRUCTED, not assumed.

- **Item 1 (norm).** `smoothedNorm M n` is the finite double kernel sum
  (`kernelCSum`) of the existing centered time moments
  `centeredTimeMoment (m+k+n) fam fam`. `smoothedNormCauchy` builds its Cauchy
  data from `centeredTimeMomentCauchy`, `scalarAddCauchy`, `scalarMulCauchy`
  and a rational constant. `smoothedNorm_pin` gives
  `R_M(n) = [smoothedNorm M n]`, via `smoothedResponse_pin` and
  `responseSum_mk`.
- **Item 3 (range witness).** `repOrbit` is the representative-level orbit sum
  (the same addition, scaling and time maps on Cauchy streams), and
  `repOrbit_class` shows its class is `orbitSum`. `familyStream_class` is the
  identity `Class(centeredStream fam) = x_M` (by `rfl`). `smoothedSector M s`
  is `fromTime` of the represented `T(s-1)` preimage, and `smoothedSector_pin`
  shows its value is `T(s) Y_M`.
- **Item 2 (floor).** This is the only estimate. `trajAnchorData tr j kappa`
  uses `floor = kappa^2 * smoothedNormFloor_j`. `path_anchor_floor` proves it
  is a TRUE floor from H1, by the odd Jensen chain
  `block_survival_of_oneStep_energy` at i=2 times P3's unconditional norm
  floor.

`smoothedAnchor_macroRatio` shows that the generic `MacroRatio` of this data
IS `SmoothedMacroRatio`, definitionally.

## The final path theorem (no bridge)

```lean
theorem path_normalized_anchor (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H1 : PathEpsBound tr c0) :
    ∀ j : Nat, a ≤ j →
      B(z_j, z_j) = Rq 1 ∧
      (∀ i, RCle (Rq (kappa^i)) (B z_j (T (i * side j) z_j))) ∧
      (∀ i time, RCle (RCscale (spacing j) (realValue time)) (Rq (Q'.ofNat i)) →
        RCle (Rq (kappa^(i+1))) (bondInner b_j (action time b_j))) ∧
      (1 ≤ j → ∀ epsilon > 0, ∀ time,
        RCle (RCscale (spacing j) (realValue time)) (Rq (macroGeometricRadius kappa epsilon)) →
        RCle (bondDist (action time b_j) b_j) (Rq epsilon))
```

Here `kappa = (1-delta)^(2^a)`, `z_j = (pathAnchor tr delta hdelta a j).normalized.val`
and `b_j = (pathAnchor tr delta hdelta a j).bondExcitation`; the Lean
statement spells all of these out in full. The only OPEN hypothesis is H1.
`path_normalized_anchor_with_survival` adds H2 (`PathFamilyRadiusSurvival tr theta`)
and appends P6's un-normalized floor
`kappa^i * theta * B(x_j,x_j) <= R_j(side j * i)`. That conjunct is the ONLY
place H2 enters.

**`PathUnitRatioBridge` is fully eliminated from the route to the A03
normalized-anchor target.** The new file never mentions it. The A03 outputs
now concern `z_j` built from `Y_j` itself. The old `path_unit_anchor_floor`
(P6 file, unedited) is superseded, not deleted. A consumer that insisted on
the UNIT state's objects by name would still need the bridge; none exists.

No new OPEN Prop is needed for this part. `NormalizedAnchorData.MacroRatio` is a
predicate, not an open input; for `Y_j` it is discharged by H1.

## B04l: why the existing contraction stops at w <= 1/2, and what w -> 1 needs

Producer: `BF4PhysicalCubeCompletedMarginalGap.completedSectorContraction`
(`hw : w <= 1/2`). It takes the rate
`q(w) = cutoffUniformRate w = (1+6C(w))/(2+6C(w))` from the finite strict form
gap `matrix_le_cutoffUniformRate`. That gap combines:

- the head bound `anchored_head_bound`, with `C(w) = S/F`: the carrier-square
  path scale over the persistent pulled positive-edge floor `F(w) <= 1/2`;
- tail absorption `centered_norm_le_energy_add_anchored_head`, which uses
  `centered_newTail_le` and `newTailTraceRate_small`.

The hypothesis `w <= 1/2` enters ONLY in the tail. In
`BF4PhysicalCubeGaussianReturn.radialEnvelope_succ_le_half`, the bound
`4096*w^13 <= 1/2` (equivalent to `w <= 1/2`) makes the high-label Gaussian
return envelope `(M+1)^12 * 4096 * w^(gaussianExponent M)` halve per radius
step beyond 1400. The high-label trace is then summable, and a FIXED base
`1400+epsilon.den` absorbs the new tail uniformly in w. As `w -> 1` the
per-step factor `4096 w^13` exceeds 1, so a fixed base fails. Every
`NomeSchedule` eventually leaves `w <= 1/2`
(`nomeSchedule_eventually_not_le_half`).

### Named OPEN Prop (not attempted)

```lean
def PathPhysicalContractionBand (ns : NomeSchedule) : Prop :=
  ∃ m M : Q', (0 : Q') < m ∧ (0 : Q') < M ∧
    Nonempty (∀ j, {gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
        (ns.nome_pos j) (ns.nome_lt_one j) 0 //
      m * spacing j ≤ (1 : Q') - gap.rate ∧ (1 : Q') - gap.rate ≤ M * spacing j})
```

Proved links between this Prop and the existing interfaces:

- `pathCubeContraction_of_band`: band implies P6's bare `PathCubeContraction`.
- `rateBand_of_pathPhysicalContractionBand` and
  `pathPhysicalContractionBand_of_rateBand`: the band is EXACTLY a B04l
  `DynamicVacuumSectorPhysicalRateBand` on `trajectoryDynamicFamily ns gap`
  (same completed transfer, dyadic spacing).

### Characterization

A uniform-in-w contraction needs, at every `w_j -> 1`, a strict norm
contraction of the completed vacuum-complement transfer with rate
`r_j < 1`, AND quantitative control of `1 - r_j` relative to the spacing
`a_j = 2^-j`:

- **Lower half.** `1 - r_j >= m a_j`. With `r_j = exp(-Delta_j)`, where
  `Delta_j` is the spectral gap of the one-step transfer operator on the
  vacuum complement in lattice units, this is `Delta_j >= ~m a_j` (up to
  constants, since `1 - e^-x` is comparable to `x` for `x <= 1`). That is a
  physical mass gap `Delta_j / a_j >= m` uniform along the trajectory: a
  LATTICE-LEVEL MASS GAP.
- **Upper half.** `1 - r_j <= M a_j`. The lattice gap must close at exactly the
  spacing rate (the correlation length in lattice units diverges like `1/a_j`).
  This is the continuum-approach condition; without it the "gap" can be a
  strong-coupling artifact.
- **Physical meaning of a_j.** Calling `a_j = 2^-j` physical needs the open
  `NomeScheduleAFJustified` (schedule matched to the AF calibration).

Suppose a w>1/2 producer kept the existing formula `1-q(w) = 1/(2+6C(w))`.
Then the band reduces to the scalar B04q target
`m <= 2^j/(2+6C(w_j)) <= M` (equivalently `L <= s_j (2+6C(w_j)) <= U`). Under
`dyadicNomeSchedule` (`1-w_j = 2^-(j+1)`) that reads `C(w) ~ 1/(1-w)`. A real
producer must also replace the fixed-base tail absorption: it needs a
w-dependent base `K0(w)` together with a head constant whose growth is exactly
`Theta(2^j)` along the schedule. That combination is the mass gap of the
lattice cube transfer, and nothing here proves it. The cube carrier is
SU(2), extent one; no theorem links it to the all-nome Wilson carrier of A03.

## Declarations

| Declaration | Source | Role |
| --- | --- | --- |
| `NormalizedAnchorData` | `lean/YMGap/Continuum/BF4WilsonAllNomeGenericNormalizedAnchor.lean:210` | Generic anchor data (items 1-3). |
| `normalizer`, `normalizerCauchy`, `normalized`, `normalizedSector`, `bondExcitation`, `halfPreimage`, `MacroRatio` | `:232-256` | Generic constructions; macro-ratio predicate. |
| `normalizer_nonnegative`, `normalizes`, `response_pin`, `normalized_norm`, `normalizedSector_pin`, `bond_value`, `bond_norm`, `halfPreimage_pin` | `:260-306` | Generic pins. |
| `halfPreimage_norm_cleared` | `:313` | Generalized line 115. |
| `block_floor` | `:325` | **Generalized line 132.** |
| `mesh_increment_bound`, `real_increment`, `real_forward_increment` | `:358,416,434` | Generalized increments. |
| `real_floor` | `:450` | **Generalized RealSurvival line 148.** |
| `unitAnchorData`, `unit_macroRatio` | `:495,507` | Original data as an instance. |
| `unit_*` (six corollaries) | `:521-607` | Original statements reproved from the generic theorems. |
| `kernelCSum`, `kernelCSumCauchy`, `responseSum_mk` | `:627,637,643` | Concrete kernel sums with Cauchy data. |
| `repOrbit`, `repOrbit_class`, `familyStream`, `familyStream_class` | `:666-686` | Representative orbit recursion. |
| `smoothedSector`, `smoothedSector_pin`, `smoothedNorm`, `smoothedNormCauchy`, `smoothedNorm_pin` | `:692-717` | Range witness and norm data for Y_M. |
| `smoothedAnchorData`, `smoothedAnchor_macroRatio` | `:729,742` | Y_M as anchor data; ratio identification. |
| `pathKappa_pos`, `trajAnchorData`, `pathAnchor` | `:751,756,767` | Trajectory instance. |
| `path_anchor_floor` | `:774` | H1 gives the true floor. |
| `path_normalized_anchor` | `:822` | **Bridge-free A03 path theorem (H1 only).** |
| `path_normalized_anchor_with_survival` | `:864` | H1 + H2 variant. |
| `PathPhysicalContractionBand` | `:895` | **OPEN** w -> 1 contraction band. |
| `pathCubeContraction_of_band`, `rateBand_of_pathPhysicalContractionBand`, `pathPhysicalContractionBand_of_rateBand` | `:902,909,924` | Links to P6 and B04l. |

## Open Props

- `PathEpsBound` (H1, from P6): still OPEN, and the only hypothesis of the A03
  path theorem.
- `PathFamilyRadiusSurvival` (H2, from P6): still OPEN, and used only for the
  appended un-normalized floor.
- `PathPhysicalContractionBand` (NEW): OPEN, a characterization only. It is
  consumed by the two link theorems, and nothing proves it.

## Honest strength assessment

- **Exact port.** The generic theorems have the SAME strength as the
  originals: the same constants (`kappa^j`, `kappa^(j+1)`, the radius
  `macroGeometricRadius`), and the same one-block slack. The six corollaries
  reproduce the original statements verbatim.
- **What normalization hides.** As with the unit anchor, the raw anchor norm
  `R_j(2 side_j)` may collapse relative to `B(x_j,x_j)`. The normalizer
  `alpha_j` is not uniformly bounded. The floor
  `kappa^2 (M_j+1)^-2 varianceFloor(w_j) sum c^2` degrades with j, but it is
  used ONLY to build `alpha_j` and does not enter any conclusion. The
  normalized outputs therefore say nothing about non-collapse of `Y_j`; that
  is what H2 (or P6's absolute variant) adds, in the separate conjunct.
- **H1 carries all the content.** It is scale-invariant, not known vacuous,
  and hides the `path_rate_screen` necessity (P6 audit). The nome schedule's
  monotonicity, limit and AF justification are still consumed by no theorem.
- **Domain restrictions.** The real floor is vacuous at `i = 0` (no positive
  time has geometric size 0); every `i >= 1` is inhabited. The increment
  modulus needs `j >= 1` (`side j >= 2`, even).
- **Hidden strength.** None was found. No hypothesis encodes a unit-state
  property. Items 1 and 3 are constructions; item 2 is proved from H1.
- **The contraction Prop is a reformulation, not progress.** It is
  equivalent to a B04l rate band on the trajectory family, and its lower half
  IS a lattice mass gap. It is stated to make the w -> 1 requirement precise.

## Verification boundary

Each Lean run went through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 8 --check`, via a wrapper that refused to start while
any other Lean/lake/safe_lean_build process existed. A 10 s sampler stood
ready to abort on memory-pressure level >= 2 or available RAM < 8 GiB.

Accepted final run (p7final): exit 0, with no error, warning or sorry. There
are 42 `#print axioms` gates. 41 report `[propext, Quot.sound]`; 1 reports
`[propext]` (`pathKappa_pos`). The olean was emitted to
`lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeGenericNormalizedAnchor.olean`.

- Resources: peak load1 13.23, peak pressure level 1 (normal), minimum
  available RAM 19978 MiB, swap 0.
- Logs (Mac, outside the repo):
  `~/ymlean_prover_scratch/logs/check-p7final-20261005-202420.out` (SHA256
  `381c620ad601a0f2bccecdafb0eaccb6e6db1f9dadba2a3fe34b5145669269d8`) and
  `~/ymlean_prover_scratch/logs/mem-p7final-20261005-202420.log`.
- Final source SHA256 (`BF4WilsonAllNomeGenericNormalizedAnchor.lean`):
  `aef149a303a73a2105ba3453713f4b2d49e547c906af44a37f1f418bb23b5dfa`.

Earlier run p7a was on the identical source, without olean output: exit 0,
the same 42 gates, peak load1 10.60, pressure level 1, minimum available RAM
20556 MiB.

`scripts/lean_forbidden_token_scan.py` reported 0 executable hits. The import
is registered in `lean/YMGap.lean`; registration is not root verification. No
full/root build, full audit, guard, broad metrics run or CI was used. The
commit adds no new sorry, axiom, classical shortcut, noncomputable
declaration, frontier change or replacement carrier.
