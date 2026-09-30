# Original sector insertions, boundary obstruction and nonzero domain source

Date: 2026-09-30 UTC. Classification: PROGRESS. Four focused checks certify
the statements below on the original all-nome Wilson completion. Physical
OS identification, scaling survival and the Clay target remain OPEN.

## Mathematical result

Write T for the original one-step transfer, S(t) for its constructed
positive-real-time action, M for the literal Wilson multiplier, and Omega
for the original unit. The sector retains explicit witnesses for the
closure of the original T range; no new ambient carrier is substituted.

At width one, the previously constructed centered origin plaquette v has
positive norm and Tv=0. A witnessed range state in ker(T) is zero, hence
v has no sector witness. The unit projection of the raw plaquette has a
sector witness with its computed scalar modulus. Therefore the raw
plaquette M Omega cannot have one either: subtracting its unit component
would put v in the sector. In particular, there is NO sector endomap
agreeing everywhere with this literal time-zero multiplier. This rules
out direct restriction, not physical OS reconstruction or a continuum
theory. The boundary kernel is retained.

The positive-time insertion S(t) M S(t), t>0, DOES act on the witnessed
sector. Carry the actual Cauchy representative through the inner time
action and multiplier; the outer time action constructs the range witness.
There is no premise that M preserves the sector. Symmetry, real linearity
with supplied scalar moduli, and the spin-only squared-norm cap follow
from the original operators. This construction is not an algebra
homomorphism and does not assert positivity of M.

S(t) fixes Omega, so the created state is exactly S(t) times the original
loop. Its autocorrelation at integer insertion time n>0 and lag k is the
original loop moment at (n+k)+n. Centering with the SAME unit projection
commutes with S(t); the resulting vector is exactly S(t) times the original
centered loop, and its lag is the original CONNECTED moment with both
external time shifts. Neither the normalization nor the operator changes.

For a fully active plaquette, the time-one centered source belongs to the
actual derivative core and has squared norm at least the existing
absoluteFloor = uniformFloor^2/4. Padding the origin to width padding+2
supplies activity and returns a concrete domain point, a positive rational
floor, its vacuum orthogonality and its norm bound as data. The floor
depends on the original nome and width; this is NOT scaling survival.

## Checked source map

Names in the declaration column have the namespace of the listed module.

| Declaration | Source | Exact role |
|---|---|---|
| `meshAction_unit`, `positiveAction_unit` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeVacuum.lean:59`, `:68` | Actual dyadic and positive-real actions fix the original vacuum. |
| `positiveAction_vacuum_pairing`, `positiveAction_preserves_vacuum_complement` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeVacuum.lean:84`, `:95` | Same unit pairing and orthogonal complement. |
| `origin_centered_not_range`, `origin_raw_not_range` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorObservableBoundary.lean:55`, `:92` | Explicit width-one obstruction, using the existing nonzero kernel state. |
| `unitRange`, `originProjectionRange` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorObservableBoundary.lean:66`, `:76` | Computed original witnesses for the unit and raw loop's projection. |
| `no_original_multiplier_sector_map` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorObservableBoundary.lean:107` | Refutes literal time-zero multiplier restriction. |
| `sandwich`, `sandwichRange`, `insertion`, `insertion_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorInsertion.lean:68`, `:73`, `:83`, `:90` | Actual S(t) M S(t), explicit range witness, extensional sector action. |
| `sandwich_add`, `sandwich_realSmul`, `sandwich_symmetric`, `sandwich_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorInsertion.lean:95`, `:102`, `:109`, `:116` | Original real-linear symmetric bounded insertion. |
| `sandwich_unit`, `sandwich_unit_original`, `sandwich_unit_lag` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorInsertion.lean:127`, `:133`, `:140` | Literal original vacuum source and shifted correlator. |
| `positiveAction_unitProjection`, `centeredPart_positiveAction` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorExcitation.lean:71`, `:79` | Original computed centering commutes with positive time. |
| `centeredSource`, `centeredSource_insertion_pin`, `centeredSource_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorExcitation.lean:86`, `:93`, `:99` | Witness-bearing same-insertion centered state. |
| `centeredSource_original`, `centeredSource_lag` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorExcitation.lean:105`, `:112` | Exact original-time and connected-moment pins. |
| `sourceDomain`, `sourceDomain_pin`, `sourceDomain_norm_floor`, `paddedDomainCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorExcitation.lean:122`, `:125`, `:132`, `:143` | SAME nonzero centered domain source with positive floor as data. |

## Scope and causal residue

The downstream physical reconstruction cannot use a silent restriction of
the time-zero observable algebra to this sector. These positive-time
insertions are valid concrete bounded maps, but a physical reflected
observable realization and its algebra/complex-Hilbert compatibility still
need an exact SAME-object join. No canonical frontier field is closed or
weakened here. The integer-time pins concern original lattice-time units.

The source review must not mistake this residue for missing finite-word
generation: `BF4WilsonAllNomeWindowRealization.compileWindow_pin` in
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:103` already
pins EVERY bounded signed multi-time Wilson expression to its actual
completed chronological program. `commonForm_nonnegative` and
`intrinsicForm_nonnegative` in
`lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:149` and `:190`
already give original reflection positivity. The downstream
`PositiveTimeOSRoot` in `lean/YMGap/Continuum/CanonicalOSRoot.lean:268`
instead requires supported representatives, reflected-form equality and
time-translation compatibility in its SAME `CanonicalSchwingerLimit`
algebra. The finite pins do not construct that canonical limiting input.
This is source review, not a new proof or a claim that this legacy target
alone suffices for the Clay problem.

Independently, the primary analytic residue remains a useful signed
temporal-energy/variance upper estimate on a justified scaling family.
The fixed-nome/width source floor here supplies no uniform continuum
survival, physical mass calibration, thermodynamic/spacing passage,
Yang--Mills local-field/UV identification or all-group theorem.

## Verification and review

Four final focused serialized checks passed 34 printed gates: 4 for
PositiveTimeVacuum, 11 for SectorInsertion, 8 for SectorObservableBoundary,
11 for SectorExcitation. Every printed dependency set is exactly
{propext, Quot.sound}. No new sorry, custom axiom, classical choice or
frontier weakening. Initial local elaboration errors in quotient notation
and an implicit centered-vector argument were fixed before final checks;
Type-valued range negation is explicitly a function to False.

Luna drafted the vacuum laws; Sol drafted the boundary argument and
independently reviewed the insertion/excitation scope. Main corrected the
drafts, proved the insertion and centered-domain construction, and ran all
checks. The safe-build skill kept verification narrow: one worker, 20 GiB
hard cap, 12 GiB OS reserve, live process/memory preflight and automatic
telemetry. No competing compiler, safety stop, raised limit, full-tree/root
build, broad audit/guard or progress script. Root import registration is
not root verification. The canonical chart remains unchanged.

Final logs and SHA-256:

- `/tmp/ym-wilson-positive-time-vacuum-20260930.log`:
  `8d25ff690b6cb5468d48e7fd1350f45bde40be1f2f5cda9897023dc1982f6bd8`
- `/tmp/ym-wilson-sector-insertion-20260930.log`:
  `61c052012837fd2c94b92562f276e3b7ea832e5596f31b1d8a988b4ee9142db4`
- `/tmp/ym-wilson-sector-observable-boundary-20260930.log`:
  `dc732ecb4a81154938c42abb66ae89623cf5999facc9ec6bc124d0b49b3591e3`
- `/tmp/ym-wilson-sector-excitation-20260930.log`:
  `90515a3d7d286af8eac474e4ddef3afc7da06ca3781950402cb8b06c09892b8e`
