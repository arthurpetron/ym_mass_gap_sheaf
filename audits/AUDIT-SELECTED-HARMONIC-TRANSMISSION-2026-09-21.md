# All-label selected-factor transmission in the actual product kinetic map

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with same-theory QFT axioms, isolated vacuum and finite positive physical
mass gap. This is a finite SU(2) kernel identity, not a gap estimate.

## New exact join

The preceding checkpoint proved all-degree harmonic reproduction only for
the exposed head/retained pair. The new result transports it through the
explicit swaps and removes one factor of the ACTUAL product kernel while
retaining the others. Write

    P = productMap(n,w,K,i::ids),
    R = productHeat(n,w,K,ids),
    J_i(p) = undoPairSwaps(liftHead(S(exposePair(p)))),

where S is the checked retained-link substitution after dropping the head.
For a supported lower input p of selected-block degree d, harmonic in the
explicit selected-pair chart, and an arbitrary supported upper test g:

    H_n[g * P(p)]
      = if d <= K then w^(d*(d+2)) *
          H_(2n)[R * (J_i(p) * liftBoundary(n,g))]
        else 0.

Every index of ids lies below n, and i is not in ids. No further
independence among retained variables or remaining factors is assumed.
The output J_i(p) may contain both lower and upper variables: the theorem
correctly leaves it in the doubled integral, not as a lower-only input.
The name P here denotes the actual product kinetic map, NOT the full
interacting transfer P(V*f) or an OS Hamiltonian.

## Hypotheses and same-object safeguards

- Support is syntactic finite coordinate support. It is required for the
  original input/insertion and proved for the constructed substitution,
  lifted output, reverse swaps and resulting image. Thus finite Haar
  reindexing does not silently truncate a variable.
- `HasQuaternionBlockDegree i.val d p` is at the ORIGINAL selected block.
  Harmonicity is `RatPolyCoeffEqv (headLaplacian (exposePair p)) polyZero`
  in the displayed explicit swap chart. This is a checkable polynomial
  property, not an assumed heat-propagation identity. No separate general
  block-Laplacian transport theorem is asserted by this result.
- The arbitrary selected-pair insertion must be supported and of degree
  zero only in the block being integrated. In the product-map consumer,
  that property is constructed for R times the upper lift of g using the
  existing untouched-factor independence lemmas.
- Both directions of the reversed swap chain are prefix-identical, not
  falsely equal as unpadded exponent lists. The original radius/Haar and
  coefficient conventions remain unchanged.
- The label, nome and cutoff are explicit. There is no positivity guard
  or uniform estimate hidden in this finite identity; the case d>K is zero.

## Source map

| Declaration | Source | Content |
| --- | --- | --- |
| `apply_reverse_inverse_prefix` | `lean/YMGap/Continuum/SU2QuaternionBlockSwapChainInverse.lean:44` | Forward chain cancels its reversed chain at prefix strength. |
| `reverse_apply_inverse_prefix` | `lean/YMGap/Continuum/SU2QuaternionBlockSwapChainInverse.lean:63` | Opposite inverse direction. |
| `apply_reverse_inverse_haar` | `lean/YMGap/Continuum/SU2QuaternionBlockSwapChainInverse.lean:96` | Same-carrier inverse with an arbitrary supported insertion. |
| `retainedImage` | `lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:42` | Explicit substitution followed by empty-head reinsertion. |
| `substituteRetained_supported` | `lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:84` | Substitution output has the required finite tail support. |
| `retainedImage_supported` | `lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:94` | Reinserted output stays on the original full carrier. |
| `harmonic_transmission_same_carrier` | `lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:113` | Local reproduction under an arbitrary head-independent insertion. |
| `transmittedImage` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:51` | Computed image in the ORIGINAL coordinate order. |
| `selected_pair_harmonic` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:65` | Arbitrary distinct original pair, support, chart harmonicity and cutoff. |
| `selected_pair_harmonic_at` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:124` | Arbitrary block count without dependent predecessor casts. |
| `kineticPairSteps` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:142` | Actual lower/upper kinetic pair chart. |
| `productHeat_selected_harmonic` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:149` | One selected factor removed, with every other factor retained. |
| `productMap_selected_harmonic` | `lean/YMGap/Continuum/SU2QuaternionSelectedHarmonicHeatTransmission.lean:193` | Direct consumer on the actual original product kinetic map. |

The final join uses `productMap_pairing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`,
and the selected-pair join uses `heat_exposed`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatPairGeometry.lean:89`.
No substitute kernel, truncated list of spins or independent interacting
action is introduced.

## Remaining mathematics

The all-label selected-factor algebraic join recorded in the preceding
harmonic-reproduction audit is now proved. A constructive decomposition
of the actual input `activeSpatialWeight * terminalMessage * observable`,
and its compatibility with repeated factor use, still have to be supplied.
This theorem does not show that the weighted input is one harmonic mode,
nor that a single fixed-degree result controls the changing family as K
grows. The original terminal-source reduction `energy_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`,
already retains both original terminal messages and remains the intended
consumer to reuse, not reconstruct.

The finite-time comparison must preserve the full endpoint weight and
signed cross terms. No useful SAME-variance small rate, cutoff/trajectory-
uniform control, spatial/scaling survival, physical mass calibration,
canonical full OS/QFT or every-group realization follows here. Inactive
kinetic slots remain Haar projections. No canonical field, analytic
premise, hole or axiom was introduced, removed or weakened.

### Next-input inventory

The existing exact polynomial identities include
`headEuler_of_blockDegree`,
`lean/YMGap/Continuum/SU2QuaternionRatPolyDifferential.lean:788`,
`headGradientDot_headRadius_left`, same file at line 1664, and
`headLaplacian_mul`, same file at line 2317. These are available algebraic
inputs, not a packaged harmonic decomposition.

The existing `homogenizeQuaternionPolynomial`,
`lean/YMGap/Continuum/SU2QuaternionArbitraryHaarHomogenization.lean:1006`,
raises individual terms using radius powers. Its preservation theorem
`quaternionHaar_homogenizePolynomial_pair`, same file at line 1461,
is a Haar-pairing identity, not a coefficient-level harmonic decomposition.
Likewise `headSector`,
`lean/YMGap/Continuum/SU2QuaternionHeadHaarSquareCertificate.lean:228`,
splits parity, not exact degree or harmonic components.

The next construction is an exact-degree splitter and finite constructive
Fischer recursion with reassembly and support proofs. It must then be
connected to repeated selected-factor transmission and the actual weighted
source. This is a plan, not a proved decomposition or signed-mode estimate.

## Verification and division of work

Three final focused checks passed 15 printed gates (6, 4, 5), all within
`{propext, Quot.sound}`. The dependency-complete target
`+YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission:olean`
passed. Final focused logs and the final consumer build log contain no
errors, warnings, classical dependencies or `sorryAx`. The safe-build
skill kept checks serialized with one capped 20 GiB worker. No full-root
build, full-tree audit or guard was run. Automatic CI remains manual-only.

Final logs:

- `/tmp/ym-gap-block-swap-chain-inverse-check.log`
- `/tmp/ym-gap-harmonic-heat-insertion-check.log`
- `/tmp/ym-gap-selected-harmonic-transmission-check.log`
- `/tmp/ym-gap-selected-harmonic-transmission-build.log`

Sol supplied the bounded inverse-chain draft. Main supplied actual
substitution support, full-carrier reproduction, selected-pair/product-map
composition, integration fixes and serialized verification.
Sol's independent read-only review passed for the three modules: it
confirmed the explicit chart-harmonicity hypotheses, constructed original-
carrier output, proved support and retention of remaining supported
factors. It also distinguished the existing homogenization and parity
split from the still-missing harmonic decomposition.
