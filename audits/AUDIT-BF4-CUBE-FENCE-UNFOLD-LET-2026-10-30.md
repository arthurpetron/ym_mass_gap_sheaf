# Audit: BF4CalibratedCubeSpectralFence line-358 proof-step fix (2026-10-30)

`physicallyRecentered_cube_defect_le_rowMass` ended with
`unfold physicalCenteredEndpointRowMass finiteJointDifferenceAbsRowMass endpoint`.
`endpoint` is a local `let` (line 315), not a global definition; by the time
of the `unfold` it is already substituted in the goal, so Lean 4.29.1 rejects
`unfold endpoint` ("failed to unfold `endpoint`"). Fix: drop `endpoint` from
the `unfold` list. Proof-step only; no statement change, no new tactics.

Checked under safe_lean_build.py (--jobs 1, 8 GiB ceiling, LEAN_NUM_THREADS=2,
nice 10): targeted +olean build rc=0 (70 s, ~5.6 GiB), --check rc=0.
`#print axioms`: physicallyRecentered_cube_entry_eqv,
physicallyRecentered_cube_defect_le_rowMass,
physicallyRecentered_cube_defect_le_rate_mul_marginal and
not_physicallyRecentered_rate_le_eighth_of_cube_defect: [propext, Quot.sound].
