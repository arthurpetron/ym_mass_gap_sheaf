# Whole signed-family kinetic upper on the original completed carrier

Date: 2026-10-01 UTC. PROVED supporting estimate after `855b0c3`.
This is an absolute temporal-energy estimate, not the missing useful
SAME-interacting-variance estimate on a continuum scaling family.

## Actual mathematical result

For any supplied signed plaquette family on a strictly padded spatial patch,
put `L1 = listQSum (fun p => Q'.abs (c p)) qs`. On its ORIGINAL all-nome
Wilson completion, with `v` the actual centered family and `T` its actual time,

    B(v,v) - B(v,T(1)v) <= 192*(1-w)*L1^2,
    B(v,v) - B(v,T(n)v) <= 192*n*(1-w)*L1^2   for every natural n.

The alternative Cauchy ceiling is `192*(1-w)*qs.length*sum(c_p^2)`.
No distinctness, positive depth, coefficient sign or nonempty-list premise
is needed. A repeated face retains its positional multiplicity. No separate
list-length factor enters the L1 ceiling, but the coefficient sum itself
can grow with family size. Zero-coefficient padding does not enlarge it.

The coefficient has no width, heat-cutoff, terminal-depth or endpoint
floor/cap factor. It DOES depend explicitly on the nome `w`, coefficients
and the supplied list; the multi-step ceiling also depends on `n`.
`cutoffOnset(w) = max 1 (sufficientCutoff w)` applies to stages of the
original cutoff `headCutoff w + k`. Each completed limit fixes `w` and width.
Neither a beta/spacing trajectory nor a completed map between widths is
constructed here.

## Causal declaration chain

1. Existing error-free SU(2) alignment supplies the original active-link
   displacement ceiling `6*(1-w)*oddMass`:
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialExactKineticAlignment.lean:106`,
   `exact_link_displacement_nome_bound`. This alignment was already proved;
   this milestone constructs its whole-family and completed consumers.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:250`,
   `wilson_energy_of_link_budget`, consumes an arbitrary proved link budget
   under the SAME complete original edge density. Unit-quaternion word
   telescoping pays squared path length and the trace-square factor four.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyKineticUpper.lean:83`,
   `oriented_displacement_bound`, retains link orientation. Its
   `wilson_energy_nome_bound` (:101) yields `2E <= 24*(1-w)*length^2*Z`.
   `face_jump_bound` (:127) uses all four active edges provided by strict
   padding, giving the common diagonal jump ceiling `384*(1-w)*Z`.
4. `family_jump_sum` in that module (:184) identifies the COMPLETE signed
   jump before squaring. `weighted_sum_square_le` (:196) and
   `family_energy_nome_cleared` (:220) give the explicit list-length Cauchy
   cost. `family_energy_nome_normalized` (:266) divides only by SAME `Z`.
5. `lean/YMGap/Continuum/QuaternionHaarUniformFamilyCost.lean:57`,
   `normalized_pair_abs_le`, uses constructive normalized Cauchy--Schwarz
   and rational Young, including zero ceilings. `normalized_family_l1_cost`
   (:103) expands the literal ordered Gram sum, bounds every mixed entry,
   and sums the absolute coefficient products. It assumes neither disjoint
   faces nor zero interference. It applies to one square-certified positive
   weight, not a substituted marginal.
6. `family_energy_l1_normalized` in the finite kinetic module (:290)
   instantiates that result with the ORIGINAL `edgeDensity`, its actual
   `edgeCertificate` and `edge_total_mass = oddMass`. Reciprocal congruence
   identifies the normalizers. The full original squared jump remains on
   the left; the L1 ceiling on the right does NOT exploit signed cancellation.
7. In `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyKineticUpper.lean`,
   `finite_family_energy_nome_bound` (:100) and `finite_family_energy_l1_bound`
   (:153) use the existing `finite_family_energy_pin` to identify the actual
   finite energy sequence, then halve `384` to `192`. The existing energy
   CReal/modulus gives `family_energyLimit_nome_bound` (:135) and
   `family_energyLimit_l1_bound` (:176). `completed_family_energy_nome_bound`
   (:142) and `completed_family_energy_l1_bound` (:183) rewrite through
   `energyLimit_completed_pin` to the ORIGINAL centered time-loss form.
   This form is not the squared norm of `v-Tv`, nor the physical bond norm.
8. `time_loss_linear_bound` in the completed module (:233) holds for EVERY
   state of this same carrier. Existing `mixedMoment_split` telescopes
   the increments and `mixedMoment_time_decreasing` bounds each by the first.
   `completed_family_time_l1_bound` (:259) applies that theorem to the actual
   family, including the exact zero-time case.

## SAME-object pins and open residue

The normalization is the original positive central-edge partition at the same
nome, cutoff, width and terminal depth. `finite_family_energy_pin` is in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondFloor.lean:147`.
The constructed energy's completed pin is
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218`,
`energyLimit_completed_pin`. No fresh limit, center, action, scalar variance,
operator, inverse, representative choice or analytic hypothesis is supplied.

A SAME completed family variance floor already exists:
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`,
`familyExcitation_norm_floor`. Its conservative coefficient is NOT adequate
to calibrate this absolute upper. The existing checked obstruction
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:102`,
`computedLossRatio_ge`, puts the available single-face upper/floor quotient
at least `115200`; `sixHundred_floor_le_defect_power` (:75) bounds the
particular floor by `(1-w)^48/600`. These are statements about computed
certificate numbers, not lower bounds on actual energy or upper bounds on
actual variance. No Yang--Mills counterexample is inferred.

NEXT remains useful control of the COMPLETE signed original energy relative
to SAME interacting variance on a justified changing-coupling/spatial/spacing
family. An absolute coefficient budget is not that input. Nontrivial continuum
survival, spatial/spacing control, physical-time/mass calibration, full
continuum OS/QFT, field/short-distance identification and every compact simple
group remain OPEN. No canonical field, guard or displayed chart claim changed;
the unchanged ASCII chart is not reprinted.

## Verification boundary

Four accepted focused checks exited zero and printed `10+3+8+13=34` axiom
gates. Seven are axiom-free; the other twenty-seven depend exactly on
`{propext, Quot.sound}`. No source `sorry`, new axiom, classical dependency,
`native_decide`, `noncomputable` or weakened frontier was introduced.
Independent Sol mathematical and Luna source/log reviews passed.

Main alone compiled, serialized through `scripts/safe_lean_build.py` with
one worker, a 20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry.
Preflight found no competing compiler/runner/test process, 84 percent
pressure-free memory, and zero swap. Final swap was also zero. No limits
were raised. Missing namespace/equality helpers and one dependent rewrite
were repaired before acceptance; failed logs are not proof evidence.

No full root/tree build, broad audit or guard ran. Root imports are registered,
not checked in aggregate. CI remains manual-only.

Accepted log SHA-256 values:

- `/tmp/ym-wilson-original-link-budget-20261001.log`:
  `135b4945a954aebfec96f84abb54c1c7e22a33f31ca8d046a5d0211fb011c836`.
- `/tmp/ym-haar-uniform-family-l1-second-20261001.log`:
  `7733af2858bd906beda7a8f5b706e61f198fb80342fa4b972398e916400bed3f`.
- `/tmp/ym-original-family-kinetic-l1-second-20261001.log`:
  `675e62025a0ea35d4c9ddad9362467c7cdba0f780c7ddc429265025eab012625`.
- `/tmp/ym-completed-family-time-l1-final-20261001.log`:
  `b83a4b255233bbbe1e8da70fa02e978e59b295b4d6ac3e9de7042d8d24d06c35`.
