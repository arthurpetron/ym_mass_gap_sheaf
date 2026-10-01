# Actual-mean radial energy under the original Wilson edge law

Date: 2026-10-01 UTC. PROVED supporting estimate after `4ba8766`.
Scope: one literal fundamental SU(2) Wilson trace, every supplied active word,
finite spatial width and terminal depth, and the computed heat-cutoff schedule.
This is not useful signed-family scaling or continuum Yang--Mills closure.

## The mathematical advance

Let f be the literal fundamental trace, d the squared quaternion chordal
distance between its ordered lower/upper words, and c the ACTUAL odd mean.
E below is the original normalized temporal energy, not a squared norm of
f-Tf. Write V for SAME oddVariance, L for normalized E_edge[d], and R for
normalized E_edge[d^2]. For every supplied rational t>=0,

    t*E <= t^2*V + (t+c^2)*R + t*(4-c^2)*L.

The previously unestimated mixed radial moment is eliminated from this
one-loop ceiling. The identity driving it is exact polynomial algebra:

    [t^2*(c-f)^2 + (t+c^2)*d^2 + t*(4-c^2)*d]
      - t*[d*(4-f^2)+d^2]
      = [t*(c-f)-c*d]^2 + t*d*(c-f)^2.

No square root, independence, factorized expectation, source concentration,
variance floor or replacement of the terminal law is needed. The generic
retained variant keeps the second term on the left of the inequality.
Dropping it uses t>=0 and the actual four-square certificate for d.

Both remaining chordal moments are paid under the SAME complete edge density:

    L <= L_word = 6*(1-w)*m^2,
    R <= R_log  = wordFourthFactor(m)*888*r^4*h^2,
    h = 2^(-6r), w = nome(2r) = 1-h, r>=22.

Here m is the actual ordered-word length, including repeated occurrences.
The new original-object consumer therefore proves

    t*E <= t^2*V + (t+c^2)*R_log + t*(4-c^2)*L_word.

The actual mean has c^2<=4, making the final coefficient nonnegative.
The source/variance comparison is retained explicitly, not assumed small.

## Causal declaration chain and SAME-object pins

1. `lean/YMGap/Continuum/QuaternionHaarRadialMeanYoung.lean:94`,
   `young_identity`, proves the displayed polynomial equality.
   `youngGapCertificate` (:105) returns its sum-of-squares witness.
   `young_retained_identity` (:115), `youngRetainedCertificate` (:124)
   and `weighted_young_moments_retained` (:244) retain the favorable square.
   `weighted_young_moments` (:275) exposes all rational moment coefficients
   under ONE supplied positive Haar weight, with t>=0 for the dropped term.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:182`,
   `edge_marginal_pairing`, exposes the already proved lower pairing and
   original transfer symmetry. It yields the marginal V_spatial*g*Tg,
   not V_spatial*g^2. Both source and insertion support are explicit.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMeanRadial.lean:75`,
   `edgeMoment`, divides ONLY by the original positive oddMass.
   `edgeMoment_pin` (:91) and `mean_pin` (:104) identify the lower endpoint
   moments and computed center with the existing middleRatio(depth+1,depth).
   `centered_edge_square_pin` (:176) identifies the actual centered square
   with the existing interacting oddVariance, not a free/Haar variance.
4. In the same module, `mean_square_le_four` (:205) uses the SAME literal
   Haar-unit ordered word and certified complete edge weight. The resulting
   `radial_coefficient_nonnegative` (:226) does not posit a near-vacuum mean.
   `wilson_energy_mean_moments` (:245) joins the exact Young bound to the
   existing `wilson_energy_radial_cleared`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonRadialIncrement.lean:117`,
   and `radial_moment_split`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonQuarticIncrement.lean:162`.
   The original factor two is canceled exactly before normalization.
5. `lean/YMGap/Continuum/QuaternionHaarWordQuadratic.lean:169`,
   `vector_square_bound`, adds all four component Cauchy certificates before
   charging the per-link bound. `word_norm_quadratic_bound` (:209) applies
   the actual ordered noncommutative word telescope. The cost is m^2 times
   the full link-norm budget, with no extra coordinate factor four.
6. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMeanQuartic.lean:73`,
   `word_quadratic_nome_cleared`, consumes the existing error-free active-link
   alignment under the SAME edge density and terminal source.
   `word_quadratic_nome_normalized` (:104) gives L_word, again dividing ONLY
   by the SAME positive partition. Support, physical word membership and
   activity of EVERY word edge are retained.
7. In the same module, `meanCutoff` (:114) computes
   `logCutoff r (sufficientCutoff(nome(2r))+stage)+1`.
   `meanCutoff_head` (:117) and `meanCutoff_kinetic` (:120) pay both the head
   and kinetic onsets. The shifted stage also satisfies the original
   logarithmic quartic producer's guards. `word_quartic_mean_normalized`
   (:125) pays R_log using that unchanged producer.
   `wilson_energy_mean_log_budget` (:144) is the final explicit estimate.

## Parameters, residue and the next consumer

The new rates depend explicitly on nome/diagnostic index and ordered length;
the estimate also retains the actual mean, variance and supplied t. Width and
terminal depth do not add a separate multiplier. The computed cutoff onset
depends on nome and split. These statements do not construct a completed map
between widths, a changing-observable limit or a beta/spacing trajectory.

This removes an unevaluated mixed moment, NOT the primary useful COMPLETE
signed energy/SAME-interacting-variance input. A whole signed family is not
a single unit-quaternion trace with cap four; its cross-word cancellations
cannot be inferred from this result. Existing plaquette-family variance floors
are proved, but their conservative calibration does not supply the required
relative comparison with R_log and the mean correction. In particular,
c^2<=4 does not say that 4-c^2 is scaling-small relative to SAME variance.

The next mathematical input is useful relative calibration of the actual
mean correction and quartic remainder on a justified family, or a combined
cancellation-preserving original signed-family estimate. No additional
equivalent survival wrapper or analytic frontier field was added.

OPEN: controlled spatial/coupling/spacing passage, nontrivial continuum
excitation survival, physical time and positive finite mass calibration,
full SAME-theory continuum OS/QFT, Yang--Mills local-field/short-distance
identification, and every compact simple group. No canonical field, guard
or displayed chart claim changes. The unchanged ASCII chart is not reprinted.

## Focused verification and independent review

Five accepted focused checks emitted their target oleans and passed
11+8+3+8+8=38 printed gates. Three have empty axiom sets, one uses only
propext, and thirty-four use exactly {propext, Quot.sound}. The final
consumer was checked after correcting the cutoff equality's unfolding order;
the four preceding accepted checks cover its unchanged new dependencies.
Failed draft logs are not proof evidence. No new sorry, axiom, Classical,
native_decide, noncomputable declaration, erased witness, weakened frontier
or substitute density was introduced.

Sol independently reviewed the square identity, original factor-two
cancellation, complete edge/center/variance pins, vector cost and guards.
Luna independently matched every accepted source gate to its log, counted
axiom sets, checked forbidden source constructs and all five log hashes.
No reviewer ran a compiler for this final review; main alone serialized
the accepted checks through `scripts/safe_lean_build.py --jobs 1` with a
20 GiB worker ceiling, unchanged 12 GiB OS reserve and dynamic telemetry.
Current preflight found 83 percent pressure-free memory, zero swap and no
competing Lean/Lake/pytest/GitHub runner. External user-owned reliability
study processes were left untouched. No safety or heartbeat limit was raised.
Final telemetry remained pressure-free with zero swap.

No full root/tree build, broad audit or guard ran. Root imports are registered,
not checked in aggregate; the axiom baseline is not regenerated. CI remains
manual-only. Documentation and whitespace checks accompany the checkpoint.

Accepted logs and SHA-256:

- `/tmp/ym-original-edge-marginal-public-20261001.log`:
  `55439db61295f4e723d4de24d56f5244043433576bd83290466f67126ef9b613`.
- `/tmp/ym-radial-mean-young-second-20261001.log`:
  `a31f03ebf386521163f81d15fd1a7405ae06d579db803262b43ec1ed8b376230`.
- `/tmp/ym-word-quadratic-final-20261001.log`:
  `f6960ccee50f6ecf34a548aa5e43d054b4ff4aa286e01f580237ec36758ee323`.
- `/tmp/ym-wilson-mean-radial-sharp-20261001.log`:
  `733a4332d19bdc96ea4fe4fe1760a778fe3de65915f859731a87252daaa39a36`.
- `/tmp/ym-wilson-mean-quartic-accepted-20261001.log`:
  `218b99fd731010ecc11ba53e4c8f2f1b07ee94b6992339cf00a7986068ebad79`.
