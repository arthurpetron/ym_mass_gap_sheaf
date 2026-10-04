# Coherent original signed-family energy

Two final focused checks passed. This is an exact finite SU(2) family producer
and its original complete-energy consumer, not a variance-relative or scaling
estimate. The unchanged whole-project goal remains continuum Yang--Mills on
R^4 for every compact simple group, with same-theory QFT axioms and a positive
physical mass gap.

## Mathematical increment and actual consumer

For the literal signed family F=spatialSpan(width,c,qs), retain the row list
qs.filter(blockRow(width,b)), including repetitions. At each original physical
link, rotate each incident four-link word and conjugate its tail for inverse
incidence. Let R_b be the weighted sum of these actual tails and F_b the
incident span. Sum tails BEFORE taking their quaternion norm. The checked
identity, against EVERY full Haar insertion, is

```
Gamma_b(F) = 4*norm(R_b) - F_b^2.
Gamma_all(F) + sum_b F_b^2 = 4*sum_b norm(R_b).
```

No unmatched face or cross-plane term is omitted; no Nodup restriction or
coefficient sign assumption is imposed. The subtracted square is F_b^2,
NOT the whole family's F^2. Each tail's selected-link independence is proved
from actual edge membership and original index injectivity. The aggregate
tail is not asserted unit: its entire norm, including all signed cross terms,
remains. All original blocks are selected by actual list indexing, with a
proved index pin; no fallback coordinate enters the original range.

Keep the actual family spectator schedule and projected V*g_depth source:

```
a_z = channelSource(ids, projectedEndpointSource(V*g_depth), z)
Q   = sum_z lambda_z * H[a_z^2 * sum_b F_b^2]
P   = sum_z lambda_z * H[a_z^2 * 4*sum_b norm(R_b)]
E + (1-w)*Q = (1-w)*P + familyChannelTaylorDebt.
```

E is the COMPLETE original temporal energy. BOTH actual signed Taylor
remainders remain, with the original cutoff and active kinetic factors.
The last equality requires existing strict spatial padding; equality otherwise
needs no nome positivity, positive depth or nonzero-source premise. Q>=0 is
constructed for w>=0, allowing cutoff zero and zero channels. Favorable
subtraction additionally needs w<=1. Q is retained in the delivered identity;
the norm-only upper cap is not asserted to be a useful estimate. The actual
source-square weight is not identified with the odd marginal V*g*Tg or its
OWN centered variance.

| Declaration | Source | Role |
| --- | --- | --- |
| `faceCoherentTail` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:75` | Computed original four-link tail at every incidence. |
| `actual_face_tail_recode` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:183` | Coefficient-strength actual-face trace pin. |
| `incidentSpan_tail_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:285` | Literal signed/repeated row equals the trace of its aggregate tail. |
| `aggregate_tail_supported` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:314` | Actual full-carrier support. |
| `aggregate_tail_degree_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:334` | Constructed independence at the selected original link. |
| `family_coherent_row` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:383` | Exact row norm minus its incident span square. |
| `selectedLink_idxOf` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:74` | All original index selections are physically pinned. |
| `family_coherent_full_angular` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:163` | Complete original angular-block sum. |
| `family_coherent_channel_cancellation` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:199` | Every actual passive channel-source square. |
| `family_coherent_retained_square_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:244` | Computed Q>=0. |
| `family_coherent_energy_retained_square` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263` | Actual original complete energy, Q and BOTH signed debts. |
| `padded_family_channel_energy_taylor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance.lean:119` | Existing complete-energy expansion consumed without new hypotheses. |

## Backward screening and remaining analytic estimate

The next producer must estimate the COMPLETE signed combination
(1-w)*(P-Q)+TaylorDebt versus SAME surviving variance on a justified changing
family, with the correct chronological source and distinct partition factors.
The current angular formula does not itself give that estimate. Its existing
downstream response consumer remains `aggregate_window_macro_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`; its actual
signed-window budget is still unsupplied.

A read-only mathematical review also considered replacing the two-face higher
word moment by a source-derivative angular-IBP flux. That rewrite is not a new
checked theorem here and supplies no favorable sign. The original source
derivatives have already cancelled in `sourceFirstOrder_eq_weightedAngularEnergy`
at `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:91`.
Reintroducing them by IBP supplies no additional power of 1-w; the available
`projectedEndpoint_familyChannelAngular_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelRegularity.lean:91`
controls source derivatives by channel mass, not SAME surviving variance.
Accordingly this turn does not add another absolute derivative cap or assumed
anisotropy-budget wrapper. The signed combination is the analytic residue.

This proves arbitrary literal-family coherent GEOMETRY and its exact original
energy realization, not useful uniform family CONTROL. Chronological window
control, justified spacing/volume/coupling trajectory, nonzero continuum
survival, physical mass calibration, full OS/QFT and every compact simple group
remain open. Exact canonical chart claims remain unchanged; no chart reprint.

## Verification boundary

Accepted logs, each exit 0 with no warning/error and only permitted axioms:

- `/private/tmp/ym-family-coherent-tail-20261004-2.log`: ten printed gates;
  `faceCoherentTail` is axiom-free; remaining gates use {propext, Quot.sound}.
  SHA256 `ca711a2ce30c1b097de287ae68d90bc9033c7b93d087a2e434dc91b06c47ffd9`.
- `/private/tmp/ym-family-coherent-energy-20261004-2.log`: nine printed gates;
  each within {propext, Quot.sound}.
  SHA256 `5d41b462a1c7b262082f671d3ef7ceafc587850b31f332cc60dc0aa3ba9ca246`.

Final source SHA256:

- `BF4ExactSlabFixedSpatialFamilyCoherentTail.lean`:
  `2dcd69d6d214339df167126bafa2799bad5b35d739d989b944424cb70b6a4c64`.
- `BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean`:
  `2280a57871ef002c6eb9464a2341faedf281ad37fea63c5e0f167215dc5560ce`.

Earlier failed elaborations are rejected evidence. Final checks used one
monitored 20-GiB worker, 12-GiB reserve and fresh process/pressure/swap checks;
swap was zero. No heartbeat/resource inflation. Independent source review
passed. Root import registration is not root verification. No full/root build,
full audit, guard or broad metrics run; CI stays off. No new sorry, axiom,
classical shortcut, analytic field, weakened frontier or replacement carrier.
