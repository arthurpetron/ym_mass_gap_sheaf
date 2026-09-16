# Geometric comparison brackets for the original finite-chain scalar

Date: 2026-09-16. Classification: PROGRESS after `aea5cde`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, on the SAME theory, within the constructive axiom gate.
The finite-spatial comparison below does not establish that target.

## Mathematical argument and its actual consumer

Fix rational 0<w<1, spatial width and K>=headCutoff(w). All functions are
on the original polynomial slice carrier and use the actual transfer
T_K f(y)=H_x[K_K(x,y)V_K(x)f(x)]. Put

    a = headFloor(w)^temporalFaceCount(width),
    b = prefixCap(w)^temporalFaceCount(width),
    ell(f) = H[V_K*f], eta = a/b, q = 1-eta.

The already constructed rank-one cone bounds give
a*ell(h) <= T_K h <= b*ell(h) for supported certified h. Cancellation
of the actual kinetic lower and upper certificates proves 0<a<=b,
so 0<eta<=1 and 0<=q<1. No numerical margin is postulated.

Given certificates f-l*g>=0 and u*g-f>=0, a supported certified g and
ell(g)>0, let h_low=f-l*g and h_high=u*g-f. Define

    gain(h) = eta * ell(h)/ell(g),
    l' = l + gain(h_low), u' = u - gain(h_high).

Each gain is nonnegative. The key certificate identity is

    T_K h - gain(h)*T_K g
      = [T_K h - a*ell(h)] + gain(h)*[b*ell(g) - T_K g].

Both terms have constructed certificates. Applying this to both residuals
gives the refreshed bracket l'*T_K g <= T_K f <= u'*T_K g. Signed linearity
of the SAME ell gives ell(h_low)+ell(h_high)=(u-l)*ell(g), hence exactly

    u'-l' = q*(u-l).

No positivity of f or of l,u is required. The mass of one has the explicit
spatial product floor, and ell(T_K g)>=a*ell(g)*ell(1)>0. Thus support,
comparison certificates and positive mass propagate through the EXISTING
iterateStep. The n-step interval width is exactly q^n times its initial
width. q=0, zero steps and zero-width intervals are included.

Original signed character probes have computed intervals [-C,C] against
one. For a signed term (spin,c), the chosen square-root-free cap is
(c*c)*characterBound(spin)+1. Sum caps inside each face factor, then
multiply across the factor list to obtain probeCap. Shared/repeated faces
are retained; no independence is assumed. This supplies an inhabited
bracket for T_K^n(sourceProbe) relative to T_K^n(1), with width 2*C*q^n.

Finally, applying ell places ell(T_K^n f)/ell(T_K^n 1) in this SAME interval.
The numerator equals the existing compactNumerator with empty terminal probe;
the denominator equals compactPartition. Both reciprocal witnesses cancel
that SAME partition. Under the original geometry/face guards, the pre-existing
selected-action finiteValue therefore lies inside the constructed interval.
There is one terminal spatial V, including at n=0, and one whole-chain
normalization. No finite-state or independently normalized-layer surrogate
is substituted.

## Declaration evidence

Paths in the table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Checked content |
|---|---|---|
| `kineticFloor_le_cap`, `mixFraction`, `mixRate_lt_one` | `BF4ExactSlabFixedSpatialTransferMixingRate.lean:55`, `:81`, `:124` | Actual a<=b, exact a/b and q<1. |
| `weightedMass_add`, `weightedMass_smul` | `BF4ExactSlabFixedSpatialWeightedMass.lean:49`, `:55` | Signed linearity of the original V_K insertion. |
| `weightedMass_one_floor`, `weightedMass_transfer_positive` | `BF4ExactSlabFixedSpatialWeightedMass.lean:136`, `:170` | Supplied positive initial mass and its actual transfer propagation. |
| `probeCap`, `sourceProbe_interval` | `BF4ExactSlabFixedSpatialProbeInterval.lean:52`, `:76` | Computed signed-probe interval, no analytic premise. |
| `Bracket`, `ofInterval`, `gain` | `BF4ExactSlabFixedSpatialTransferBracket.lean:65`, `:72`, `:82` | Witness-bearing endpoints/certificates and computed improvement. |
| `relativeFloorCertificate`, `refresh` | `BF4ExactSlabFixedSpatialTransferBracket.lean:132`, `:167` | Same-kernel certificate identity and refreshed comparison. |
| `massRatio_bounds` | `BF4ExactSlabFixedSpatialTransferBracket.lean:198` | Actual normalized weighted scalar is between the endpoints. |
| `refresh_width`, `iterateWeightedMass_positive` | `BF4ExactSlabFixedSpatialTransferBracketDecay.lean:103`, `:133` | Exact q factor and propagated positive denominators. |
| `iterateBracket`, `iterateBracket_width` | `BF4ExactSlabFixedSpatialTransferBracketDecay.lean:152`, `:175` | Constructed brackets for the existing iterate and exact q^n width. |
| `sourceProbeBracket`, `sourceProbeBracket_width` | `BF4ExactSlabFixedSpatialTransferBracketDecay.lean:204`, `:216` | Inhabited signed-source specialization; no extra mass premise. |
| `sourceProbeMassRatio`, `sourceProbeMassRatio_bounds` | `BF4ExactSlabFixedSpatialTransferBracketDecay.lean:231`, `:242` | Concrete normalized consumer with proved denominator. |
| `weightedMass_iterate_compactNumerator`, `weightedMass_iterate_compactPartition` | `BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.lean:52`, `:66` | Same numerator and same partition. |
| `sourceProbeMassRatio_normalizedScalar`, `sourceProbeMassRatio_originalFiniteValue` | `BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.lean:84`, `:116` | Same normalization and original-action identification. |
| `originalFiniteValue_bounds` | `BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.lean:130` | Original chain observable lies in the constructed shrinking-width interval. |

## Parameter scope and remaining work

- a,b,q depend on nome and width, not on late heat cutoff K.
- ell, the iterated messages, the normalized scalar and interval endpoints
  still depend on K. Their equality pins do not erase that dependence.
- probeCap depends on the supplied signed coefficients/spins/factor list,
  not on nome, width or heat cutoff. Physical placement still requires
  the original width/time/face-membership guards in the finiteValue pin.
- This is decay of comparison spread relative to T_K^n g, NOT decay of
  the unnormalized T_K^n f or a completed OS norm estimate.
- The interval centres may change with n and K. Nesting/consistency or
  positive terminal-boundary comparisons and explicit limit passage still
  need proof before asserting stationarity or connected-correlation decay.
- Finite-power/moment compatibility of the previously constructed cutoff-
  limit operator remains open, as do physical reflected OS/vacuum realization,
  width/spacing-uniform estimates, continuum QFT and all compact simple groups.

## Verification boundary

Six focused serialized one-worker/20 GiB checks passed all 40 public axiom
gates within {propext, Quot.sound}. No literal hole, new axiom, analytic
premise, old statement or canonical frontier field changed. Independent
source reviews checked the two-residual identity, q=0, signed probes,
positive-mass propagation and the scope of geometric decay.

Scalar arithmetic was isolated to avoid expanding concrete source data.
The iteration uses explicit Nat induction and local elaborator opacity for
weightedMass, kineticWeight, spatialWeight and baseLinks. Its heartbeat
budget is 2,000,000; the one-worker and 20 GiB memory ceilings were unchanged.
These changes affect proof elaboration, not the actual iteration or theorem
statements. Six selective-root imports added; root/full-tree and full axiom
audit unrun. CI remains manual-only.

| Focused log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialTransferMixingRate.log` | `d026bfa8005361d6539c4742907d9702e7e6729613804a7c91ac1ff4273e320d` |
| `BF4ExactSlabFixedSpatialWeightedMass.log` | `e39deb17277bef7cfb88ca1c792adbe79e9943bcae08cbd50ec3cea5e00f5c25` |
| `BF4ExactSlabFixedSpatialProbeInterval.log` | `2b351189ed5d49e27536829b15ebd7ab5664f85ba06823645aea3746434022a5` |
| `BF4ExactSlabFixedSpatialTransferBracket.log` | `33dea6649e6de088000b6ce0e1e3d62c70eea851d4f0a07cb6452eeae16e3532` |
| `BF4ExactSlabFixedSpatialTransferBracketDecay.log` | `bdaf62fe2a05c40efa877cbed223592b83f420303658c145a60856362e2333b2` |
| `BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.log` | `8ea3fc37cdbad34162b137cd67d7eaf01daa57b742bf998437bda4d19efe615d` |
