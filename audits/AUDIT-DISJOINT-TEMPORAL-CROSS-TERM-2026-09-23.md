# Full mixed temporal form and a finite disjoint-support test

Date: 2026-09-23. Parent revision: `d8446a9`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT and
Yang--Mills local-field/short-distance structure, isolated vacuum and finite
positive physical Hamiltonian mass gap.

## Actual mixed-form identity

`full_jump_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:245`,
proves, for the actual selected-link product P, supported source a and
supported signed observables f,r,

```
H_edge[(f(x)-f(y))*(r(x)-r(y))]
  = 2*(H[a*(P a)*f*r] - H[(a*f)*P(a*r)]).
```

The edge is the existing `edgeWeight`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductLocalGap.lean:58`:
the original product heat times a on each endpoint. The marginal is the
existing `marginalPair`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:115`.
The only guards are the actual support and selected-index bounds. Neither
positivity, conditional centering, disjointness nor a zero mixed term is
assumed. The proof expands both jumps, identifies both diagonal terms with
the same marginal, and uses the original kernel's slice-swap symmetry for
the two cross terms. It does not separate and then discard the signed
endpoint correction.

This identifies the finite signed Gram entries to be controlled. It is an
identity, not a collective upper estimate or a spectral-gap lower bound.

## Positive finite SU(2) certificate

All declarations in this section are in
`lean/YMGap/Continuum/SU2QuaternionDisjointTemporalCrossTerm.lean`.

`P` at line 55 is literally `productMap 2 (1/2) 1 [0,1]`.
`x`, `y`, and `source` at lines 50--52 are the scalar coordinates on two
distinct quaternion blocks and `a=1+(1/2)*x*y`. The source is diagnostic
data, not the physical original-action endpoint source V*g.

- `sourceFloor_certificate` at line 97 constructs a square certificate
  for `a-1/2` on the original Haar carrier; `source_certificate` at line 101
  certifies a itself. These certificates are valid with arbitrary supported
  square insertions, not assumptions extracted from a numerical experiment.
- `firstHeatFloor_certificate` at line 113 and
  `secondHeatFloor_certificate` at line 118 certify the half floor for each
  actual cutoff-one heat factor. `kernel_certificate` at line 123 and
  `edge_certificate` at line 134 certify the full original kernel and edge.
  No unproved eventual-cutoff guard is used to certify this small cutoff.
- `propagatedSource_certificate` at line 140 uses the checked coefficient
  identity `P(a)=(1/64)*a+63/64`. `marginal_certificate` at line 147
  consequently certifies the SAME density `a*P(a)`.
- `x_independent_second` at line 151 and `y_independent_first` at line 157
  certify disjoint coordinate dependence.
- `marginalMass_value` at line 164 gives `Z=4097/4096`.
  `marginal_x_zero` at line 169 and `marginal_y_zero` at line 173 prove
  that both observables are centered in this SAME source-dependent marginal.
- `mixedCorrectedEnergy_value` at line 179 gives `B_a(x,y)=49/2048`;
  `mixedCorrectedEnergy_ne_zero` at line 182 rules out zero.
- `edgeMixedEnergy_pin` at line 196 consumes the general mixed-form identity;
  `edgeMixedEnergy_value` at line 206 gives the literal mixed jump integral
  `49/1024`. This is not a separately assigned matrix entry.
- `energy_nonadditivity_value` at line 211 gives
  `E_a(x+y)-E_a(x)-E_a(y)=49/1024`.
- `normalizer_pin` at line 218 proves that `4096/4097` is the inverse of
  the SAME Z; `normalizedMixed_value` at line 221 gives `B_a(x,y)/Z=98/4097`.

Thus disjoint support and same-marginal centering do not, by themselves,
make temporal energy additive. The interaction in the endpoint source
survives the product kinetic kernel.

## What is pruned, and what is not

Pruned: an unconditional inference from static disjoint support/centering
to a zero mixed temporal form. In particular, the static Ward bounded-overlap
costs cannot justify deleting mixed terms merely because the observables
have disjoint supports.

Not refuted: a joint coefficient-square upper bound. Such an inequality may
retain nonzero off-diagonal entries and their cancellations. Absolute row-sum
control would be a stronger sufficient route, not a necessary condition or
a replacement for the original signed quadratic target.

No theorem identifies this diagnostic source with physical V*g. The finite
check is at w=1/2,K=1; it neither asserts nor refutes a theorem restricted to
arbitrarily late cutoffs. No Yang--Mills, continuum-survival, physical-gap,
QFT or all-group counterexample is claimed.

## Next actual consumer

The original action's `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`,
and `normalizedEnergy_window`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`,
already keep the same edge and positive partition. The missing estimate is
collective signed-family temporal control with those objects, quantitatively
useful relative to the SAME centered variance. Its completed consumer is
`centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`.
It still requires that relative one-step estimate as input.

Do not rebuild the already proved one-loop normalized increment
`joint_increment_nome_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeKineticIncrement.lean:168`, or try to
replace the required temporal form by the static Ward score form. The
remaining quantitative source/correction cancellation must be proved on
the whole original form. Spatial/scaling, continuum survival, physical
time and finite positive mass, full QFT/local fields and all groups remain open.

## Verification and division of work

Accepted single-worker 8 GiB leaf checks, both terminal exit 0:

- `/tmp/ym-gap-full-weighted-jump-pairing-check-1.log`: five public gates,
  including unchanged declarations in the existing module.
- `/tmp/ym-gap-disjoint-temporal-cross-term-final-2.log`: twenty-three gates.

All twenty-eight observations report only `{propext, Quot.sound}`; the
accepted logs contain no warning, error, `sorryAx` or `Classical.choice`.
An earlier draft missed a namespace open, and a later certificate draft
required rational proof arguments to be elaborated before kernel reduction;
those failed logs are not accepted verification evidence. The finite
arithmetic uses kernel `decide`, never `native_decide` or an external oracle.

Sol independently derived the mixed term and drafted the finite example.
Root added the general full mixed-form identity, source/kernel/edge/marginal
certificates, exact consumer, normalization and nonadditivity, and checked
the leaves. Luna independently reviewed arithmetic and scope. No new hole,
axiom, weakened frontier field, classical exception or full-root
build/audit/guard. Automatic CI remains disabled.
