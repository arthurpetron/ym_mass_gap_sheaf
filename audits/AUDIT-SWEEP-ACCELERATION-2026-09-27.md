# Avoiding a loss in the dynamics-to-spatial-decay conversion

**Follow-up:** the operator energy identity, literal recurrence, original
rational scalar action, completed centered preservation and unconditional
all-order NON-STRICT bound at `c=2` have now been checked. See
`AUDIT-ORIGINAL-SWEEP-CHEBYSHEV-2026-09-27.md`. The planning discussion
below records the preceding review; its normalized accelerated rate and
actual centered coercivity remain open.

This is a targeted primary-source/planning review, with a small checked
supporting adjoint lemma recorded below. It is NOT a proved acceleration
bound or an instantiated Yang--Mills coercivity theorem. It was performed
alongside the focused conditional-kernel check; no routine math-ph listing
was fetched.

## Primary-source result

Gosset--Huang, *Correlation Length versus Gap in Frustration-Free Systems*,
Theorem 1 and equations (9)--(15), treat finite-dimensional, geometrically
local, frustration-free projection Hamiltonians. For a layered projection
product S, a degree-m polynomial of S* S normalized at 1 preserves the
separated-observable pairing. A rescaled Chebyshev polynomial suppresses
the excited interval by `2 exp(-2m sqrt(eta))`, with
`eta=epsilon/(g^2+epsilon)`. This improves the correlation-length dependence
from inverse gap to inverse square root of gap.
[Primary paper, pages 2--3](https://arxiv.org/pdf/1509.06360).

Anshu--Arad--Vidick, *Simple proof of the detectability lemma and spectral
gap amplification*, Lemma 2/Corollary 3, prove the projection-product energy
estimate with arbitrary projector ordering and bounded noncommutation
degree; the lemma does not require geometric locality. Locality is needed
for the separate spatial conclusion.
[Primary paper, pages 3--4](https://arxiv.org/pdf/1602.01210).

## Existing repository inputs

- `Family.adjoint` and `Family.idem` in
  `lean/YMGap/Continuum/GNSProjectionSweep.lean:59` define the same completed
  self-adjoint projections; `Family.loss_eq` (`:133`) is the exact telescope.
- `eight_layer_energy_le_625_loss` in
  `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:84` gives
  `sum_i ||R_i Sx||^2 <=625*(||x||^2-||Sx||^2)` on the original completion.
- `runLayers_localized` in
  `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:216` treats arbitrary
  color lists, not only one direction of the eight-layer order.
  `runLayers_pairing` (`:271`) preserves the actual pairing for any such
  list before cone/test contact. `cycles_pairing` (`:320`) and
  `covariance_as_sweep_pairing` in
  `lean/YMGap/Continuum/BF4ExactSlabConditionalCovariance.lean:190` give the
  existing forward-sweep separated-pairing and original normalization pins.
- `Cheb.pythForm_all` in `lean/YMGap/Continuum/ChebyshevBound.lean:645`
  proves the scalar polynomial identity
  `T_(n+1)^2+(1-x^2)*U_n^2=1`. `Cheb.Tsq_le_one` (`:672`) is a scalar
  rational bound, not an operator functional calculus.

## Inference for the next mathematical work

Write epsilon for the still-unproved original centered lower-energy
constant. Combining that proposed lower estimate with the checked 625
upper estimate would give the squared sweep contraction
`q=625/(625+epsilon)`. This implication does not supply epsilon.

If the polynomial acceleration can be proved on THIS completed carrier,
the candidate spatial rate scales as `sqrt(epsilon/(625+epsilon))`.
Consequently a hypothetical `epsilon` of order physical spacing squared
need not be rejected merely because ordinary sweep powers give too weak
a physical decay estimate. Neither that scaling law nor the adapted
accelerated bound is currently proved. This is an inference from the
source mechanism and the repository constants, not an imported theorem.

The reverse-adjoint sweep and its SAME-carrier positive product S* S are
now constructed below. Remaining bounded tasks are the polynomial
cone-pairing identity and a constructive operator Chebyshev bound. The scalar identity
above suggests a square-positivity proof without importing a classical
spectral theorem. A source theorem about a finite tensor-product space
cannot simply be applied to the current completed CReal carrier.

A candidate elementary operator argument is the coupled recurrence
`T'=X*T-H*U`, `U'=T+X*U`, where `H=I-X^2` and X is self-adjoint and
contractive on the preserved centered sector. Self-adjointness and
`H*X=X*H` cancel the cross terms, formally preserving
`||T||^2+<U,H*U>`. Positivity of H would then bound the first term.
This is a proof plan, not a checked operator identity. The scalar
counterpart is `Cheb.linRel` (`ChebyshevBound.lean:193`). It exposes an
algebraic route to the operator bound without a spectral theorem.

The completed contraction of X also has a direct candidate argument.
The checked `final_energy_le_625_loss`
(`BF4ExactSlabConditionalSweepEnergy.lean:71`) permits arbitrary
duplicate-free schedules. Hypothetical original centered coercivity would
therefore give the same norm-square contraction q to S and its reverse.
For `B=S* S`, this yields `||Bv||^2 <= q*<Bv,v>`. Expanding
`X=(2/q)B-I` then gives `||Xv||^2 <= ||v||^2` on that preserved sector.
These implications remain unformalized, and their coercivity premise
remains unsupplied.

For a rational geometric normalization instead of exponentials, a proposed
certificate would choose rational `0<rho<1` with
`eta/4 <= rho^2 <= eta` and use `r=(1+rho)/(1-rho)`. The two-sided comparison
is essential to retain the square-root rate; an arbitrarily tiny lower
witness would not suffice. Using `qbar=1-rho^2 >= q` gives the exact
vacuum evaluation `2/qbar-1=(r+1/r)/2`; this suggests obtaining geometric
normalization directly rather than proving a separate monotonicity theorem.
Neither this scalar construction nor its normalized operator consumer is
supplied by the current increment.

The completed rational action also needs an exact physical construction:
the original `fullData` is a `GNSData`, not automatically a
`SmulGNSData`. Existing generic laws are `SmulGNSData.cSmul` and
`cSmul_cAdd` (`lean/YMGap/Continuum/HamiltonianScalar.lean:360`, `:377`),
and the paired scalar laws in
`lean/YMGap/Continuum/ContinuousFunctionalCalculusForm.lean:251`, `:268`.
They cannot be applied to the original full form by assuming an unstated
scalar structure.

## Checked supporting algebra

`Family.sweep_adjoint_reverse` in
`lean/YMGap/Continuum/GNSProjectionSweepAdjoint.lean:21` proves the reverse
order is the pairing adjoint, for the existing completed projection family
without a commutativity or gap premise. `balanced` (`:34`) constructs
S* S on that SAME completion. `balanced_pairing` (`:38`) gives
`<S* S x,y>=<Sx,Sy>`; `balanced_selfAdjoint` (`:46`) and
`balanced_positive` (`:61`) follow. These declarations establish no strict
rate or accelerated polynomial bound.

All five printed gates passed a focused monitored one-worker/20 GiB check
within `{propext, Quot.sound}`. Sol constructed the file; main reviewed and
checked it. No hole, analytic field, scalar-action instance or full-tree
build/audit was added. The root import list was updated but not root-compiled.

The primary analytic producer remains useful actual centered coercivity.
The eventual OS/physical-Hamiltonian and continuum joins remain separate.
No canonical frontier field or chart marker has been changed.
