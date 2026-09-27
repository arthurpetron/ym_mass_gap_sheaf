# Constructive Chebyshev energy on the actual original completion

## Exact mathematical increment

For a self-adjoint completed operator X define a pair of actual vectors by

    T_0=x, U_0=0;
    U_(n+1)=T_n+X U_n;
    T_(n+1)=X U_(n+1)-U_n.

The signed quadratic quantity

    ||T_n||^2 + ||U_n||^2 - ||X U_n||^2 = ||x||^2

is proved at every order, without a contraction premise. Expansion of the
two squares and self-adjointness cancel the cross terms. No spectral
theorem, eigenbasis, vector representative choice or operator-norm
completion is used. Contraction on the auxiliary vector U_n suffices to
deduce `||T_n||^2 <= ||x||^2`. A preserved additive sector suffices; no
contraction on the physical vacuum is required.

The first component satisfies the literal first-kind recurrence
`T_0=x`, `T_1=Xx`, `T_(n+2)=2X T_(n+1)-T_n`. Self-adjointness and the
existing nondegenerate completed pairing prove the needed add/sub laws;
no separate linearity premise is assumed.

## Source and same-object construction

All paths below are relative to the repository root.

| Declaration | Source | Checked claim |
| --- | --- | --- |
| `GNSChebyshevEnergy.step_energy` | `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:106` | Exact one-step signed energy identity. |
| `GNSChebyshevEnergy.state_energy` | `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:113` | Invariant at every order. |
| `GNSChebyshevEnergy.state_norm_le` | `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:127` | Auxiliary-state contraction implies the first-state norm bound. |
| `GNSChebyshevEnergy.state_mem` / `state_norm_le_on` | `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:137`, `:150` | Invariant-sector version, not an assumption on the vacuum. |
| `GNSChebyshevRecurrence.X_add` / `X_sub` | `lean/YMGap/Continuum/GNSChebyshevRecurrence.lean:86`, `:95` | Completed additivity/subtractivity derived from self-adjointness. |
| `GNSChebyshevRecurrence.first_one` / `first_succ_succ` | `lean/YMGap/Continuum/GNSChebyshevRecurrence.lean:109`, `:128` | Literal first-kind operator recurrence. |
| `fullScalarData` / `fullScalarData_toGNSData` | `lean/YMGap/Continuum/BF4ExactSlabFullActionScalar.lean:27`, `:41` | Rational scalar action with `toGNSData` DEFINITIONALLY the existing original fullData. |
| `constant_fixed` / `sweep_centered` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:112`, `:117` | Actual constant fixed; arbitrary completed orthogonal states stay centered under any schedule, including reverse order/repetitions. |
| `affine` / `affine_pairing` / `affine_selfAdjoint` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:125`, `:132`, `:140` | Actual same-carrier map `c*S* S-I` and its exact pairing. |
| `affine_centered` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:147` | This map preserves the original completed centered sector. |
| `affine_two_norm` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:160` | NON-STRICT contraction for `2*S* S-I` on every actual completed vector. |
| `coupled_energy` / `coupled_centered` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:175`, `:181` | Exact physical-instance energy and preservation of both centered recurrence vectors. |
| `coupled_two_norm` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:197` | Unconditional all-order `||T_n(2*S* S-I)x||^2 <= ||x||^2`. |
| `coupled_first_recurrence` | `lean/YMGap/Continuum/BF4ExactSlabSweepChebyshev.lean:202` | Recurrence pin on those actual physical-instance vectors. |

Here S is the existing eight-layer conditional sweep and S* its checked
reverse, not the physical-time OS transfer. All forms remain the original
unnormalized full-action form. The constant is the literal polynomial one;
no unit-length replacement or changed partition is introduced.

The unconditional operator bound is elementary: the reversed sweep is
nonexpansive, so `||S* S x||^2 <= ||Sx||^2 = <S* S x,x>`. Expanding
`||2*S* S x-x||^2` gives the non-strict contraction. The energy invariant
then supplies the all-order bound. This uses no strict gap input.

## What this removes, and what it does not

The scalar action, actual completed centered-sector preservation, coupled
energy identity, literal operator recurrence, and unshrunk-interval
polynomial norm control proposed in the preceding acceleration review are
now supplied. Identifying all common fixed vectors with constants is not
needed for these results.

Still open are useful ORIGINAL centered lower coercivity; contraction of
the rescaled interval map at `c=2/q` for a useful `q<1`; the rational
normalization producing geometric suppression; and the polynomial cone/
normalized covariance join. The all-order bound at `c=2` is stability,
NOT accelerated decay. It neither constructs q nor improves the physical
mass calibration. OS/physical-Hamiltonian identification, changing-spacing
control, nontrivial continuum survival, full QFT axioms and every-group
Clay closure remain open.

Forward work continues on selecting and controlling the actual polynomial
kernel tests from `BF4ExactSlabStarPolynomialResidual`. Parallel read-only
review identified exterior multiplication as a possible restricted test
family; that identity and its useful estimates were NOT proved in this
increment. No new global-gap assumption bundle is introduced.

## Verification

All four modules passed serialized focused checks with one worker and the
20 GiB cap. The 6 energy, 6 recurrence, 2 scalar and 12 physical gates were
all `{propext, Quot.sound}`, without remaining warnings or holes. Sol
constructed the scalar and recurrence modules and independently reviewed
the energy, original-carrier pin, centered scope and non-strict limitation.
Main implemented the energy and physical instance and checked all files.

Root imports were updated but no root/full-tree build or audit was run.
No canonical field, chart marker, CI setting or analytic hypothesis field
changed. No routine literature refresh was performed. The safe-build
procedure kept all checks focused, serialized and capped.
