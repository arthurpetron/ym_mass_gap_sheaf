# Original two-link comparison and completed-form transport

## Checked mathematical scope

Under the strict small-nome guards

    0 < w < 1,  heatRatio(w) <= 1/2,  heatRemainderBound(w) < 1,

set `delta = heatRemainderBound(w)`,
`L = (1-delta)^12`, and `U = (1+delta)^12`. For every finite cutoff and
slab extent, every supported polynomial `p` (including arbitrary spectator
dependence) obeys the actual same-polynomial comparison

    L * B0(p,p) <= F(p,p) <= U * B0(p,p),

where `F` is the original full-face weighted form and `B0` is the same
original heat action with only faces touching the selected two links
removed. The bounds are independent of cutoff, extent, and test support at
fixed nome. The raw form comparison holds for every cutoff K; the existing
`fullData` completion additionally requires its explicit `headCutoff(w) <= K`
guard. `twoLinkLower_positive`, `twoLinkUpper_positive`, and the exact
pilot inequality `25*U < 26*L` are finite rational facts; the latter is not a
spectral or physical gap.

The completion comparison transports the same literal polynomial sequence
in both directions, changing only its explicit Cauchy modulus, and proves
the maps inverse on the quotient. It extends both form bounds to every
completed original vector. This is an equivalence of ordinary weighted GNS
carriers, not an isometry or an Osterwalder-Schrader construction.

## Declaration map

1. `twoLinkLower`, `twoLinkUpper`, `remainder_nonnegative`,
   `twoLinkLower_positive`, `twoLinkUpper_positive`, and
   `existingNome_pair_calibration` are respectively at
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:22`,
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:26`,
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:30`,
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:36`,
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:43`, and
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:51`.
   The last is the exact rational pilot, at the existing nome 1/1024.
2. The collar comparison is in
   `lean/YMGap/Continuum/BF4ExactSlabSmallNomeCollarComparison.lean`:
   `collar_weighted_bounds` at line 105, `two_link_weighted_bounds` at 137,
   `twoLinkBackgroundData` at 157, and
   `two_link_fullData_bounds` at 163. The collar is at most twelve faces
   by `collarCount_le` in
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportComparison.lean:56`.
   The arbitrary supported test is not required to be local to the selected
   links.
3. The two data objects have definitionally identical polynomial carriers:
   `fullData` is `weightedGNSData` in
   `lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`, while
   `twoLinkBackgroundData` uses the same constructor in the lines above.
   `weightedGNSData` fixes `V` independently of its weight and certificate
   in `lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:63`.
   Thus `two_link_fullData_bounds` compares the same polynomial, with no
   change of carrier or observable.
4. `distance_bounds` in
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkCompletionComparison.lean:41`
   applies that same-form bound to the literal difference polynomial.
   `toBackgroundCauchy` and `toFullCauchy` (lines 67 and 75) preserve every sequence
   term; their moduli use respectively `L*epsilon` and the explicit
   `epsilon * oneOver1p(U)` tolerance. The corresponding Type-level null
   transports are `toBackgroundNullModulus` and `toFullNullModulus` (83 and 91),
   and the legacy quotient relations descend in `toBackground_null` and
   `toFull_null` (99 and 106). `toBackground`/`toFull` (114 and 119) are the
   quotient maps. `toFull_toBackground` and `toBackground_toFull` (136 and 141)
   follow by quotient induction and reflexivity because the composite keeps
   the exact input sequence; changed modulus functions need not be equal.
5. `completed_form_bounds` in
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkCompletionComparison.lean:147`
   passes both dense same-polynomial inequalities to the diagonal Cauchy
   limits for each arbitrary vector in the original completion. The maps
   also preserve residual differences exactly: `toBackground_sub` and
   `toFull_sub` in the same module at lines 168 and 176.
6. The finite dense signed polarization is `two_link_signed_pair` at
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkSignedComparison.lean:51`;
   its original-data form is `two_link_signed_fullData` at
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkSignedComparison.lean:76`,
   using `centered_polarization` in
   `lean/YMGap/Continuum/QuaternionHaarSignedFormComparison.lean:114`.
   With S=B0(p,p)+B0(q,q), it proves the square-root-free signed bound
   `-(U-L)*S <= 4*F(p,q)-2*(L+U)*B0(p,q) <= (U-L)*S`.
   `completed_signed_pair` at
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkSignedComparison.lean:93`
   passes the SAME inequality to arbitrary original completed x,y, replacing
   each B0 argument by its explicit `toBackground` image.
7. `weighted_project_selfAdjoint`, `weighted_square_decomposition`, and
   `weighted_project_square_contraction` are at
   `lean/YMGap/Continuum/SU2QuaternionWeightedHaarBlockProjection.lean:33`,
   `lean/YMGap/Continuum/SU2QuaternionWeightedHaarBlockProjection.lean:71`, and
   `lean/YMGap/Continuum/SU2QuaternionWeightedHaarBlockProjection.lean:105`.
   They retain the independent certified spectator background. The actual
   two-link instance is `detached_project_square_contraction` at
   `lean/YMGap/Continuum/BF4ExactSlabTwoLinkSignedComparison.lean:161`.

## What this does not prove

The weighted `B0` projection contraction is for Haar projection under the
detached background. It does not establish that the actual original-law
conditional projection is self-adjoint in `B0`, nor the mixed identities
`Pi Qi = Qi` and `Qi Pi = Pi` (the background conditional `Qi` is not
asserted self-adjoint in the full form `F`). Even the completed signed polarization
does not itself provide an actual signed residual bound for the original
conditional pair. That bound, and a constructive `H^2` coercivity estimate,
remain open; no new analytic premise has been assumed here.

The relevant consumer remains
`reverse_energy_of_coercivity_at_balanced` in
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`: it
converts a supplied Dirichlet lower bound into reverse energy using the
proved 625 sweep-loss upper bound. The missing residual/coercivity input is
not discharged by the present two-link comparison.

These are finite SU(2) heat-kernel form comparisons in ordinary weighted GNS
carriers; `detached_project_square_contraction` concerns Haar coordinate
projection in the `B0` weighted form. The constants are independent of cutoff
and extent at fixed nome, but make no physical scaling or thermodynamic claim.
The OS-time/Hamiltonian identification, scaling-family estimate,
nontrivial continuum survival, and physical mass gap remain open.
Full same-theory QFT structure, every compact simple group, A03 and the Clay
target remain open; the canonical chart is unchanged.

## Verification and independent review

Six modules passed focused checks through `scripts/safe_lean_build.py`,
serialized with one worker and a 20 GiB hard cap:

- `BF4ExactSlabSmallNomePairCalibration`: 6 printed gates.
- `BF4ExactSlabSmallNomeCollarComparison`: 7.
- `QuaternionHaarSignedFormComparison`: 1.
- `SU2QuaternionWeightedHaarBlockProjection`: 4.
- `BF4ExactSlabTwoLinkCompletionComparison`: 14.
- `BF4ExactSlabTwoLinkSignedComparison`: 4.

All 36 axiom outputs lie within {propext, Quot.sound}; no sorryAx or classical
axiom remains. The scalar pilot uses kernel `decide`, not `native_decide`.
Namespace, section-variable and parser issues encountered during development
were corrected before the successful checks. Every check finished within its
initial call; no live long-running job needed manual polling. Resource limits
were not raised and no compiler ran concurrently.

Sol supplied signed polarization and weighted-projection proofs and reviewed
the common-background scope and remaining range identities. Luna supplied
scalar calibration, checked the completion API and independently reviewed
the explicit identity-sequence/null-modulus maps. The main agent constructed
the collar/completion comparison and checked the integrated actual instances.

No new sorry, axiom, noncomputable declaration, analytic hypothesis bundle or
canonical field. No full-tree/root build, full axiom audit, guard, progress-
metric script, routine literature scan or CI run. Root imports are registered;
the reported verification boundary is these six focused modules.
