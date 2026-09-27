# Original signed neighborhood energy: checked reduction and next argument

## Kernel-checked result

On the SAME original finite full-action SU(2) GNS completion, let P_i be
the constructed conditional projection, R_i=I-P_i, and Hx=sum_i R_i x
over the duplicate-free physical schedule. The new theorems give

    <Hx,x> = E(x) = sum_i ||R_i x||^2,
    ||Hx||^2 = E(x) + C_near(x) + Q_remote(x),
    Q_remote(x) >= 0,
    E(x) + C_near(x) <= ||Hx||^2.

Here C_near is the ORDERED sum of <R_i x,R_j x> over DISTINCT neighboring
physical links. Q_remote is the ordered nonneighbor sum of ||R_i R_j x||^2.
Every neighborhood row contains at most 25 links, including its diagonal.
No original norm, action, normalizer or completed state is replaced, and no
neighbor cross term is dropped or made positive by assumption.

This isolates all potentially negative terms in a bounded-degree geometric
sum. It does NOT prove that this sum is small enough for coercivity or decay.
H is a finite conditional-link dynamics operator, not the OS-time Hamiltonian.

## Exact declarations

- `commuting_residual_pairing_eq_normSq`,
  `lean/YMGap/Continuum/GNSProjectionResidualPair.lean:53`, proves the
  positive-square identity for commuting projections. `residual_idem` at
  line 38 and `residual_commute_of_op_commute` at line 44 supply its algebra.
- `residualSum`, `residualSum_adjoint`, and `residualSum_self_pairing`,
  `lean/YMGap/Continuum/GNSProjectionSignedEnergy.lean:89`,
  `lean/YMGap/Continuum/GNSProjectionSignedEnergy.lean:112`, and
  `lean/YMGap/Continuum/GNSProjectionSignedEnergy.lean:120`, construct H,
  establish its adjoint identity, and identify its quadratic form with the
  EXISTING `finalEnergy`.
- `neighborhoodGram_diagonal`,
  `lean/YMGap/Continuum/GNSProjectionSignedEnergy.lean:150`, uses a
  duplicate-free list and reflexive adjacency to count each diagonal once.
  `residualSum_square_decomposition` at line 198 and
  `neighborhoodGram_le_residualSum_square` at line 226 retain the signed
  neighborhood part and discard only proved nonnegative remote squares.
- `conditionalGenerator_energy` and `conditionalGenerator_square`,
  `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:61` and
  `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`, instantiate
  these facts on the actual original physical schedule and fullData carrier.
  `remoteEnergy_nonnegative` at line 79 and
  `signed_energy_le_generator_square` at line 85 give the actual lower
  comparison. `neighborhood_row_count` at line 97 returns the geometric 25.

## Next mathematical argument — reviewed, NOT yet formalized

The next missing estimate is a signed neighboring-pair bound, not another
certificate assuming global coercivity. The following elementary argument
specifies a candidate producer and its precise missing same-object pins.

Suppose B is the ORIGINAL inner product and B0 is a common spectator-weighted
product-Haar comparator with both selected coordinates free, on a shared
space. Suppose L*B0(z,z)<=B(z,z)<=U*B0(z,z), L>0. Let Q_i,Q_j be commuting
B0-orthogonal coordinate projections. The actual B-orthogonal P_i,P_j must
have the SAME coordinate-omission ranges. These are requirements to prove
for the intended comparator, not new assumed Lean fields.

Put c=(L+U)/2, eta=(U-L)/2, A=B-c*B0. For u=R_i x, v=R_j x,
e_i=(I-Q_i)x and e_j=(I-Q_j)x, orthogonality and range pinning give

    B(u,v) = c*B0(e_i,e_j)
             + A(u,(I-Q_i)v) - A(v,Q_j e_i).

The first term is nonnegative because Q_i,Q_j commute. Polarization of
the form comparison bounds |A(a,b)| by eta*||a||_0*||b||_0. Both error
terms are bounded by eta*||u||_0*||v||_0; 2ab<=a^2+b^2 then gives

    B(R_i x,R_j x) >= -e*(||R_i x||_B^2+||R_j x||_B^2),
    e = (U-L)/(2L).

The square roots in this prose derivation are not required computational
data: a constructive formalization must use squared-form Cauchy/AM--GM or
explicit constructive roots. The polarization estimate and shared-completion
range/orthogonality pins are still to be formalized for the actual operators.

IMPORTANT COUNTING: C_near is ordered, so a maximum degree D costs **2D*e**,
not D*e. The safe existing D=25 yields
`||Hx||^2 >= [1-25*(U-L)/L]*E(x)` if the missing pair estimates are supplied.
Positivity thus requires `25*U < 26*L`. No such analytic instance is proved
in this increment. The diagonal-inclusive 25 is deliberately conservative.

Candidate source inputs already exist: `heatRemainderBound_eq`,
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:85`, displays
delta(w)=128*w^3. `insertFace_upper` and `insertFace_lower`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:135` and
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:147`, compare
each original face to 1+/-delta under a supplied positive background, subject
to their explicit small-nome guards. `existingNome_guards` at line 195
checks those guards for the existing pilot, not the new pair bound.
`neither_heat_local`,
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceGeometry.lean:198`, supplies
literal independence of the background with both selected stars removed.
The proposed two-link near-one form comparison is not asserted proved here.

No new collar geometry is needed: `collarCount_le`,
`lean/YMGap/Continuum/BF4ExactSlabLocalSupportComparison.lean:56`, bounds the
collar of the literal list [i,j] by 12. `background` at line 50 is exactly
the product of the detached original faces; `links_detached_disjoint` at
line 69 and `fullWeight_split` at line 79 supply its independence and exact
factorization. `weighted_bounds` at line 99 already handles arbitrary
positive-certificate insertions, but with the coarse headFloor/prefixCap
constants, not the desired near-one constants. Reusing this partition with
the small-nome face estimates is the next comparison task. It must allow
arbitrary spectator-dependent test polynomials; merely comparing polynomials
supported on [i,j] would not control every actual residual pair.

Even H^2>=gamma*H would still need a constructive kernel-removal/coercivity
argument. The existing positive finite-volume centered estimate is a possible
input: for M at least the schedule length, iteration of I-H/M has geometric
energy decay, while the finite-volume lower estimate controls its norm.
Telescoping could then give centered coercivity gamma/2 without a spectral
theorem. This argument is reviewed mathematics, not a checked bridge in this
increment. Its eventual consumer is the existing
`reverse_energy_of_coercivity_at_balanced`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`.

Small-nome control alone would not supply a justified continuum scaling
trajectory. A03, same-theory thermodynamic/scaling/OS/QFT construction,
nontrivial continuum survival, physical Hamiltonian mass, every compact
simple group and the Clay target remain open. Canonical chart unchanged.

## Verification and parallel review

Three focused modules passed under the safe launcher with one worker and
20 GiB hard cap: GNSProjectionResidualPair (4 printed gates),
GNSProjectionSignedEnergy (10), BF4ExactSlabSignedNeighborEnergy (8).
All 22 printed dependencies lie within {propext, Quot.sound}. Initial proof
orientation, simplifier-loop and explicit decidable-instance issues were
corrected; no resource limits were raised. Each check finished in its initial
call; no long-running process required polling.

Luna supplied the residual-pair proof; the main agent corrected and checked
it, constructed the finite signed decomposition and actual specialization.
Sol independently reviewed the source, diagonal counting, operator identity
and ordered-pair factor of two. A second Sol review derived the next
perturbation argument and identified existing small-nome inputs.

No new sorry, axiom, noncomputable declaration, analytic certificate bundle
or canonical field. No root/full-tree build, full audit, guard, progress-metric
script, routine literature scan or CI run. Root imports are registered only.
