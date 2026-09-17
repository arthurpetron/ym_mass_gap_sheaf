# Active-core transfer remainder: execution review

Date: 2026-09-17 22:05 UTC. Source baseline:
`eb9d98d7fea79546d6491b98b297dc86ed841e13`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with the required same-theory QFT axioms,
isolated vacuum and strictly positive finite physical Hamiltonian mass gap.
That goal remains OPEN. This is a source/mathematical planning review, not
a new Lean proof, axiom audit or analytic closure.

Follow-up, 2026-09-17: the prospective full-source fusion identity and
original-partition cutoff-boundary estimate in sections 3--4 are now
proved in `audits/AUDIT-ORIGINAL-FUSION-BOUNDARY.md`, with explicit cutoff
and focused axiom gates. The historical planning review below is retained
as written. Its signed bulk, iteration and continuum obligations remain open.

## 1. Decision: retain both endpoint action weights

`transferStep`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferStep.lean:51`,
is T=K(V*.); `swept_step_pairing` in that file at line 77 retains V at BOTH
ends of the original pairing. `inputNumerator` and `inputPartition`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowInput.lean:88` and `:94`,
retain the right terminal message and the weighted functional M(h)=H[V*h].
The latter is `weightedMass`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:65`.

Consequently, for a=V*g_left and b=V*g_right the original fundamental
two-endpoint numerator is H[(a*chi)*K(b*chi)]. It is not H[(a*chi)*K(chi)].

`coordinate_transmission`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatTransmission.lean:88`,
gives the single-coordinate factor w^3. `one_layer`,
`lean/YMGap/Continuum/SU2QuaternionFullHeatTubeLayer.lean:96`,
combines four factors into w^12, with an explicit independence hypothesis
on the retained spectator. That hypothesis also appears in
`Propagates.pairing`, the field of `Propagates` at
`lean/YMGap/Continuum/SU2QuaternionLinearHeatPropagation.lean:32`.
No corresponding independence of V*g_right is supplied for an active face.
These declarations do not transmit the full input b*chi by that scalar.

A proposed bare-output test was

    Z0*H[chi*T(g*chi)] - B0*H[chi*Tg]
        = w^12*(Z0*C0-B0^2),
    Z0=H[V*g], B0=H[V*g*chi], C0=H[V*g*chi^2].

It would follow from a literal physical kinetic eigen-pin, which was not
implemented in this checkpoint. Even with that pin it uses the wrong
output weighting for the original connected consumer. At most it detects
nonproportionality under Haar tests. It supplies no odd-marginal upper
contraction, transfer-orbit estimate or completed gap. Defer its dedicated
implementation unless a specific useful physical estimate consumes it.

## 2. Precise working remainder, with centering retained

The following is a pencil-and-paper derivation from the cited definitions
and symmetry, not a newly kernel-checked declaration. It is valid for any
supported f and g; g=T^n(1) is the current physical specialization.

Write

    t=Tg, M(h)=H[V*h], Z=M(g*t),
    B=M(g*t*f), C=M(g*t*f^2),
    R=T(g*f)-lambda*f*t.

`transferStep_weighted_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`,
gives M[g*T(g*f)]=B, hence M(g*R)=(1-lambda)*B. Expanding R gives

    energy(g,f) = (1-lambda)*C - M(g*f*R),
    clearedDefect(delta,g,f,f)
      = (1-lambda-delta)*(Z*C-B^2) - M[g*(Z*f-B)*R].

Here `energy` is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`;
`clearedDefect` is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:62`.
Its existing physical consumer is `clearedDefect_diagonal_nonnegative_iff`
in the latter file at line 175. The exact full-source pairing and mean
correction already exist as `combinedTest` at line 71 and
`clearedDefect_pairing` at line 96. Do not create another wrapper for them.

The missing estimate is the SIGNED upper bound

    M[g*(Z*f-B)*R] <= (1-lambda-delta)*(Z*C-B^2)

with an explicit positive delta and the regulator control required by the
chosen route, or a direct improved estimate on the original iterated
connected numerator. The displayed rearrangement alone reduces no analytic
input. Lambda is a freely chosen scalar in the algebra; choosing w^12 for
a fundamental face neither proves a physical eigenvalue nor sets delta.
No polynomial weak-coupling margin or coupling-independent margin is assumed.

## 3. Source-preserving SU(2) calculation to investigate

For a fundamental face, put c_j=(j+1)*w^(j*(j+2)) and let chi_j be its
twice-spin-label-j character. The source definitions are `coeffW`,
`lean/YMGap/Continuum/BondMovingStep.lean:259`, and `heatPrefix`,
`lean/YMGap/Continuum/QuaternionHaarHeatCertificate.lean:31`.
`first_mul_succ`, the private lemma at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceHeatMoment.lean:46`,
checks chi_1*chi_(j+1)=chi_(j+2)+chi_j.

The prospective finite-sum consequence, for K>=1, is

    (chi_1-c_1)*H_K
      = sum_{j=1}^K d_j*chi_j + c_K*chi_(K+1) - c_(K+1)*chi_K,
    d_j=c_(j-1)+c_(j+1)-c_1*c_j.

This summed identity is NOT claimed Lean-proved here. If V=H_K*V_rest,
the tested source retains V_rest*g*K(s), where s includes the actual right
action, terminal message and probe. Moving the kinetic map onto s uses
`kineticMap_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:72`.
No independence of V_rest*g*K(s) may be assumed. Both cutoff-boundary
terms are necessary. Positive d_j, even if proved, would not establish the
sign or magnitude of these weighted harmonic responses. Do not implement
only a scalar coefficient bound and label it the missing full-source bound.

The cube branch is also not a substitute. The exact selected fundamental
cube activity is `finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact`,
`lean/YMGap/Continuum/SU2QuaternionElementaryCubeWeightedActivityNormalization.lean:174`.
The factor-sixteen comparison is
`finiteProductHaarComplex_weightedCanonical_eq_coarseActivity_div_sixteen`
at line 229 of the same file. A multiplicity activity is not the complete
quaternion heat action with terminal messages.

## 4. Bounded next proof target: the original-partition cutoff boundary

The following is a proposed estimate, NOT a checked theorem. It isolates a
finite-cutoff artefact without assuming the desired bulk decay. Its regime
is 0<w<1, K>=1 and K>=headCutoff(w), with a physical selected spatial face.
Let P be the original kinetic map, g the actual left terminal message,
V=H_K*V_rest with only that face factor separated from the full product, and

    u=P(V*g), f=P(V*g*chi_1), v_j=P(V_rest*g*chi_j),
    J(h)=inputNumerator(w,K,width,L,n,h,psi),
    Zfun(h)=inputPartition(w,K,width,L,n,h),
    Z=Zfun(u), Y=J(u), Gamma_j=Z*J(v_j)-Y*Zfun(v_j).

The proposed fusion expansion, combined with the existing input linearity,
would give the ORIGINAL connected determinant

    Z*J(f)-Y*Zfun(f)
      = sum_{j=1}^K d_j*Gamma_j
        + c_K*Gamma_(K+1)-c_(K+1)*Gamma_K.

All terms use the same original Z and Y. They are not expectations
normalized by an erased replacement action. The full spatial face list is
the original duplicate-free list; the selected physical face occurs once.
With a certified right-window interval for psi on (L+1)*N(width) blocks
with cap c, and h=headFloor(w), the bounded next estimate is

    h*abs(c_K*Gamma_(K+1)-c_(K+1)*Gamma_K)
      <= 2*c*Z^2*((K+2)*c_K+(K+1)*c_(K+1)).

The proposed proof uses sharp |chi_j|<=j+1 and the single-face floor
H_K>=h, retaining the entire positive V_rest*g and positive right-window
functional. The relevant existing APIs are `sharpCharacterInterval`,
`lean/YMGap/Continuum/QuaternionHaarSharpCharacterInterval.lean:50`;
`prefixFloorCertificate`,
`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:137`;
and `inputNumerator_bounds` / `inputNumerator_abs_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowInput.lean:176` / `:201`.
The proof must construct the retained-product positivity and comparison
h*Zfun(P(V_rest*g))<=Z on the original carrier; neither is a new hypothesis
to assume. Cutoff-dependent messages and normalizers remain inside this
finite-regulator estimate. An explicit all-nome tail modulus must accompany
any claimed vanishing boundary RELATIVE TO THE ORIGINAL Z(K)^2, with its
dependence on w and tolerance. No vanishing of the unnormalized boundary
is implied when the partition varies with K.

In particular, v_j is signed: `inputNumerator_abs_le` cannot be applied
directly to it. With v_0=P(V_rest*g), construct certificates for
(j+1)*v_0+v_j and (j+1)*v_0-v_j first. Input linearity and both sides of
the positive-window bounds then yield |J(v_j)|<=c*(j+1)*Zfun(v_0) and
|Zfun(v_j)|<=(j+1)*Zfun(v_0). Together with |Y|<=c*Z and the original
partition comparison, these give the proposed factor 2 without treating a
signed message as positive. This construction remains to be formalized.

This is the first implementation target, jointly with the full-source
fusion identity. No uniform bulk contraction follows from it: the signed
sum of d_j*Gamma_j still requires a new estimate, and the full Wilson
transfer orbit remains necessary. Taking absolute values of that entire
sum is not justified as a route to a strict rate by this review.

## 5. Execution and verification boundary

Primary work: the exact full-source fusion identity and original-partition
cutoff-boundary estimate above, followed by the unresolved signed bulk
remainder or iterated connected determinant.
Parallel review: verify its original Wilson-orbit consumer, parameter
dependence, endpoint weights and improved-domain limiting form. The
plaquette test is not a replacement for products, arbitrary spins and time
offsets; the existing coverage audit remains
`audits/AUDIT-TRANSFER-ORBIT-CONSUMER.md`.

No new estimate with the required control was found in this review. The
next analytic milestone therefore remains OPEN. The completed small-nome
gap/excitation are preserved; physical scaling, continuum QFT and the
every-group quantifier are not discharged. The chart/plan is changed, not
the mathematical goal, analytic guards or canonical frontier statements.

Two parallel read-only reviews agreed on the missing target weight and
the retained interaction remainder. No `.lean` file or ledgered obligation
was changed, and no `sorry` was introduced or discharged. No Lean build,
full-tree audit, guard or progress run was performed; no new axiom-status
claim is made. CI and resource limits remain unchanged.
