# Scope: identifying the physical slab T₁ with a Peter–Weyl-diagonal operator (2026-10-06 PT)

Audit only.  Companion to `SpecMaxRateFamily` (REDUCTION on hypothesis `hC`).

## Declarations

- The physical side: `BF4WilsonAllNomeCompletedInner.Completion` with `completedInner` B,
  the one-step transfer `T 1` (`BF4WilsonAllNomeCompletedTime.completedTime`), and
  `BF4WilsonAllNomeExprMixRateContraction.WilsonVacuumSqContraction hw0 hw1 width r :=
  ∀ y : VacuumComplement, B(T₁y,T₁y) ≤ r²·B(y,y)`.
- The model side: `WilsonSpectralBridge.CharacterDiagResolution op R w N` (over an
  abstract `GNSDynamics.TransferOperator` on a `CompleteGNSHilbert`); the new
  `SpecMaxRateFamily.CharacterDiagNormResolution op R w N perp` with
  `charDiag_normGap : perp x → ⟨Tx,Tx⟩ ≤ specMax(excitedCharModel w N)²·⟨x,x⟩`;
  `excitedCharModel` with λ_s = w^{c4(s)} (`RGTransport.c4 s = s(s+2)`).
- The gap in between: `SpecMaxRateFamily.specMaxRateFamily … hC` takes
  `hC : WilsonVacuumSqContraction … (specMax (S j))` as a hypothesis.

## Minimum missing statement

There must be an isometric embedding `ι : Completion_W → H` (or an identification of
`Completion_W` with a `CompleteGNSHilbert` that has a `TransferOperator op`) satisfying:
1. `B(y,y) = ⟨ιy, ιy⟩` and `ι(T₁y) = op.T(ιy)` (so `T₁` is intertwined);
2. `VacuumComplement` maps into `perp`;
3. a `CharacterDiagNormResolution op R w_eff N perp` whose eigenvalue list is the slab's
   actual excited spectrum.

Then `charDiag_normGap` gives `hC` at r = specMax.  Items 1–2 are plumbing.  Item 3 is the
real content, and it fails as stated (below).

## Is it true for a width-W slab?

- **Not with the single-link character model.**  The slab transfer of a W-wide spatial
  lattice acts on gauge-invariant functions of all spatial links.  It is block-diagonal
  in **spin-network** states (spins on links, intertwiners at vertices), not in single-link
  characters χ_s.  The electric (heat-kernel) part is diagonal there, with eigenvalue
  `Π_links w^{c4(j_ℓ)}`.  The magnetic (spatial plaquette) part does not commute with it
  and mixes spin networks.  So the slab spectrum is not {w^{c4(s)}}.  The true top
  excitation lies near the lowest gauge-invariant excitation (a single plaquette loop,
  4 links at spin ½: about w^{4·3} at strong coupling), up to magnetic corrections.
  `excitedCharModel` fits neither of these.
- **W = 1 / a single plaquette chain:** close, but still not exact.  With one spatial
  plaquette and a pure heat-kernel (electric-only) transfer, the gauge-invariant sector is
  spanned by characters of the plaquette holonomy and the eigenvalues are w^{4·c4(s)}
  (four links).  Exact Peter–Weyl diagonality holds only for the electric-only transfer.
  Once the spatial Wilson weight is included it is diagonal only to leading order in the
  strong-coupling expansion.
- **Strong coupling:** the leading order is diagonal, with an O(β) or O(w-dependent) mixing
  error.  A rigorous statement needs a perturbation bound (Kato–Rellich-type, or the
  finite-dimensional Weyl inequality on a truncated spin-network basis).

Verdict: the identification is **false as literally needed** for W > 1, and exact only for
the electric-only transfer.  The present `CharacterDiagResolution` is the wrong basis for
the slab.

## Honest replacements

1. **Trace/variational bound on the true slab:** `‖T₁|vac⊥‖ ≤ ρ` from exact rational traces
   of `T₁^n` restricted to a finite spin-network truncation (`SpectralTraceSandwich`
   applies once a finite `SpectralModel` for the truncated slab exists), plus a tail bound
   for the truncation.
2. **Spin-network basis:** a `CharacterDiagNormResolution` analogue indexed by spin
   networks, for the electric-only slab operator, with eigenvalues `Π w^{c4(j_ℓ)}`.  Then
   handle the magnetic factor as a bounded perturbation.
3. **Strong-coupling leading order plus error:** `r ≤ λ_lead + ε(w)`.  This is compatible
   with `RgRateRelation`-style defects already in `BF4WilsonAllNomeRGStepComposition`.

## U(1) rule

`CharacterDiagNormResolution`, `charDiag_normGap`, `specMaxRateFamily` and the halving chain
are **U(1)-blind plumbing**.  The same algebra applies with λ_n = w^{n²}.  The SU(2) content
lives only in `c4` and in item 3.  The 4D U(1) Wilson action at large β is gapless, so any
claim that item 3 holds uniformly in β with a gap is refuted for U(1).  No such claim is made
here.
