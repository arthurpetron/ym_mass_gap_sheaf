# Scope: `CharacterDiagResolution` and the `hlink` of the trace route (2026-10-06 PT)

Audit only, no Lean.

## Declarations involved

- `SpectralHalvingMargin.wilsonLowerMargin_of_traceCertificates`, hypothesis
  `hlink : ∀ j, F.rate j ≤ specMax (S j)`. It is used in `rate_pow_le_half_of_trace`:
  `r^n ≤ specMax^n ≤ excitedTrace S n ≤ U ≤ 1/2`. So **specMax is used as an UPPER bound
  on the rate**, and the trace certificate then bounds specMax from above.
- `BF4WilsonAllNomeWilsonDynamicFamily.WilsonDynamicFamily.rate`, with
  `contraction : WilsonVacuumSqContraction … (width j) (rate j)`, where
  `WilsonVacuumSqContraction r := ∀ y ∈ VacuumComplement, B(T₁y, T₁y) ≤ r²·B(y, y)`
  (`BF4WilsonAllNomeExprMixRateContraction`). This is an all-vector, squared-norm,
  one-step contraction **upper bound** on the full-width all-nome slab transfer `T₁`.
  Any `r` above the true norm `r* := ‖T₁|vac⊥‖` is admissible.
- `timeRate := entropyRate 96 comparisonCoreRate` (`BF4WilsonDescentUniformConnectedDecay`;
  `timeRate_eq_one_fourth`). This is a **w-independent cluster/descent-count constant**
  (a polymer-entropy rate). It enters through `allNome_strongCoupling_vacuumSq` under the
  guards `heatRatio ≤ 1/2` and `heatRemainderBound < 1`. It is not an eigenvalue.
- `WilsonSpectralBridge.excitedCharModel w N`: `λ_i = qpow w (c4 (i+1))` (single-link
  heat-kernel character eigenvalues; `specMax ≤ w³`).
- `WilsonSpectralBridge.CharacterDiagResolution op R w N` (Type-level, OPEN):
  `coeffSq`, `parseval_self : ⟨x,x⟩ = Σ|cᵢ|²`, and
  `parseval_T : ⟨Tx,x⟩ = Σ λᵢ|cᵢ|²` for a GNS `TransferOperator op`. It feeds
  `wilsonTransferSpectralBridge` and `wilsonTransferFormGap`, giving the **form** bound
  `⟨Tx,x⟩ ≤ w³⟨x,x⟩` on vac⊥.

## What the link would assert

`F.rate j ≤ specMax(S j)` says the carried contraction rate is no larger than the top
excited eigenvalue. If `T` were diagonalized by characters, the best possible rate is
`r* = specMax`, and every valid contraction rate satisfies `r ≥ r*`. So `hlink` holds only
if the carried rate is **sharp** (`r = r*`). It is a sharpness assertion, not a consequence
of diagonalization.

## Loose, or the wrong shape? Both, in a precise sense

1. **Loose.** At w = 1/1024, `timeRate = 1/4` and `specMax ≤ w³ ≈ 9.3·10⁻¹⁰`
   (`SpectralHalvingStrongCouplingCarrier.excitedChar_specMax_lt_rate`). The cluster rate
   overshoots by about 2.7·10⁸. No correct sharpening of the *cluster argument* reaches
   w³, because it is w-independent by construction.
2. **Wrong shape.**
   - (a) Direction: the chain needs `rate ≤ specMax`, i.e. a lower bound on the spectrum
     in terms of the rate. Diagonalization gives the opposite inequality
     (`r* = specMax ≤ any valid r`).
   - (b) Operator mismatch: `CharacterDiagResolution` is about a single-slice
     heat-kernel `TransferOperator` on an abstract GNS Hilbert space, while `F.rate` is
     about the all-nome slab transfer `T₁` on `Completion` (width `W`). Nothing identifies
     the two. Its spectrum is not `{w^{c4(s)}}`: plaquettes couple links, so the slab
     eigenvalues are the plaquette character ratios, not single-link Casimir powers.
   - (c) Form vs norm: `parseval_T` controls `⟨Tx,x⟩`, while
     `WilsonVacuumSqContraction` is `‖Tx‖² ≤ r²‖x‖²`. That needs a `⟨Tx,Tx⟩` Parseval
     (`Σ λᵢ²|cᵢ|²`), which is absent.

So the statement "rate_true ≤ specMax" with rate_true ≈ w³ is correct in spirit, but only
for the operator that the character model actually diagonalizes. For the slab carrier the
honest target is `r* ≤ specMax(S_slab)`, with `S_slab` the slab's own spectral model.

## Recommendation

- Do **not** try to prove `hlink` for `F.rate = timeRate` with `excitedCharModel`. It is
  false (proved no-go).
- Reverse the construction: define the rate *from* the spectrum.
  1. Add to `CharacterDiagResolution` (or a sibling) a norm Parseval
     `parseval_TT : ⟨Tx,Tx⟩ = Σ λᵢ²|cᵢ|²`.
  2. Prove `WilsonVacuumSqContraction`-style `‖Tx‖² ≤ specMax²‖x‖²` from it (finite
     algebra: `λᵢ² ≤ specMax²`).
  3. Build a `WilsonDynamicFamily`-shaped family whose `rate := specMax (S j)`. Then
     `hlink` is `le_refl`, and the trace certificate does real work, with margin about
     1 − w³.
- What stays OPEN, and is the real content: the character diagonalization of the
  *physical* transfer operator (Peter–Weyl inside `cinner`), and identifying that operator
  with the all-nome `Completion` transfer `T₁`. Until then the trace route is non-vacuous
  only in the circular sense of `scFamily_lowerMargin_via_trace`.
- U(1) rule: steps 1–3 are group-blind algebra. The SU(2) content is only in `c4(s)` and
  in the identification. The w³ separation is the SU(2) spin-½ heat-kernel gap; for U(1)
  the analogue is `w^{n²}` with n = 1. No large-β claim is made, so nothing is refuted.
