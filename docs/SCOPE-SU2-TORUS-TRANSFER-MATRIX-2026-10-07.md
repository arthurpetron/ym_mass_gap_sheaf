# Scope: transfer matrix for the torus SU(2) T_K weight (2026-10-07 PT)

**SCOPE NOTE ONLY: no Lean definitions in this commit.** Labels: strong coupling (for the gap
step only; T itself is defined for every β ≥ 0); Wilson T_K (Taylor-truncated, uniform in K);
also true for U(1); not gap evidence.  This note is coordinated with Realizer's torus RP files
(`SU2TorusRPCore`, `SU2TorusRPWilson` 3eb8cc83, `SU2TorusRPHaar/SplitSel/Word/Subst/Reindex/
HeadSub/Conj/ConjCongr/Pad`, `docs/J04-TORUS-RP-SCOPE-2026-10-07.md`).  None of them are edited.

## 1. Definition (paper level; to be formalised)

The torus is `torusPlaquettes N` (Z_N^4).  Take direction 0 as time, so N_t = N.
For a time t, write:
* `U_t` for the spatial links of slice t (3N³ links);
* `V_t` for the temporal links t → t+1 (N³ links).

The plaquettes then split by slice:
* spatial plaquettes in slice t, which depend on `U_t` only;
* timelike plaquettes between t and t+1, which depend on `(U_t, V_t, U_{t+1})`.

**Slice kernel**, with no gauge fixing (the same decision as the RP scope: V stays integrated):

    T(U, U') = Π_{p spatial in slice} T_K(p)(U) · ∫ dV Π_{p timelike} T_K(p)(U, V, U').

**Transfer operator** on slice link polynomials f(U):

    (T f)(U) = ∫ dU' T(U, U') f(U').

**Partition function.** Each link occurs in exactly one slice factor, so Haar factorisation and
periodicity give:

    Z_W = ∫ Π_{p∈torus} T_K(p) = ∫ Π_t dU_t Π_t T(U_t, U_{t+1}) = Tr T^{N_t},

with `Tr K := ∫ K(U, U) dU` for a polynomial kernel.

**Finite rank.** For finite K, T(U, U') is a polynomial of bounded degree in U.  So T maps into
a finite-dimensional space of slice polynomials: T is finite rank, and `Tr T^{N_t}` is a trace
on a finite-dimensional space.  All the spectral theory is linear algebra there, which is the
setting of `CompactTransferGNS.FiniteOp` / `diagOp.toSpectralModel`.

## 2. Where it plugs into existing machinery

| piece | existing repo object | status |
|---|---|---|
| polynomial weight T_K(p), T_K split | `SU2WilsonPolymerIdentity.TK`, `T_split` | PROVED (Realizer) |
| Haar factorisation across block groups | `SU2TorusRPCore.haar_factor`, `SU2TorusRPPad.pad_haar` | PROVED |
| slice shift t → t+1 as a block map | `SU2TorusRPReindex.reindex_ringSub`, `SU2TorusRPSubst.prodPoly_sub` | PROVED (RingSub level) |
| symmetry T(U,U') ~ T(U',U) (V ↦ V*) | `SU2TorusRPHaar.conj_haar`, `SU2TorusRPConjCongr.conj_peCongr` | PROVED (ingredients) |
| positivity T ≥ 0 (from RP across a slice plane) | `SU2TorusRPCore.rpk_pos`, `SU2TorusRPWilson.wilson_rp_full` / `wilson_rp_qfull` | **OPEN**: `hW` bridge (a)–(d) |
| GNS form ⟨F,G⟩ = E(ΘF·G) | `WilsonGNS.WilsonGNSData`, `wilson_qInner_posdef` | PROVED (abstract) |
| dynamics pin T(embed a) = embed(τ a) | `WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin` | needs τ = slice shift and T from §1 |
| OS bundle / gap interface | `WilsonLinkedOSReconstruction` (`WilsonLinkedOSGNSData`, `WilsonCharacterOS4Pin`, `formGap`) | `formGap` is the named open input |
| clustering input | `SU2WilsonTrunc.wilson_trunc_ratio` (commit 23), `SU2TruncRatio.trunc_ratio` (heat) | PROVED: χ₁–χ₁ covariance ≤ C λ^d, uniform in K, N |

The intended route:
1. RP across the plane between slices gives a positive semi-definite form on Λ₊ polynomials.
2. GNS quotient (`WilsonGNSData`), with τ the slice shift.
3. τ induces T on the quotient; T is a self-adjoint positive contraction (Osterwalder–Seiler, by
   Cauchy–Schwarz iteration).  This is the `WilsonTimeTranslationPin`.
4. Covariance decay in time separation gives the spectral separator on the χ₁-cyclic sector.
5. That supplies `formGap` / `WilsonCharacterOS4Pin`.

## 3. Open obligations (in dependency order)

1. **Slice geometry (definitions).**
   - Partition the links of `torusPlaquettes N` into `U_t`, `V_t`.
   - Partition the plaquettes into spatial and timelike classes.
   - Express `plaqWord` of each class in slice variables.
   - This is the same kind of work as RP obligation (c), and it should share Realizer's ordering.
2. **Z = Tr T^{N_t}.**
   - Iterated `haar_factor` over the N_t slice groups, plus periodic closure.
   - Needs (1) and the block-reindex RingSub instances (`PECongr` for reindex is still OPEN in
     `SU2TorusRPConj`).
3. **Trace identities for correlators.**
   - `Z_S = Tr(T^{N_t−t} A_p T^t B_q)` for observables inserted at slices 0 and t.
   - Then the commit-23 bound at time separation t reads `|Tr(…)/Tr T^{N_t} − …| ≤ Cw λ^t`.
4. **Self-adjointness.**
   - Kernel symmetry via `conj_haar` on V and the reflection of the slice.
   - The spatial weight must be split symmetrically (T_K^{1/2} is not polynomial).
   - Use `A^{1/2}` only at the operator level, or work with the similar operator `B A` (same
     trace and spectrum).
5. **Positivity T ≥ 0.**
   - Follows from RP for the actual torus measure, which is **OPEN** (Realizer's `hW` bridge,
     items (a)–(d) of the RP scope doc).
   - Without it, T is only a finite-rank real operator.
6. **Gap from clustering.**
   - For finite-rank positive self-adjoint T, the χ₁ covariance bound gives `(λ₁/λ₀)^t ≲ C λ^t`
     on the χ₁-cyclic sector, uniformly in N = N_t → ∞.
   - Full gap needs all local slice observables, not only χ₁ of one plaquette.  The generic
     `SU2TruncGeneric.trunc_gen` takes any activity package, so extending to bounded-support
     polynomial observables changes only the constants (Dw grows with the observable's bSum).
7. **Scope limits.**
   - Everything is lattice and strong coupling (β_S = 1/(2·10¹²)) for the gap.
   - The continuum and weak coupling are untouched.
   - The resulting gap is also true for U(1), so it is not mass-gap evidence.

## 4. Not done here

No `def` of T, slices or trace was added; per instruction this is a scope note only.  No
Realizer file was edited.
