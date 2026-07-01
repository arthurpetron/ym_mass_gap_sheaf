/-
Inhabiting `WilsonSpectralBridge.CharacterDiagResolution` for the physical
finite-volume Wilson GNS — the last plumbing between the standard
Osterwalder–Seiler / Peter–Weyl Schur datum and the operator-form gap.

# What this module delivers

`WilsonSpectralBridge.CharacterDiagResolution op R w N` is the sole residual
gating the finite-volume Wilson operator-form gap
`⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩` on `vac⊥`.  It bundles, INSIDE the completed
GNS inner product `H.hilbert.cinner`:

  * `coeffSq  : carrier → Fin N → RC` with `coeffSq_nonneg`;
  * `parseval_self : ⟨x,x⟩   = Σ_{i<N} coeffSq x i`;
  * `parseval_T    : ⟨Tx,x⟩  = Σ_{i<N} R.RCscale (qpow w (c4 (i+1))) (coeffSq x i)`.

`wilsonCharacterDiagResolution` REDUCES this whole datum, for the concrete
scaling `R = rcScaleResidualPlus` (`RCscale s ⟦A⟧ = ⟦ofQ' s · A⟧`), to exactly
TWO diagonal Schur / Peter–Weyl identities on the completion carrier plus a
finite character coordinate map `coord : carrier → Fin N → Q'`:

  * `schur_self` : `⟨x,x⟩  = Σ_{i<N} ⟦ e^{−t·C₂(i+1)} · c_i² ⟧`
    (Schur self-orthogonality, diagonal weight `μ_i = reflWeight t (i+1)`);
  * `schur_T`    : `⟨Tx,x⟩ = Σ_{i<N} ⟦ λ_i · (e^{−t·C₂(i+1)} · c_i²) ⟧`
    (diagonal transfer action, eigenvalue `λ_i = qpow w (c4 (i+1))`).

Here `c_i = coord x i`, `μ_i = reflWeight t ht (i+1) = e^{−t·C₂(i+1)}` is the
genuine Schur-diagonal reflection weight of `ReflectionPositivity` (a `CReal`,
NOT a rational — the honest heat-kernel coefficient), and the squared Fourier
weight the bridge consumes is `coeffSq x i = ⟦ μ_i · c_i² ⟧`.

Everything between the two Schur identities and the three
`CharacterDiagResolution` fields is discharged HERE, axiom-clean:

  * `coeffSq_nonneg` — `μ_i · c_i² ≥ 0` from `reflWeight_nonneg` (i.e.
    `e^{−·} ≥ 0`) and `q_mul_self_nonneg` (i.e. `c_i² ≥ 0`), via the constructive
    product-of-nonnegatives `CReal.mul_nonneg`, then transported to the `RC`
    quotient — using that `RCnonneg ⟦M⟧` is DEFINITIONALLY `geRat M 0`
    (`czero.approx = 0`);
  * `parseval_self := schur_self` verbatim (the summand IS `coeffSq`);
  * `parseval_T := schur_T` verbatim — because
    `rcScaleResidualPlus.RCscale λ ⟦A⟧` reduces DEFINITIONALLY to `⟦ofQ' λ · A⟧`
    (`RCscale_mk`, a `rfl`), which is exactly the `schur_T` summand.

# The honest residual (what remains open)

The two hypotheses `schur_self` / `schur_T` ARE the standard, citable
Osterwalder–Seiler / Peter–Weyl Schur-orthogonality input, now stated as finite
algebraic identities on the base reflection form realized in `cinner`, NOT an
integral wall.  They are carried as `Type`-level premises (Rule 8), not proved.
The scalar-order monotonicity of the scaling (`Rscalar`, needed only for the
final form-gap composition `wilsonFormGap`) is likewise threaded as a premise —
it is monotonicity of `RCscale` in its SCALAR (distinct from the argument-
monotonicity `RCscale_mono` already proved), left open here.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonSpectralBridge
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.ReflectionPositivity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.CharacterDiagResolutionProof

/-! ## 1. The `geRat → RCnonneg` transport (definitional) -/

/-- **Nonnegativity transports from `geRat` to the `RC` quotient.**  `RCnonneg ⟦M⟧`
is `RCle ⟦czero⟧ ⟦M⟧`, which reduces (through the `Quotient.lift₂` of `RCle`) to
`leEv czero M`; since `czero.approx n = 0` definitionally, that is exactly
`geRat M 0`.  So a `geRat M 0` proof IS an `RCnonneg ⟦M⟧` proof. -/
theorem rcnonneg_mk_of_geRat {M : CReal} (h : ExpPos.geRat M 0) :
    CReal.RCnonneg (Quotient.mk CReal.crealSetoid M) := h

/-- **The reflection-weighted squared coefficient is nonnegative in `RC`.**
`μ_i · c_i² ≥ 0` (product of the nonneg reflection weight `e^{−t·C₂(i+1)}` and the
square `c_i²`), lifted to the `RC` quotient. -/
theorem reflCoeffSq_nonneg (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) (c : Q') :
    CReal.RCnonneg
      (Quotient.mk CReal.crealSetoid
        (CReal.mul (reflWeight t ht s) (CReal.ofQ' (c * c)))) :=
  rcnonneg_mk_of_geRat
    (CReal.mul_nonneg (reflWeight_nonneg t ht s)
      (SumOfSquares.geRat_ofQ'_nonneg (SumOfSquares.q_mul_self_nonneg c)))

/-! ## 2. The reduction: `CharacterDiagResolution` from two Schur identities -/

/-- **The physical finite-volume Wilson `CharacterDiagResolution`.**

Given the two diagonal Schur / Peter–Weyl identities `schur_self` / `schur_T`
realized in `cinner` (with the character coordinate map `coord`, the reflection
weight `μ_i = reflWeight t ht (i+1)` and the heat-kernel eigenvalue
`λ_i = qpow w (c4 (i+1))`), the `CharacterDiagResolution` for the concrete
scaling `rcScaleResidualPlus` is inhabited:

  * `coeffSq x i := ⟦ μ_i · c_i² ⟧`, nonneg by `reflCoeffSq_nonneg`;
  * `parseval_self := schur_self` (the summand IS `coeffSq`);
  * `parseval_T := schur_T`, because `rcScaleResidualPlus.RCscale λ ⟦A⟧` reduces
    definitionally (`RCscale_mk`) to `⟦ ofQ' λ · A ⟧`, the `schur_T` summand. -/
def wilsonCharacterDiagResolution
    {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w t : Q') (ht : (0 : Q') ≤ t) (N : Nat)
    (coord : H.hilbert.carrier → Fin N → Q')
    (schur_self : ∀ x, H.hilbert.cinner x x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (reflWeight t ht (i.val + 1))
                (CReal.ofQ' (coord x i * coord x i)))))
    (schur_T : ∀ x, H.hilbert.cinner (op.T x) x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
                (CReal.mul (reflWeight t ht (i.val + 1))
                  (CReal.ofQ' (coord x i * coord x i)))))) :
    CharacterDiagResolution op rcScaleResidualPlus w N where
  coeffSq := fun x i =>
    Quotient.mk CReal.crealSetoid
      (CReal.mul (reflWeight t ht (i.val + 1)) (CReal.ofQ' (coord x i * coord x i)))
  coeffSq_nonneg := fun x i =>
    reflCoeffSq_nonneg t ht (i.val + 1) (coord x i)
  parseval_self := schur_self
  parseval_T := schur_T

/-! ## 3. The payoff: firing the operator-form gap -/

/-- **The finite-volume Wilson operator-form gap from the two Schur identities.**
Composes `wilsonCharacterDiagResolution` with the already-proved
`wilsonTransferFormGap`: on `vac⊥`, `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩`.

The remaining premise `Rscalar` is the scalar-order monotonicity of the scaling
(distinct from the argument-monotonicity `RCscale_mono` already discharged in
`rcScaleResidualPlus`); it is threaded here as the single honest residual
alongside the two Schur identities. -/
def wilsonFormGap
    {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (rcScaleResidualPlus.RCscale s c) (rcScaleResidualPlus.RCscale t c))
    (coord : H.hilbert.carrier → Fin N → Q')
    (schur_self : ∀ x, H.hilbert.cinner x x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (reflWeight t ht (i.val + 1))
                (CReal.ofQ' (coord x i * coord x i)))))
    (schur_T : ∀ x, H.hilbert.cinner (op.T x) x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
                (CReal.mul (reflWeight t ht (i.val + 1))
                  (CReal.ofQ' (coord x i * coord x i)))))) :
    TransferFormGapResidual (excitedCharSpectralGapData op w hw0 hw1 N) :=
  wilsonTransferFormGap op w hw0 hw1 N rcScaleResidualPlus Rscalar
    (wilsonCharacterDiagResolution op w t ht N coord schur_self schur_T)

end YMGap.Continuum.CharacterDiagResolutionProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CharacterDiagResolutionProof.rcnonneg_mk_of_geRat
#print axioms YMGap.Continuum.CharacterDiagResolutionProof.reflCoeffSq_nonneg
#print axioms YMGap.Continuum.CharacterDiagResolutionProof.wilsonCharacterDiagResolution
#print axioms YMGap.Continuum.CharacterDiagResolutionProof.wilsonFormGap
