/-
Inhabiting `LinearTransferOperator` for the genuine Wilson character tower — the
honest three-input completion of `DiagonalTransferSymbol.toLinearTransfer`.

# What this module adds (all axiom-clean)

`Continuum/LinearTransferOperator.lean` gives `DiagonalTransferSymbol.toLinearTransfer`:
from a carrier symbol `S` it supplies the operator-LINEARITY half
(`T_add`/`T_smul`/rep-lift) unconditionally, and exposes the three `cinner`-level
OS axioms of `S.TqSymb` — self-adjointness / positivity / contraction — as explicit
inputs.  `Continuum/WilsonSpectralBridge.lean`'s `CharacterDiagResolution` carries
the DIAGONAL Peter–Weyl data (`parseval_self`, `parseval_T`), i.e. the forms
`⟨x,x⟩` and `⟨Tx,x⟩` only.  That diagonal datum delivers exactly ONE of the three
`toLinearTransfer` hypotheses (`positive`, from `parseval_T`); the other two need
genuinely more:

  * self-adjointness needs the OFF-diagonal `⟨Tx,y⟩ = ⟨x,Ty⟩` (`parseval_offdiag`),
    which no diagonal `⟨·,·⟩`-form supplies;
  * contraction needs the SQUARE form `⟨Tx,Tx⟩` (`parseval_Tsq`), absent from
    `CharacterDiagResolution`.

We package the diagonal data PLUS these two genuine new inputs as
`WilsonTowerParseval` (R1 `parseval_offdiag`, R2 `parseval_Tsq`, exposed as named
`Type`-level fields, never faked), and derive all three `toLinearTransfer`
hypotheses from it, landing `wilsonLinearTransfer` — a legitimate inhabitant of
`LinearTransferOperator` for the Wilson tower.

## Genuine content proved here (green)

  * `RCadd_nonneg` / `RCfinSum_nonneg` — nonnegativity is closed under `RCadd` and
    under finite `RC`-sums (the `RC` companions of `RCfinSum_mono`).
  * `qpow_sq_le_one` — `λᵢ² = (w^{C₄(i+1)})² ≤ 1` for `0 ≤ w ≤ 1`, a 3-line sibling
    of `casimir_qpow_le` off `qpow_ge_shift … 0 (c4 (i+1))` (`λᵢ ≤ w⁰ = 1`).
  * `wilson_positive` — `hpos` from `parseval_T` + `RCfinSum_nonneg`.
  * `wilson_contraction` — `hcon` from `parseval_Tsq` + `parseval_self`, reduced
    termwise via `RCfinSum_mono` to `λᵢ² ≤ 1` (`qpow_sq_le_one`) + `RCscale 1 = id`.
  * `wilsonLinearTransfer` — the assembled `LinearTransferOperator D`.

## Honest residuals (named, not faked)

  * **R1 `parseval_offdiag`, R2 `parseval_Tsq`** — the two genuine inputs beyond
    the diagonal Peter–Weyl data, carried as fields of `WilsonTowerParseval`.
  * **R3 `RCDistBridge`** — the RC-norm ↔ rational `distSqQ` modulus bridge that
    would build `PolyImageCauchy` (the continuous functional calculus limit) and
    pass self-adjointness / norm bounds through `carrierLimit`.  Named here as a
    `Type`-level residual; it is orthogonal to the Wilson-tower inhabitation and
    remains the blocking analytic input for the CONTINUOUS calculus.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.LinearTransferOperator
import YMGap.Continuum.WilsonSpectralBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonSpectralBridge

/-! ## 0. Nonnegativity of finite `RC`-sums (companions of `RCfinSum_mono`) -/

namespace YMGap.Constructive.CReal

/-- **`RCadd` preserves nonnegativity.**  `0 ≤ a → 0 ≤ b → 0 ≤ a + b`, from the
additive monotonicity `RCadd_le_add` and `RCadd RCzero RCzero = RCzero`. -/
theorem RCadd_nonneg {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h : RCle (RCadd RCzero RCzero) (RCadd a b) := RCadd_le_add ha hb
  have e : RCadd RCzero RCzero = RCzero := by
    show RCadd (Quotient.mk crealSetoid czero) (Quotient.mk crealSetoid czero)
        = Quotient.mk crealSetoid czero
    rw [RCadd_mk]
    exact Quotient.sound
      (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_add_eqv (czero.approx n)))
  rw [e] at h
  exact h

/-- **Finite `RC`-sums of nonnegative terms are nonnegative.**  Induction along
`RCfinSum`, base `RCzero` by `RCle_refl`, step by `RCadd_nonneg`. -/
theorem RCfinSum_nonneg :
    {k : Nat} → {f : Fin k → RC} → (∀ i, RCnonneg (f i)) → RCnonneg (RCfinSum k f)
  | 0, _, _ => RCle_refl _
  | (k + 1), f, h =>
      RCadd_nonneg
        (RCfinSum_nonneg (f := fun i => f i.castSucc) (fun i => h i.castSucc))
        (h (Fin.last k))

end YMGap.Constructive.CReal

namespace YMGap.Continuum.WilsonLinearFC

/-! ## 1. The square-Casimir bound `λᵢ² ≤ 1` -/

/-- **`λᵢ² ≤ 1`** for the heat-kernel eigenvalues.  `λᵢ = w^{C₄(i+1)} ≤ w⁰ = 1`
(from `qpow_ge_shift` at base exponent `0`), and `0 ≤ λᵢ`, so `λᵢ·λᵢ ≤ 1·1 = 1`.
A 3-line square-sibling of `casimir_qpow_le`. -/
theorem qpow_sq_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (i : Nat) :
    qpow w (c4 (i + 1)) * qpow w (c4 (i + 1)) ≤ (1 : Q') := by
  have hle1 : qpow w (c4 (i + 1)) ≤ (1 : Q') := by
    have h := qpow_ge_shift hw0 hw1 0 (c4 (i + 1))
    rw [Nat.zero_add, qpow_zero] at h
    exact h
  have hnn : (0 : Q') ≤ qpow w (c4 (i + 1)) := qpow_nonneg w hw0 _
  have s1 : qpow w (c4 (i + 1)) * qpow w (c4 (i + 1))
      ≤ qpow w (c4 (i + 1)) * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left (qpow w (c4 (i + 1))) (1 : Q') (qpow w (c4 (i + 1)))
      hle1 hnn
  have s2 : qpow w (c4 (i + 1)) * (1 : Q') ≤ (1 : Q') :=
    le_of_eqv_le (Q'.mul_one_eqv (qpow w (c4 (i + 1)))) hle1
  exact Q'.le_trans' _ _ _ s1 s2

/-! ## 2. `WilsonTowerParseval`: the diagonal data PLUS the two genuine inputs -/

variable {D : SmulGNSData}

/-- **The Wilson character-tower Parseval datum for `S.TqSymb`.**  The squared
character Fourier weights and the four `cinner`-level identities realized inside the
completed GNS inner product of `D`.  The first two (`parseval_self`, `parseval_T`)
are the diagonal Peter–Weyl data (verbatim from `CharacterDiagResolution`, with
`T := S.TqSymb`).  The last two are the genuinely new inputs beyond the diagonal
forms:

  * **R1 `parseval_offdiag`** — off-diagonal self-adjointness `⟨Tx,y⟩ = ⟨x,Ty⟩`;
  * **R2 `parseval_Tsq`** — the square resolution `⟨Tx,Tx⟩ = Σ λᵢ²·|cᵢ|²`.

Carried as `Type`-level data (Rule 8): standard Osterwalder–Seiler / Peter–Weyl
input, NOT proved here. -/
structure WilsonTowerParseval (S : DiagonalTransferSymbol D)
    (R : RCScaleResidualPlus) (w : Q') (N : Nat) : Type where
  /-- The squared character Fourier weights `|⟨χ_{i+1}, x⟩|²`. -/
  coeffSq : D.toGNSData.gnsComplete.hilbert.carrier → Fin N → CReal.RC
  /-- The weights are nonnegative. -/
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  /-- Parseval / character orthonormality: `⟨x,x⟩ = Σ |cᵢ|²`. -/
  parseval_self : ∀ x, D.toGNSData.gnsComplete.hilbert.cinner x x
      = CReal.RCfinSum N (coeffSq x)
  /-- Diagonal transfer action: `⟨Tx,x⟩ = Σ (w^{C₄(i+1)})·|cᵢ|²`. -/
  parseval_T : ∀ x, D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) x
      = CReal.RCfinSum N (fun i => R.RCscale (qpow w (c4 (i.val + 1))) (coeffSq x i))
  /-- **R1** off-diagonal self-adjointness `⟨Tx,y⟩ = ⟨x,Ty⟩`. -/
  parseval_offdiag : ∀ x y, D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) y
      = D.toGNSData.gnsComplete.hilbert.cinner x (S.TqSymb y)
  /-- **R2** square resolution `⟨Tx,Tx⟩ = Σ (w^{C₄(i+1)})²·|cᵢ|²`. -/
  parseval_Tsq : ∀ x, D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) (S.TqSymb x)
      = CReal.RCfinSum N (fun i =>
          R.RCscale (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))) (coeffSq x i))

/-! ## 3. Deriving the three `toLinearTransfer` hypotheses -/

/-- **`hpos` — positivity `⟨Tx,x⟩ ≥ 0`** from `parseval_T`.  Each summand
`R.RCscale (w^{C₄(i+1)} ≥ 0) (|cᵢ|² ≥ 0)` is nonnegative (via `Rnonneg`), so their
`RCfinSum` is nonnegative (`RCfinSum_nonneg`). -/
theorem wilson_positive {S : DiagonalTransferSymbol D} {R : RCScaleResidualPlus}
    {w : Q'} {N : Nat} (P : WilsonTowerParseval S R w N) (hw0 : (0 : Q') ≤ w)
    (Rnonneg : ∀ {s : Q'}, (0 : Q') ≤ s → ∀ {c : CReal.RC},
      CReal.RCnonneg c → CReal.RCnonneg (R.RCscale s c)) :
    ∀ x, CReal.RCnonneg
        (D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) x) := by
  intro x
  rw [P.parseval_T x]
  exact RCfinSum_nonneg (fun i =>
    Rnonneg (qpow_nonneg w hw0 (c4 (i.val + 1))) (P.coeffSq_nonneg x i))

/-- **`hcon` — contraction `⟨Tx,Tx⟩ ≤ ⟨x,x⟩`** from `parseval_Tsq` + `parseval_self`.
Rewrite both sides to their Parseval sums, then reduce termwise via `RCfinSum_mono`
to `R.RCscale (λᵢ²) |cᵢ|² ≤ R.RCscale 1 |cᵢ|² = |cᵢ|²`, discharged by `Rscalar`
applied to `qpow_sq_le_one` and `Rone`. -/
theorem wilson_contraction {S : DiagonalTransferSymbol D} {R : RCScaleResidualPlus}
    {w : Q'} {N : Nat} (P : WilsonTowerParseval S R w N)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (R.RCscale s c) (R.RCscale t c))
    (Rone : ∀ c : CReal.RC, R.RCscale (1 : Q') c = c) :
    ∀ x, CReal.RCle
        (D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) (S.TqSymb x))
        (D.toGNSData.gnsComplete.hilbert.cinner x x) := by
  intro x
  rw [P.parseval_Tsq x, P.parseval_self x]
  refine RCfinSum_mono (fun i => ?_)
  have h1 : CReal.RCle
      (R.RCscale (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))) (P.coeffSq x i))
      (R.RCscale (1 : Q') (P.coeffSq x i)) :=
    Rscalar (qpow_sq_le_one hw0 hw1 i.val) (P.coeffSq_nonneg x i)
  rw [Rone (P.coeffSq x i)] at h1
  exact h1

/-! ## 4. Assembling the inhabitant -/

/-- **`wilsonLinearTransfer` — the Wilson character tower as a
`LinearTransferOperator`.**  Feeds `DiagonalTransferSymbol.toLinearTransfer` the
three derived hypotheses: `hsa := P.parseval_offdiag` (R1), `hpos` from
`wilson_positive`, `hcon` from `wilson_contraction`.  The `R`-side inputs
(`Rnonneg`, `Rscalar`, `Rone`) are the standard scalar-order laws of the
`RC`-scaling (`Rscalar`, `Rnonneg` are already threaded in `wilsonTransferSpectralBridge`;
`Rone` is `RCscale_one` for the concrete scaling). -/
def wilsonLinearTransfer (S : DiagonalTransferSymbol D) (R : RCScaleResidualPlus)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat)
    (P : WilsonTowerParseval S R w N)
    (Rnonneg : ∀ {s : Q'}, (0 : Q') ≤ s → ∀ {c : CReal.RC},
      CReal.RCnonneg c → CReal.RCnonneg (R.RCscale s c))
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (R.RCscale s c) (R.RCscale t c))
    (Rone : ∀ c : CReal.RC, R.RCscale (1 : Q') c = c)
    (vac : D.toGNSData.gnsComplete.hilbert.carrier) :
    LinearTransferOperator D :=
  S.toLinearTransfer vac P.parseval_offdiag
    (wilson_positive P hw0 Rnonneg)
    (wilson_contraction P hw0 hw1 Rscalar Rone)

/-! ## 5. The blocking analytic residual R3 (named, not faked)

The CONTINUOUS functional calculus (`fcApply = lim_n pₙ(T)x`, its self-adjointness
and norm bound) is orthogonal to the Wilson-tower inhabitation above.  It is gated
on exactly one missing bridge: converting the RC-norm smallness
`RCle ‖·‖²_RC (RCscale M ‖x‖²)` into an eventual rational `distSqQ ≤ ε` at
representatives (to feed `GeneralCompletionCauchy` and to pass equalities through
`carrierLimit`).  We name it here as a `Type`-level residual — never faked. -/

/-- **R3 — the RC ↔ rational-`distSqQ` modulus bridge.**  For a completion point
`z` and a nonnegative `RC` bound `B`, if the completed self-inner product
`⟨z,z⟩` is `RCle` a scaled bound, this datum extracts, at representatives, an
eventual rational squared-distance modulus.  This is the exact input that would
build `PolyImageCauchy` (`Continuum/ContinuousFCCarrierLimit.lean`) and pass
`polyApply` self-adjointness / norm bounds through the carrier limit; it does not
exist in this branch. -/
structure RCDistBridge (D : GNSData) : Type where
  /-- From an `RC`-order self-inner bound to a rational squared-distance modulus at
  representatives. -/
  toDistSqModulus :
    ∀ (x y : CauchyGNS D) (B : Q'),
      CReal.RCle (D.cinnerCompl (Quotient.mk (cauchySetoid D) x)
                                (Quotient.mk (cauchySetoid D) y))
                 (Quotient.mk crealSetoid (CReal.ofQ' B)) →
      ∀ ε : Q', (0 : Q') < ε → ∃ Nz : Nat, ∀ n : Nat, Nz ≤ n →
        D.distSqQ (x.seq n) (y.seq n) ≤ B + ε

end YMGap.Continuum.WilsonLinearFC

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.RCadd_nonneg
#print axioms YMGap.Constructive.CReal.RCfinSum_nonneg
#print axioms YMGap.Continuum.WilsonLinearFC.qpow_sq_le_one
#print axioms YMGap.Continuum.WilsonLinearFC.wilson_positive
#print axioms YMGap.Continuum.WilsonLinearFC.wilson_contraction
#print axioms YMGap.Continuum.WilsonLinearFC.wilsonLinearTransfer
