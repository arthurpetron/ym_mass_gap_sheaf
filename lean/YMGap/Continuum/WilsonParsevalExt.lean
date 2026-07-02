/-
Track 4 — the two *genuine new* Parseval inputs of `WilsonTowerParseval`
(R1 `parseval_offdiag`, R2 `parseval_Tsq`) discharged on the CONCRETE
character-diagonal carrier `charHilbert` / `charTransfer`.

# What this module delivers

`Continuum/WilsonLinearFC.lean` packages the diagonal Peter–Weyl data PLUS two
"genuine new inputs" as `WilsonTowerParseval`:

  * **R1 `parseval_offdiag`** — off-diagonal self-adjointness `⟨Tx,y⟩ = ⟨x,Ty⟩`;
  * **R2 `parseval_Tsq`**      — the square resolution `⟨Tx,Tx⟩ = Σ λᵢ²·|cᵢ|²`.

On the concrete character carrier of `Continuum/WilsonSchurIdentities.lean` — where
the inner product is manifestly bilinear-diagonal
`⟨a,b⟩ = ⟦ Σ_{s<N} μ_s·(a_s·b_s) ⟧` (μ_s = `reflWeight t ht (s+1)`) and the
transfer operator is `T c s = λ_s·c_s` (λ_s = `qpow w (c4 (s+1))`) — BOTH of these
collapse to elementary algebra:

  * **R1 is FREE, verbatim.**  `parseval_offdiag` is literally the already-proved
    `charTransfer.selfAdjoint` field (`q_selfAdj`, no new lemma).
  * **R2 needs ONE `Q'` rearrangement + ONE clone of `charSchurT`.**
    `q_rearrange_schurTsq` is the `l ↦ l·l` sibling of `q_rearrange_schurT`
    (3 lines, seeded by `q_sq_regroup`); `charSchurTsq` is a copy of `charSchurT`
    with the summand rearrangement swapped and the eigenvalue squared.

We then assemble, mirroring `wilsonCharacterDiagResolution`, a
`WilsonTowerParsevalOp` (the operator-carrier restatement of `WilsonTowerParseval`,
against `TransferOperator H` on `H.hilbert.cinner` — Option 1 of the plan) and
inhabit it UNCONDITIONALLY with the six field assignments.

## Genuine content proved here (green)

  * `q_rearrange_schurTsq` — `(m·((l·y)(l·y))) ≃ (l·l)·(m·(y·y))`, the R2 summand
    rearrangement (pull the squared eigenvalue out, regroup the reflection weight).
  * `charSchurTsq` — R2 on the concrete carrier:
    `⟨Tx,Tx⟩ = Σ_{i<N} ⟦ λᵢ² · (μᵢ · xᵢ²) ⟧`, a pure `RCfinSum`↔`csum` repackaging.
  * `charParsevalOffdiag` — R1 on the concrete carrier, = `charTransfer.selfAdjoint`.
  * `WilsonTowerParsevalOp` + `wilsonTowerParsevalConcrete` — the operator-carrier
    Parseval datum, all four `cinner`-identities discharged (the two diagonal ones
    from `charSchurSelf`/`charSchurT`, plus R1/R2).

## Honest residual (named, not faked)

  * **`SymbolTypedParseval`** — the `DiagonalTransferSymbol`-typed
    `WilsonLinearFC.WilsonTowerParseval` (the form `wilsonLinearTransfer` consumes)
    is typed over `S.TqSymb` and the CANONICAL completion
    `D.toGNSData.gnsComplete.hilbert.cinner`.  The concrete carrier here uses the
    DIRECTLY-defined `charHilbert.cinner` (bypassing the canonical completion) and
    `charTransfer.T ≠ S.TqSymb` definitionally; so the concrete R1/R2 content does
    NOT populate the `S`-typed structure without a symbol/canonical-completion
    identification (Option 2).  That identification is named here as a `Type`-level
    residual, never faked.  (On the concrete carrier itself `charTransfer` is
    already a full `TransferOperator`, so the operator-carrier `WilsonTowerParsevalOp`
    IS inhabited above.)

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonSchurIdentities
import YMGap.Continuum.WilsonLinearFC

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.CharacterDiagResolutionProof
open YMGap.Continuum.WilsonSchurIdentities

namespace YMGap.Continuum.WilsonParsevalExt

/-! ## 1. The R2 summand rearrangement (new, 3 lines) -/

/-- **The R2 (`parseval_Tsq`) summand rearrangement.**  `(m·((l·y)(l·y))) ≃
(l·l)·(m·(y·y))` — the `l ↦ l·l` sibling of `q_rearrange_schurT`, seeded by
`q_sq_regroup`: pull the SQUARED eigenvalue `l·l` out and regroup the reflection
weight `m`. -/
theorem q_rearrange_schurTsq (m l y : Q') :
    (m * ((l * y) * (l * y))).eqv ((l * l) * (m * (y * y))) := by
  have h1 : (m * ((l * y) * (l * y))).eqv (m * ((l * l) * (y * y))) :=
    Q'.mul_eqv_congr_left m _ _ (q_sq_regroup l y)
  have t3 : (m * ((l * l) * (y * y))).eqv (((l * l) * m) * (y * y)) := by
    have a1 : (m * ((l * l) * (y * y))).eqv ((m * (l * l)) * (y * y)) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv m (l * l) (y * y))
    have a2 : ((m * (l * l)) * (y * y)).eqv (((l * l) * m) * (y * y)) :=
      Q'.mul_eqv_congr_right (m * (l * l)) ((l * l) * m) (y * y) (Q'.mul_comm_eqv m (l * l))
    exact Q'.eqv_trans _ _ _ a1 a2
  have t5 : (((l * l) * m) * (y * y)).eqv ((l * l) * (m * (y * y))) :=
    Q'.mul_assoc_eqv (l * l) m (y * y)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ t3 t5)

/-! ## 2. R2 on the concrete carrier: `charSchurTsq` (clone of `charSchurT`) -/

/-- **R2 `parseval_Tsq` on the character-diagonal carrier.**  The square resolution
`⟨Tx,Tx⟩ = Σ_{i<N} ⟦ λᵢ² · (μᵢ · xᵢ²) ⟧` — a pure `RCfinSum`↔`csum` repackaging,
with the per-summand `Q'` rearrangement supplied by `q_rearrange_schurTsq`.
A verbatim clone of `charSchurT` with the summand rearrangement swapped and the
rational eigenvalue squared. -/
theorem charSchurTsq (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) (x : Nat → Q') :
    (charComplete t ht N).hilbert.cinner
        ((charTransfer w hw0 hw1 t ht N).T x) ((charTransfer w hw0 hw1 t ht N).T x)
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))))
              (CReal.mul (reflWeight t ht (i.val + 1)) (CReal.ofQ' (x i.val * x i.val))))) := by
  refine Eq.trans ?_ (RCfinSum_mk (fun s =>
      CReal.mul (CReal.ofQ' (qpow w (c4 (s + 1)) * qpow w (c4 (s + 1))))
        (CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s)))) N).symm
  exact Quotient.sound (csum_approx_congr
    (fun s => CReal.mul (reflWeight t ht (s + 1))
        (CReal.ofQ' ((qpow w (c4 (s + 1)) * x s) * (qpow w (c4 (s + 1)) * x s))))
    (fun s => CReal.mul (CReal.ofQ' (qpow w (c4 (s + 1)) * qpow w (c4 (s + 1))))
        (CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s))))
    (fun s p => q_rearrange_schurTsq ((reflWeight t ht (s + 1)).approx p)
                  (qpow w (c4 (s + 1))) (x s))
    N)

/-! ## 3. R1 on the concrete carrier: `charParsevalOffdiag` (FREE) -/

/-- **R1 `parseval_offdiag` on the character-diagonal carrier — FREE.**  The
off-diagonal self-adjointness `⟨Tx,y⟩ = ⟨x,Ty⟩` is literally the already-proved
`charTransfer.selfAdjoint` field (proved via `q_selfAdj`). -/
theorem charParsevalOffdiag (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) (x y : Nat → Q') :
    (charComplete t ht N).hilbert.cinner ((charTransfer w hw0 hw1 t ht N).T x) y
      = (charComplete t ht N).hilbert.cinner x ((charTransfer w hw0 hw1 t ht N).T y) :=
  (charTransfer w hw0 hw1 t ht N).selfAdjoint x y

/-! ## 4. The operator-carrier Parseval datum (Option 1 restatement) -/

/-- **The Wilson tower Parseval datum against a `TransferOperator H`** (the
operator-carrier restatement of `WilsonLinearFC.WilsonTowerParseval`, exactly as
`WilsonSpectralBridge.CharacterDiagResolution` is stated — Option 1 of the plan).
Adds to the diagonal data (`parseval_self`, `parseval_T`) the two genuine new
inputs R1 (`parseval_offdiag`) and R2 (`parseval_Tsq`). -/
structure WilsonTowerParsevalOp {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (R : RCScaleResidualPlus) (w : Q') (N : Nat) : Type where
  /-- The squared character Fourier weights `|⟨χ_{i+1}, x⟩|²`. -/
  coeffSq : H.hilbert.carrier → Fin N → CReal.RC
  /-- The weights are nonnegative. -/
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  /-- Parseval / character orthonormality: `⟨x,x⟩ = Σ |cᵢ|²`. -/
  parseval_self : ∀ x, H.hilbert.cinner x x = CReal.RCfinSum N (coeffSq x)
  /-- Diagonal transfer action: `⟨Tx,x⟩ = Σ (w^{C₄(i+1)})·|cᵢ|²`. -/
  parseval_T : ∀ x, H.hilbert.cinner (op.T x) x
      = CReal.RCfinSum N (fun i => R.RCscale (qpow w (c4 (i.val + 1))) (coeffSq x i))
  /-- **R1** off-diagonal self-adjointness `⟨Tx,y⟩ = ⟨x,Ty⟩`. -/
  parseval_offdiag : ∀ x y, H.hilbert.cinner (op.T x) y = H.hilbert.cinner x (op.T y)
  /-- **R2** square resolution `⟨Tx,Tx⟩ = Σ (w^{C₄(i+1)})²·|cᵢ|²`. -/
  parseval_Tsq : ∀ x, H.hilbert.cinner (op.T x) (op.T x)
      = CReal.RCfinSum N (fun i =>
          R.RCscale (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))) (coeffSq x i))

/-- **The concrete Wilson tower Parseval datum, UNCONDITIONALLY.**  Mirrors
`wilsonCharacterDiagResolution` with the two extra fields R1/R2:

  * `coeffSq x i := ⟦ μᵢ · xᵢ² ⟧`, nonneg by `reflCoeffSq_nonneg`;
  * `parseval_self := charSchurSelf`, `parseval_T := charSchurT`
    (the summands ARE the fields, via `RCscale_mk` a `rfl`);
  * `parseval_offdiag := charTransfer.selfAdjoint` (R1, free);
  * `parseval_Tsq := charSchurTsq` (R2, the clone above; `RCscale_mk` again). -/
def wilsonTowerParsevalConcrete (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    WilsonTowerParsevalOp (charTransfer w hw0 hw1 t ht N) rcScaleResidualPlus w N where
  coeffSq := fun x i =>
    Quotient.mk CReal.crealSetoid
      (CReal.mul (reflWeight t ht (i.val + 1)) (CReal.ofQ' (x i.val * x i.val)))
  coeffSq_nonneg := fun x i => reflCoeffSq_nonneg t ht (i.val + 1) (x i.val)
  parseval_self := fun x => charSchurSelf t ht N x
  parseval_T := fun x => charSchurT w hw0 hw1 t ht N x
  parseval_offdiag := fun x y => charParsevalOffdiag w hw0 hw1 t ht N x y
  parseval_Tsq := fun x => charSchurTsq w hw0 hw1 t ht N x

/-! ## 5. The honest residual: the `DiagonalTransferSymbol`-typed form (Option 2) -/

/-- **Residual — the `DiagonalTransferSymbol`-typed `WilsonTowerParseval`.**

`wilsonLinearTransfer` (`Continuum/WilsonLinearFC.lean`) consumes the `S`-typed
`WilsonLinearFC.WilsonTowerParseval S R w N`, whose fields are hardwired to
`S.TqSymb x` and the CANONICAL completion `D.toGNSData.gnsComplete.hilbert.cinner`.
The concrete carrier of `Continuum/WilsonSchurIdentities.lean` uses the
DIRECTLY-defined `charHilbert.cinner` (bypassing that canonical completion) and
`charTransfer.T ≠ S.TqSymb` definitionally.  Populating the `S`-typed structure from
the concrete R1/R2 content (`wilsonTowerParsevalConcrete`) therefore requires a
`SmulGNSData D` and symbol `S` whose canonical completion reproduces the diagonal
reflection form and whose `TqSymb` equals the λ-action — the sole non-free piece
(Option 2).  Named here as a `Type`-level residual (Rule 8), never faked. -/
structure SymbolTypedParseval (w : Q') (N : Nat) : Type 1 where
  /-- The scaling module underlying the canonical completion. -/
  D : SmulGNSData
  /-- The diagonal transfer symbol whose `TqSymb` is the λ-action. -/
  S : DiagonalTransferSymbol D
  /-- The `RC`-scaling residual. -/
  R : RCScaleResidualPlus
  /-- The realized `S`-typed Parseval datum (the open Option-2 target). -/
  parseval : YMGap.Continuum.WilsonLinearFC.WilsonTowerParseval S R w N

end YMGap.Continuum.WilsonParsevalExt

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonParsevalExt.q_rearrange_schurTsq
#print axioms YMGap.Continuum.WilsonParsevalExt.charSchurTsq
#print axioms YMGap.Continuum.WilsonParsevalExt.charParsevalOffdiag
#print axioms YMGap.Continuum.WilsonParsevalExt.wilsonTowerParsevalConcrete
