/-
The OPERATOR-LINEARITY layer of the transfer operator on the completed GNS
Hilbert space: the structure `LinearTransferOperator` extending
`AdditiveTransferOperator` with the two data that `ContinuousFCCarrierLimit.lean`
names as its residuals (1) and (2) — a representative-level lift of `T` and the
scalar-homogeneity `T (c·x) = c·(T x)` — together with the carrier-level symbol
`DiagonalTransferSymbol` (the character tower `Dv`, `|λ_i| ≤ 1`) that inhabits it.

# What this module adds (all axiom-clean)

A `DiagonalTransferSymbol D` is a carrier map `Dv : V → V` with a squared-distance
contraction `d²(Dv a, Dv b) ≤ d²(a,b)` (the carrier form of
`TransferOperator.contraction`, i.e. `Σ λ_i²|c_i|² ≤ Σ|c_i|²` with `λ_i ≤ 1`) plus
additivity and scalar homogeneity on the carrier.  From those five fields the
representative-level machinery follows by copying, verbatim, the `cNeg` /
`cSmul` templates:

  * `cDiagCauchy` / `cDiagCauchy_null` — the pointwise `Dv`-image of a Cauchy
    representative is Cauchy (contraction transitivity), respecting `CauchyNull`;
  * `TqSymb` — the descended quotient map `⟦x⟧ ↦ ⟦Dv∘x⟧`, with `TqSymb_embed`;
  * `TqSymb_add` / `TqSymb_smul` — operator additivity and scalar-homogeneity,
    one-liners off `Dv_add` / `Dv_smul` through `rad_of_veq`.

These are exactly residuals (1) `T_ofCauchy`/`TCauchy` and (2) `T_smul` of
`Continuum/ContinuousFCCarrierLimit.lean` (header 57–66), which blocked presenting
`polyApply pₙ x` via representatives.

## What closes vs. what stays open (Rule 8, honest)

  * **Closes.**  `idLinearTransfer` fully inhabits `LinearTransferOperator` in the
    structural `λ ≡ 1` form (the degenerate character tower), mirroring
    `idAdditiveTransfer`: all of `T_add`, `T_smul`, and the rep-lift by `rfl`.

  * **Reduces (honest constructor).**  `DiagonalTransferSymbol.toLinearTransfer`
    turns ANY symbol `S` PLUS the three cinner-level OS axioms of `TqSymb S`
    (self-adjointness / positivity / contraction) into a full
    `LinearTransferOperator`.  The symbol supplies the operator-LINEARITY half
    (`T_add`/`T_smul`/rep-lift) unconditionally; the OS axioms — for the genuine
    Wilson tower these are the diagonal Peter–Weyl / Osterwalder–Seiler identities
    (`CharacterDiagResolution` in `Continuum/WilsonSpectralBridge.lean`) — remain
    the open cinner-level input, here exposed as explicit hypotheses rather than
    faked.  Residual (3) (`RC` Cauchy–Schwarz) is orthogonal and untouched.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HamiltonianScalar

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Continuum

/-! ## The linear transfer operator: operator-linearity + representative lift -/

/-- A **linear transfer operator** on the concrete GNS completion.  Extends the
additive-linear, reflection-positive `AdditiveTransferOperator` with the two data
that the continuous-functional-calculus carrier limit requires but the additive
interface does not expose:

  * a representative-level lift `TCauchy` of the quotient map `T` (residual (1)),
  * scalar-homogeneity `T (c·x) = c·(T x)` (residual (2)).

`T_add` (additivity) is inherited; together `T_add` + `T_smul` are full
`Q'`-linearity of the formed operator. -/
structure LinearTransferOperator (D : SmulGNSData)
    extends AdditiveTransferOperator D.toGNSData where
  /-- Representative-level lift of `T` (mirrors `cAddCauchy` / `cSmulCauchy`). -/
  TCauchy       : CauchyGNS D.toGNSData → CauchyGNS D.toGNSData
  /-- The lift respects the null relation. -/
  TCauchy_null  : ∀ {x x'}, CauchyNull D.toGNSData x x' →
                    CauchyNull D.toGNSData (TCauchy x) (TCauchy x')
  /-- The lift descends to the inherited quotient map `T`. -/
  T_ofCauchy    : ∀ x, toTransferOperator.T (Quotient.mk (cauchySetoid D.toGNSData) x)
                      = Quotient.mk (cauchySetoid D.toGNSData) (TCauchy x)
  /-- Scalar-homogeneity `T (c·x) = c·(T x)` (closes residual (2)). -/
  T_smul        : ∀ (s : Q') x, toTransferOperator.T (D.cSmul s x)
                      = D.cSmul s (toTransferOperator.T x)

/-! ## The carrier-level symbol that inhabits it (the character tower) -/

/-- A **diagonal transfer symbol**: a carrier map `Dv` that contracts squared
distances (`|λ_i| ≤ 1`) and is additive + scalar-homogeneous.  For the physical
Wilson `T` this is the single-slice heat-kernel character tower, with
`λ_i = qpow w (c4 (i+1)) ≤ 1` supplying `distSqQ_Dv`
(`= Σ λ_i²|c_i|² ≤ Σ|c_i|²`, the carrier form of `TransferOperator.contraction`). -/
structure DiagonalTransferSymbol (D : SmulGNSData) where
  /-- The carrier symbol map. -/
  Dv         : D.toGNSData.V → D.toGNSData.V
  /-- `Dv` respects the carrier equivalence. -/
  Dv_congr   : ∀ {a b}, D.toGNSData.veq a b → D.toGNSData.veq (Dv a) (Dv b)
  /-- **Contraction** `d²(Dv a, Dv b) ≤ d²(a,b)` (`|λ_i| ≤ 1`). -/
  distSqQ_Dv : ∀ a b, D.toGNSData.distSqQ (Dv a) (Dv b) ≤ D.toGNSData.distSqQ a b
  /-- Additivity `Dv (a+b) ≈ Dv a + Dv b`. -/
  Dv_add     : ∀ a b, D.toGNSData.veq (Dv (D.toGNSData.add a b))
                        (D.toGNSData.add (Dv a) (Dv b))
  /-- Scalar homogeneity `Dv (s·a) ≈ s·(Dv a)`. -/
  Dv_smul    : ∀ s a, D.toGNSData.veq (Dv (D.toGNSData.smul s a))
                        (D.toGNSData.smul s (Dv a))

namespace DiagonalTransferSymbol

variable {D : SmulGNSData} (S : DiagonalTransferSymbol D)

/-! ### The representative-level lift (copies `cNegCauchy` / `cSmulCauchy`) -/

/-- **Step 1.**  The pointwise `Dv`-image of a Cauchy representative is Cauchy,
with the SAME modulus (contraction, no rescale). -/
def cDiagCauchy (x : CauchyGNS D.toGNSData) : CauchyGNS D.toGNSData where
  seq := fun n => S.Dv (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact Q'.le_trans' _ _ _ (S.distSqQ_Dv (x.seq p) (x.seq q))
      (x.isCauchy ε hε p q hp hq)

/-- **Step 2.**  `cDiagCauchy` respects `CauchyNull`. -/
theorem cDiagCauchy_null {x x' : CauchyGNS D.toGNSData}
    (hx : CauchyNull D.toGNSData x x') :
    CauchyNull D.toGNSData (S.cDiagCauchy x) (S.cDiagCauchy x') := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn =>
    Q'.le_trans' _ _ _ (S.distSqQ_Dv (x.seq n) (x'.seq n)) (hN n hn)⟩

/-- **Step 3.**  The descended quotient map `⟦x⟧ ↦ ⟦Dv∘x⟧` (copies `cNeg`). -/
def TqSymb : GNSCompletionSpace D.toGNSData → GNSCompletionSpace D.toGNSData :=
  Quotient.lift (fun x => Quotient.mk (cauchySetoid D.toGNSData) (S.cDiagCauchy x))
    (fun _ _ hx => Quotient.sound (S.cDiagCauchy_null hx))

/-- **Step 4.**  `TqSymb` extends `Dv` on the dense image (copies `cNeg_embed`). -/
theorem TqSymb_embed (a : D.toGNSData.V) :
    S.TqSymb (embedV D.toGNSData a) = embedV D.toGNSData (S.Dv a) := by
  apply Quotient.sound
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (D.toGNSData.rad_refl (S.Dv a))) (Q'.le_of_lt hε)⟩

/-- **Step 5.**  Operator additivity `TqSymb (x+y) = TqSymb x + TqSymb y`
(the `cSmul_cAdd` one-liner off `Dv_add`). -/
theorem TqSymb_add (x y : GNSCompletionSpace D.toGNSData) :
    S.TqSymb (D.toGNSData.cAdd x y)
      = D.toGNSData.cAdd (S.TqSymb x) (S.TqSymb y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  exact le_of_eqv_le (rad_of_veq D.toGNSData (S.Dv_add (u.seq n) (v.seq n)))
    (Q'.le_of_lt hε)

/-- **Step 6.**  Scalar-homogeneity `TqSymb (s·x) = s·(TqSymb x)`
(the same one-liner off `Dv_smul`). -/
theorem TqSymb_smul (s : Q') (x : GNSCompletionSpace D.toGNSData) :
    S.TqSymb (D.cSmul s x) = D.cSmul s (S.TqSymb x) := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  exact le_of_eqv_le (rad_of_veq D.toGNSData (S.Dv_smul s (u.seq n)))
    (Q'.le_of_lt hε)

/-! ### Assembling the inhabitant — honest split

The five symbol fields deliver operator-LINEARITY (`T_add`/`T_smul`) and the
representative lift (`TCauchy`/`TCauchy_null`/`T_ofCauchy`) for free.  A
`LinearTransferOperator` ALSO inherits the three cinner-level OS axioms of
`TransferOperator` (`selfAdjoint`/`positive`/`contraction`), which the carrier
symbol does not by itself deliver.  `toLinearTransfer` exposes those three as
explicit inputs — for the genuine Wilson tower they are the diagonal Peter–Weyl
identities (the open `CharacterDiagResolution`); we do not fake them. -/

/-- **Honest reduction.**  From a symbol `S`, a vacuum vector, and the three
cinner-level OS axioms of `TqSymb S`, assemble a full `LinearTransferOperator`.
The linearity half (`T_add`/`T_smul` + rep-lift) is discharged by `S`; the OS
axioms are the residual continuum input. -/
def toLinearTransfer
    (vac : D.toGNSData.gnsComplete.hilbert.carrier)
    (hsa : ∀ x y, D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) y
                = D.toGNSData.gnsComplete.hilbert.cinner x (S.TqSymb y))
    (hpos : ∀ x, CReal.RCnonneg
                (D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) x))
    (hcon : ∀ x, CReal.RCle
                (D.toGNSData.gnsComplete.hilbert.cinner (S.TqSymb x) (S.TqSymb x))
                (D.toGNSData.gnsComplete.hilbert.cinner x x)) :
    LinearTransferOperator D where
  toAdditiveTransferOperator :=
    { toTransferOperator :=
        { T := S.TqSymb
          vacuum := vac
          selfAdjoint := hsa
          positive := hpos
          contraction := hcon }
      T_add := S.TqSymb_add }
  TCauchy := S.cDiagCauchy
  TCauchy_null := S.cDiagCauchy_null
  T_ofCauchy := fun _ => rfl
  T_smul := S.TqSymb_smul

end DiagonalTransferSymbol

/-! ## Non-vacuity: the degenerate `λ ≡ 1` tower -/

/-- The **identity diagonal symbol** (`λ ≡ 1`, the degenerate character tower):
`Dv = id`, contraction by reflexivity, additivity/homogeneity by `veq_refl`. -/
def idDiagonalSymbol (D : SmulGNSData) : DiagonalTransferSymbol D where
  Dv := id
  Dv_congr := fun h => h
  distSqQ_Dv := fun a b => Q'.le_refl' (D.toGNSData.distSqQ a b)
  Dv_add := fun _ _ => D.toGNSData.veq_refl _
  Dv_smul := fun _ _ => D.toGNSData.veq_refl _

/-- **Non-vacuity of `LinearTransferOperator`.**  The identity transfer operator
is a linear transfer operator: `T_add`/`T_smul` and the representative lift all
hold by `rfl` (mirrors `idAdditiveTransfer`).  This is the diagonal
character-tower `T` in its structural `λ ≡ 1` form. -/
def idLinearTransfer (D : SmulGNSData) : LinearTransferOperator D where
  toAdditiveTransferOperator := D.toGNSData.idAdditiveTransfer
  TCauchy := id
  TCauchy_null := fun hx => hx
  T_ofCauchy := fun _ => rfl
  T_smul := fun _ _ => rfl

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DiagonalTransferSymbol.cDiagCauchy
#print axioms YMGap.Continuum.DiagonalTransferSymbol.cDiagCauchy_null
#print axioms YMGap.Continuum.DiagonalTransferSymbol.TqSymb
#print axioms YMGap.Continuum.DiagonalTransferSymbol.TqSymb_embed
#print axioms YMGap.Continuum.DiagonalTransferSymbol.TqSymb_add
#print axioms YMGap.Continuum.DiagonalTransferSymbol.TqSymb_smul
#print axioms YMGap.Continuum.DiagonalTransferSymbol.toLinearTransfer
#print axioms YMGap.Continuum.idDiagonalSymbol
#print axioms YMGap.Continuum.idLinearTransfer
