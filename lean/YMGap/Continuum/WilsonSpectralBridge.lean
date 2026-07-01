/-
The finite-volume SU(2) Wilson `TransferSpectralBridge`, reduced to ONE named
Peter–Weyl/Schur datum.

# What this module delivers

`HamiltonianScalar.TransferSpectralBridge G R` is the finite ONB coordinate
resolution of the transfer operator's quadratic form; once inhabited,
`TransferSpectralBridge.toFormGapResidual` (already proved, axiom-clean)
discharges the operator-form gap `⟨Tx,x⟩ ≤ sep·⟨x,x⟩` on `vac⊥`.

For the physical single-edge heat-kernel SU(2) transfer operator the model is the
vacuum-SUBTRACTED (excited-only) character tower: mode `i` (`i < N`) carries the
spin-`(i+1)` character `χ_{i+1}` with transfer eigenvalue `qpow w (c4 (i+1))`
(`= w^{C₄(i+1)}`, the single-slice heat-kernel eigenvalue) and multiplicity
`dimQ (i+1)`.  The vacuum mode `s = 0` (eigenvalue `1`) is EXCLUDED — it must be,
because `SpectralGapData.gap.bound` demands every eigenvalue clear the separator
`sep = w³ < 1`, which `λ₀ = 1` fails.  The excited-only model is the only
consistent choice.

## Genuine content proved here

  * `casimir_qpow_le` — the elementary Casimir monotonicity
    `qpow w (c4 (i+1)) ≤ heatKernelSep w = qpow w 3` for `0 ≤ w ≤ 1`.  Because
    `c4 (i+1) = (i+1)(i+3) ≥ 3` and a power of `w ∈ [0,1]` decreases in the
    exponent (`qpow_ge_shift`).  This is the whole of `eigen_le_sep`; the
    `vacPerp` hypothesis is not even needed (the bound holds for all `x`).
  * `excitedCharModel` / `excitedCharLocatedGap` / `excitedCharSpectralGapData`
    — the genuine excited-only `SpectralModel`, its `LocatedSpectralGap` (with
    `sep = heatKernelSep w`, `sep < 1` by `heatKernelSep_lt_one`), and the
    bundled `SpectralGapData` over any transfer operator.
  * `wilsonTransferSpectralBridge` — the reduction: given (i) the character
    diagonalization datum `CharacterDiagResolution` and (ii) the scalar-order
    monotonicity of the `RC`-scaling `R`, the bridge is inhabited and the
    finite-dim form-gap chain closes.

## The honest residual (the sharp wall)

`CharacterDiagResolution` bundles the Peter–Weyl / Schur orthonormality realized
INSIDE the completed GNS inner product `H.hilbert.cinner`: the squared character
Fourier weights `coeffSq x i` together with `parseval_self` (character
orthonormality, `⟨x,x⟩ = Σ |cᵢ|²`) and `parseval_T` (diagonal action of the
transfer operator, `⟨Tx,x⟩ = Σ (qpow w (c4 (i+1)))·|cᵢ|²`).  This is a strictly
weaker, standard Osterwalder–Seiler / Peter–Weyl input than the `P_N` walls; it
is carried here as a named `Type`-level datum (Rule 8), NOT proved.

The `RC`-scaling `R : RCScaleResidualPlus` is itself the already-named
`RCScaleResidual` residual of the codebase; it is kept as a parameter (together
with its scalar-order monotonicity), rather than fixing a concrete `RCmul`-based
instance, which keeps the reduction honest and the scope tight.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.HeatKernelGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.WilsonSpectralBridge

/-! ## 1. Casimir monotonicity of the heat-kernel eigenvalues -/

/-- **Powers of `w ∈ [0,1]` decrease in the exponent.**
`qpow w (m + k) ≤ qpow w m` (each extra factor of `w ≤ 1` can only shrink a
nonnegative power). -/
theorem qpow_ge_shift {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (m : Nat) :
    ∀ k, qpow w (m + k) ≤ qpow w m
  | 0 => Q'.le_refl' _
  | k + 1 => by
      have step : qpow w (m + (k + 1)) ≤ qpow w (m + k) := by
        show qpow w (m + k) * w ≤ qpow w (m + k)
        have h : qpow w (m + k) * w ≤ qpow w (m + k) * (1 : Q') :=
          Q'.mul_le_mul_of_nonneg_left w (1 : Q') (qpow w (m + k)) hw1
            (qpow_nonneg w hw0 (m + k))
        exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv (qpow w (m + k))))
      exact Q'.le_trans' _ _ _ step (qpow_ge_shift hw0 hw1 m k)

/-- **Casimir monotonicity.**  Every excited heat-kernel eigenvalue clears the
separator: `qpow w (c4 (i+1)) ≤ heatKernelSep w = qpow w 3` for `0 ≤ w ≤ 1`.
Because `c4 (i+1) = (i+1)(i+3) ≥ 3 = c4 1`, write `c4 (i+1) = 3 + d` and apply
`qpow_ge_shift`. -/
theorem casimir_qpow_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (i : Nat) :
    qpow w (c4 (i + 1)) ≤ heatKernelSep w := by
  show qpow w (c4 (i + 1)) ≤ qpow w 3
  have h3 : 3 ≤ c4 (i + 1) := by
    have hc : c4 (i + 1) = (i + 1) * (i + 3) := rfl
    rw [hc]
    calc 3 = 1 * 3 := (Nat.one_mul 3).symm
      _ ≤ (i + 1) * (i + 3) := Nat.mul_le_mul (Nat.le_add_left 1 i) (Nat.le_add_left 3 i)
  obtain ⟨d, hd⟩ := Nat.le.dest h3
  rw [← hd]
  exact qpow_ge_shift hw0 hw1 3 d

/-! ## 2. The excited-only character tower model and its located gap -/

/-- **The excited-only character tower** as a finite `SpectralModel`: `N` modes,
mode `i` (spin `i+1`) with multiplicity `dimQ (i+1)` and heat-kernel eigenvalue
`qpow w (c4 (i+1))`.  The vacuum mode `s = 0` (eigenvalue `1`) is excluded. -/
def excitedCharModel (w : Q') (hw0 : (0 : Q') ≤ w) (N : Nat) : SpectralModel where
  k := N
  w := fun i => dimQ (i + 1)
  lam := fun i => qpow w (c4 (i + 1))
  w_nonneg := fun i => dimQ_nonneg (i + 1)
  lam_nonneg := fun i => qpow_nonneg w hw0 (c4 (i + 1))

/-- **The located spectral gap** of the excited-only tower: separator
`sep = heatKernelSep w = w³`, strictly below the vacuum eigenvalue `1`
(`heatKernelSep_lt_one`), bounding every excited eigenvalue (`casimir_qpow_le`). -/
def excitedCharLocatedGap (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    LocatedSpectralGap (excitedCharModel w hw0 N) where
  sep := heatKernelSep w
  sep_lt_one := heatKernelSep_lt_one hw0 hw1
  bound := fun i => casimir_qpow_le hw0 (Q'.le_of_lt hw1) i

/-- **The excited-only `SpectralGapData`** over any transfer operator `op`:
bundles `op` with the excited character model and its located gap. -/
def excitedCharSpectralGapData {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) : SpectralGapData H where
  op := op
  model := excitedCharModel w hw0 N
  gap := excitedCharLocatedGap w hw0 hw1 N

/-! ## 3. The honest residual: character diagonalization inside `cinner` -/

/-- **Character diagonalization datum (the sharp Peter–Weyl / Schur wall).**

The squared character Fourier weights `coeffSq x i = |⟨χ_{i+1}, x⟩|²` together
with the two orthonormality/diagonality identities realized inside the completed
GNS inner product:

  * `parseval_self` : `⟨x,x⟩ = Σ_{i<N} |cᵢ|²`  (character orthonormality);
  * `parseval_T`    : `⟨Tx,x⟩ = Σ_{i<N} (qpow w (c4 (i+1)))·|cᵢ|²`
    (diagonal action of the single-slice heat-kernel transfer operator).

Carried as `Type`-level data (Rule 8): this is the standard Osterwalder–Seiler /
Peter–Weyl input, NOT proved here. -/
structure CharacterDiagResolution {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (R : RCScaleResidualPlus) (w : Q') (N : Nat) : Type where
  /-- The squared character Fourier weights `|⟨χ_{i+1}, x⟩|²`. -/
  coeffSq : H.hilbert.carrier → Fin N → CReal.RC
  /-- The weights are nonnegative (reflection positivity of the modulus²). -/
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  /-- Parseval / character orthonormality: `⟨x,x⟩ = Σ |cᵢ|²`. -/
  parseval_self : ∀ x, H.hilbert.cinner x x = CReal.RCfinSum N (coeffSq x)
  /-- Diagonal transfer action: `⟨Tx,x⟩ = Σ (qpow w (c4 (i+1)))·|cᵢ|²`. -/
  parseval_T : ∀ x,
    H.hilbert.cinner (op.T x) x
      = CReal.RCfinSum N (fun i => R.RCscale (qpow w (c4 (i.val + 1))) (coeffSq x i))

/-! ## 4. The reduction: inhabiting the `TransferSpectralBridge` -/

/-- **The finite-volume SU(2) Wilson `TransferSpectralBridge`.**

Given the character diagonalization datum `P` and the scalar-order monotonicity
`Rscalar` of the `RC`-scaling, the bridge is inhabited:

  * `coeffSq` / `coeffSq_nonneg` / `innerT_diag` / `innerSelf_diag` come verbatim
    from `P` (the `T`-diagonal eigenvalue `G.model.lam i = qpow w (c4 (i+1))` and
    the norm resolution ARE `parseval_T` / `parseval_self`);
  * `eigen_le_sep` is `Rscalar` applied to the elementary Casimir bound
    `casimir_qpow_le` — the `vacPerp` hypothesis is not needed, the excited-only
    model already excludes the vacuum.

Composing with `TransferSpectralBridge.toFormGapResidual` then discharges the
operator-form gap `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩` on `vac⊥`. -/
def wilsonTransferSpectralBridge {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (R : RCScaleResidualPlus)
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (R.RCscale s c) (R.RCscale t c))
    (P : CharacterDiagResolution op R w N) :
    TransferSpectralBridge (excitedCharSpectralGapData op w hw0 hw1 N) R where
  coeffSq := P.coeffSq
  coeffSq_nonneg := P.coeffSq_nonneg
  innerT_diag := P.parseval_T
  innerSelf_diag := P.parseval_self
  eigen_le_sep := fun {x} _ i =>
    Rscalar (casimir_qpow_le hw0 (Q'.le_of_lt hw1) i.val) (P.coeffSq_nonneg x i)

/-- **The operator-form gap for the finite-volume SU(2) Wilson transfer
operator.**  Composes the bridge with the already-proved
`TransferSpectralBridge.toFormGapResidual`: on `vac⊥`,
`⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩`. -/
def wilsonTransferFormGap {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (R : RCScaleResidualPlus)
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (R.RCscale s c) (R.RCscale t c))
    (P : CharacterDiagResolution op R w N) :
    TransferFormGapResidual (excitedCharSpectralGapData op w hw0 hw1 N) :=
  (wilsonTransferSpectralBridge op w hw0 hw1 N R Rscalar P).toFormGapResidual

end YMGap.Continuum.WilsonSpectralBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonSpectralBridge.qpow_ge_shift
#print axioms YMGap.Continuum.WilsonSpectralBridge.casimir_qpow_le
#print axioms YMGap.Continuum.WilsonSpectralBridge.excitedCharModel
#print axioms YMGap.Continuum.WilsonSpectralBridge.excitedCharLocatedGap
#print axioms YMGap.Continuum.WilsonSpectralBridge.excitedCharSpectralGapData
#print axioms YMGap.Continuum.WilsonSpectralBridge.wilsonTransferSpectralBridge
#print axioms YMGap.Continuum.WilsonSpectralBridge.wilsonTransferFormGap
