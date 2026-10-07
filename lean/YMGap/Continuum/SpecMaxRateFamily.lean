/-
# Norm Parseval for the character model, the operator-norm bound, and the
# `specMax`-rate family (hlink by `le_refl`)

ADDITIVE.  Implements the recommendation of
`audits/SCOPE-CHARACTER-DIAG-RESOLUTION-2026-10-06.md`.

* `CharacterDiagNormResolution op R w N perp` (**ADDED, not derived**): a sibling of
  `WilsonSpectralBridge.CharacterDiagResolution` (unchanged), restricted to a
  vacuum-orthogonality predicate `perp`, with the norm Parseval
  `parseval_TT : perp x → ⟨Tx,Tx⟩ = Σ λᵢ²·|cᵢ|²` (λᵢ = w^{c4(i+1)}).  It is not derivable
  from `parseval_T` (a statement about `⟨Tx,x⟩` only).  `ofTsq` derives it from a `T²`-form
  Parseval via `op.selfAdjoint`.  Vacuum split: the original structure's `parseval_self`
  is stated for ALL `x` over excited modes only, which forces every vector to be
  vacuum-free; here both Parsevals are required only on `perp`.
* `charDiag_normGap` (PROVED, finite algebra in `CReal.RC` with the abstract scaling
  `R : RCScaleResidualPlus` plus its scalar monotonicity `Rscalar`, the same hypothesis as
  `wilsonTransferSpectralBridge`): `perp x → ⟨Tx,Tx⟩ ≤ R.scale (specMax S)² ⟨x,x⟩` with
  `S = excitedCharModel w N`.  PLUMBING (group-blind).
* `specMaxRateFamily` (REDUCTION): a `WilsonDynamicFamily` with `rate j := specMax (S j)`,
  built from the OPEN hypothesis `hC : ∀ j, WilsonVacuumSqContraction … (specMax (S j))`
  on the physical `Completion` carrier.  That hypothesis IS the open identification
  (see `audits/SCOPE-SLAB-PETER-WEYL-IDENTIFICATION-2026-10-06.md`).
* `specMaxRate_hlink` (`le_refl`) and `specMaxRate_lowerMargin` (REDUCTION through
  `wilsonLowerMargin_of_traceCertificates`): honest at the model level.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.WilsonSpectralBridge
import YMGap.Continuum.SpectralHalvingMargin

namespace YMGap.Continuum.SpecMaxRateFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap (SpectralModel)
open YMGap.Continuum (specMax specMax_nonneg)
open YMGap.Continuum.HamiltonianScalar (RCScaleResidualPlus)
open YMGap.Continuum.RGTransport (qpow c4 qpow_nonneg)
open YMGap.Continuum.WilsonSpectralBridge (excitedCharModel)
open YMGap.Continuum.SpectralTraceSandwich (excitedTrace lam_le_specMax)
open YMGap.Continuum.SpectralHalvingMargin (wilsonLowerMargin_of_traceCertificates)
open YMGap.Continuum.BF4WilsonHalvingTimeMargin (halvingMargin)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily (WilsonDynamicFamily WilsonLowerMargin)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Constructive.HalfPow (half)

/-- Norm-Parseval character resolution on the vacuum-orthogonal part. -/
structure CharacterDiagNormResolution {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (R : RCScaleResidualPlus) (w : Q') (N : Nat)
    (perp : H.hilbert.carrier → Prop) : Type where
  coeffSq : H.hilbert.carrier → Fin N → CReal.RC
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  parseval_self : ∀ x, perp x → H.hilbert.cinner x x = CReal.RCfinSum N (coeffSq x)
  parseval_TT : ∀ x, perp x →
    H.hilbert.cinner (op.T x) (op.T x)
      = CReal.RCfinSum N (fun i =>
          R.RCscale (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))) (coeffSq x i))

/-- `parseval_TT` from a `T²`-form Parseval and self-adjointness. -/
def CharacterDiagNormResolution.ofTsq {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (R : RCScaleResidualPlus) (w : Q') (N : Nat)
    (perp : H.hilbert.carrier → Prop)
    (coeffSq : H.hilbert.carrier → Fin N → CReal.RC)
    (hnn : ∀ x i, CReal.RCnonneg (coeffSq x i))
    (hself : ∀ x, perp x → H.hilbert.cinner x x = CReal.RCfinSum N (coeffSq x))
    (hTsq : ∀ x, perp x →
      H.hilbert.cinner (op.T (op.T x)) x
        = CReal.RCfinSum N (fun i =>
            R.RCscale (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1))) (coeffSq x i))) :
    CharacterDiagNormResolution op R w N perp where
  coeffSq := coeffSq
  coeffSq_nonneg := hnn
  parseval_self := hself
  parseval_TT := fun x hx => by
    rw [← hTsq x hx]; exact (op.selfAdjoint (op.T x) x).symm

/-- `λ² ≤ m²` for `0 ≤ λ ≤ m`. -/
theorem sq_le_sq_of_le {l m : Q'} (h0 : (0 : Q') ≤ l) (h : l ≤ m) : l * l ≤ m * m :=
  Q'.mul_le_mul_of_nonneg h h (Q'.le_trans' _ _ _ h0 h) h0

/-- **Operator-norm bound** (PLUMBING): on `perp`, `‖Tx‖² ≤ specMax² · ‖x‖²`. -/
theorem charDiag_normGap {D : GNSData} {H : CompleteGNSHilbert D}
    {op : TransferOperator H} {R : RCScaleResidualPlus} {w : Q'} (hw0 : (0 : Q') ≤ w)
    {N : Nat} {perp : H.hilbert.carrier → Prop}
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (R.RCscale s c) (R.RCscale t c))
    (P : CharacterDiagNormResolution op R w N perp) (x : H.hilbert.carrier) (hx : perp x) :
    CReal.RCle (H.hilbert.cinner (op.T x) (op.T x))
      (R.RCscale (specMax (excitedCharModel w hw0 N) * specMax (excitedCharModel w hw0 N))
        (H.hilbert.cinner x x)) := by
  rw [P.parseval_TT x hx, P.parseval_self x hx, R.RCscale_finSum]
  refine CReal.RCfinSum_mono (fun i => Rscalar ?_ (P.coeffSq_nonneg x i))
  exact sq_le_sq_of_le (qpow_nonneg w hw0 _)
    (lam_le_specMax (excitedCharModel w hw0 N) i.val i.isLt)

/-! ## The `specMax`-rate family (REDUCTION on the OPEN identification) -/

/-- Family with `rate j := specMax (S j)`; contraction is the OPEN hypothesis `hC`. -/
def specMaxRateFamily (nome : Nat → Q') (nome_pos : ∀ j, (0 : Q') < nome j)
    (nome_lt_one : ∀ j, nome j < 1) (width : Nat → Nat)
    (sp : YMGap.Continuum.PhysicalSeparatorLogRate.PhysicalSpacing)
    (spz : YMGap.Continuum.PhysicalSeparatorLinearTail.SpacingToZero sp)
    (S : Nat → SpectralModel) (hS1 : ∀ j, specMax (S j) < 1)
    (hC : ∀ j, WilsonVacuumSqContraction (nome_pos j) (nome_lt_one j) (width j) (specMax (S j))) :
    WilsonDynamicFamily where
  nome := nome
  nome_pos := nome_pos
  nome_lt_one := nome_lt_one
  width := width
  transferSpacing := sp
  transferSpacingToZero := spz
  rate := fun j => specMax (S j)
  rate_nonnegative := fun j => specMax_nonneg (S j)
  rate_lt_one := hS1
  contraction := hC

theorem specMaxRate_hlink (nome : Nat → Q') (nome_pos : ∀ j, (0 : Q') < nome j)
    (nome_lt_one : ∀ j, nome j < 1) (width : Nat → Nat)
    (sp : YMGap.Continuum.PhysicalSeparatorLogRate.PhysicalSpacing)
    (spz : YMGap.Continuum.PhysicalSeparatorLinearTail.SpacingToZero sp)
    (S : Nat → SpectralModel) (hS1 : ∀ j, specMax (S j) < 1)
    (hC : ∀ j, WilsonVacuumSqContraction (nome_pos j) (nome_lt_one j) (width j) (specMax (S j)))
    (j : Nat) :
    (specMaxRateFamily nome nome_pos nome_lt_one width sp spz S hS1 hC).rate j ≤ specMax (S j) :=
  Q'.le_refl' _

/-- **REDUCTION.** OPEN contraction at rate `specMax (S j)` + trace certificates ⇒
`WilsonLowerMargin … (1/(2·M0))`. -/
theorem specMaxRate_lowerMargin (nome : Nat → Q') (nome_pos : ∀ j, (0 : Q') < nome j)
    (nome_lt_one : ∀ j, nome j < 1) (width : Nat → Nat)
    (sp : YMGap.Continuum.PhysicalSeparatorLogRate.PhysicalSpacing)
    (spz : YMGap.Continuum.PhysicalSeparatorLinearTail.SpacingToZero sp)
    (hsp : ∀ j, sp.spacing j = half ^ j)
    (S : Nat → SpectralModel) (hS1 : ∀ j, specMax (S j) < 1)
    (hC : ∀ j, WilsonVacuumSqContraction (nome_pos j) (nome_lt_one j) (width j) (specMax (S j)))
    (M0 : Nat) (hM0 : 0 < M0) (U : Nat → Q')
    (hU : ∀ j, excitedTrace (S j) (M0 * 2 ^ j) ≤ U j) (hUh : ∀ j, U j ≤ half) :
    WilsonLowerMargin (specMaxRateFamily nome nome_pos nome_lt_one width sp spz S hS1 hC)
      (halvingMargin M0) :=
  wilsonLowerMargin_of_traceCertificates _ M0 hM0 hsp S U
    (specMaxRate_hlink nome nome_pos nome_lt_one width sp spz S hS1 hC) hU hUh

end YMGap.Continuum.SpecMaxRateFamily

#print axioms YMGap.Continuum.SpecMaxRateFamily.charDiag_normGap
#print axioms YMGap.Continuum.SpecMaxRateFamily.CharacterDiagNormResolution.ofTsq
#print axioms YMGap.Continuum.SpecMaxRateFamily.specMaxRate_hlink
#print axioms YMGap.Continuum.SpecMaxRateFamily.specMaxRate_lowerMargin
