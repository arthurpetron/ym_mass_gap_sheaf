/-
M3q -- reuse `SpectralMarginInput` as a constructive normalized physical-loss
flow.

`AsymptoticSpectralLoc.SpectralMarginInput` already carries a physical mass
sequence, a uniform ceiling, and a proved multiplicative recursion.  Its tower
defect is identified with the tail of the graded spectral-localization defect.
This file converts those data to the direction-neutral additive-loss interface:

  rateLoss k = T.delta k * physicalMass k
             <= ceilConst * T.delta k.

The tail-shift identity then supplies an inverse-square majorant with offset
`fmCutoff + 2`, so a complete constructive tail modulus follows.  This is
wiring and arithmetic; `SpectralMarginInput` itself remains uninhabited for the
four-dimensional theory.
-/

import YMGap.Continuum.AsymptoticSpectralLoc
import YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss

namespace YMGap.Continuum.SpectralMarginInputMassNormalizedLoss

open YMGap.Constructive
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss
open YMGap.Continuum.SummableInverseSquare

/-! ## Tail-shift bookkeeping for the inverse-square majorant -/

/-- Shifting the sequence index by `cutoff` is definitionally the same
inverse-square denominator as increasing the offset by `cutoff`. -/
theorem invSqTerm_tail_shift_eqv (cutoff k : Nat) :
    (invSqTerm 2 (by decide) (k + cutoff)).eqv
      (invSqTerm (cutoff + 2) (by omega) k) := by
  unfold invSqTerm
  apply Q'.eqv_of_eq
  congr 1

end YMGap.Continuum.SpectralMarginInputMassNormalizedLoss

namespace YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput

open YMGap.Constructive
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss
open YMGap.Continuum.SpectralMarginInputMassNormalizedLoss
open YMGap.Continuum.SummableInverseSquare

variable {b : Nat} {afr : AFRateModulus} {N₀ : Nat}

/-- The dimensionful additive loss induced by the tower's multiplicative
physical-margin recursion. -/
def normalizedLoss (I : SpectralMarginInput b afr N₀) (k : Nat) : Q' :=
  I.T.δ k * I.g k

/-- Encode the normalized loss as a log loss at the next physical spacing. -/
def logLoss (I : SpectralMarginInput b afr N₀) (k : Nat) : Q' :=
  I.normalizedLoss k * I.spacing (k + 1)

theorem physicalMass_pos (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (0 : Q') < I.g k :=
  Q'.divPos_pos _ _ (I.spacing_pos k) (I.atSpacing k).floorRate_pos

theorem physicalMass_nonnegative
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (0 : Q') <= I.g k :=
  Q'.le_of_lt (I.physicalMass_pos k)

theorem ceiling_nonnegative (I : SpectralMarginInput b afr N₀) :
    (0 : Q') <= I.ceilConst :=
  Q'.le_trans' _ _ _ (I.physicalMass_nonnegative 0) (I.physCeil 0)

theorem normalizedLoss_nonnegative
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (0 : Q') <= I.normalizedLoss k :=
  Q'.mul_nonneg _ _ (I.T.δ_nonneg k) (I.physicalMass_nonnegative k)

theorem logLoss_nonnegative
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (0 : Q') <= I.logLoss k :=
  Q'.mul_nonneg _ _ (I.normalizedLoss_nonnegative k)
    (Q'.le_of_lt (I.spacing_pos (k + 1)))

/-- The already-proved multiplicative recursion becomes the additive loss step
needed by `MassNormalizedLossFlow`. -/
theorem additive_step (I : SpectralMarginInput b afr N₀) (k : Nat) :
    I.g k <= I.g (k + 1) +
      Q'.divPos (I.logLoss k) (I.spacing (k + 1))
        (I.spacing_pos (k + 1)) := by
  have hadded :
      (1 - I.T.δ k) * I.g k + I.normalizedLoss k <=
        I.g (k + 1) + I.normalizedLoss k :=
    Q'.add_le_add_right _ _ _ (I.toAsymptotic.recursion k)
  have hraw : I.g k <= I.g (k + 1) + I.normalizedLoss k :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (oneSubMul_add_loss_eqv (I.T.δ k) (I.g k)))
      hadded
  have hquot :
      (Q'.divPos (I.logLoss k) (I.spacing (k + 1))
        (I.spacing_pos (k + 1))).eqv (I.normalizedLoss k) :=
    divPos_mul_right_eqv
      (I.normalizedLoss k) (I.spacing (k + 1)) (I.spacing_pos (k + 1))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.add_le_add_left _ _ _ (Q'.ge_of_eqv hquot))

/-- The direction-neutral rational physical-loss flow already latent in
`SpectralMarginInput`. -/
def toMassNormalizedLossFlow (I : SpectralMarginInput b afr N₀) :
    MassNormalizedLossFlow where
  spacing := I.spacing
  spacing_pos := I.spacing_pos
  mass := I.g
  mass_nonnegative := I.physicalMass_nonnegative
  logLoss := I.logLoss
  logLoss_nonnegative := I.logLoss_nonnegative
  step := I.additive_step

theorem rateLoss_eqv_normalizedLoss
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (I.toMassNormalizedLossFlow.rateLoss k).eqv (I.normalizedLoss k) :=
  divPos_mul_right_eqv
    (I.normalizedLoss k) (I.spacing (k + 1)) (I.spacing_pos (k + 1))

/-- The physical ceiling turns the tower defect into a dimensionful rate-loss
majorant. -/
theorem rateLoss_le_ceiling_mul_delta
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    I.toMassNormalizedLossFlow.rateLoss k <= I.ceilConst * I.T.δ k := by
  have heq : I.toMassNormalizedLossFlow.rateLoss k <= I.normalizedLoss k :=
    Q'.le_of_eqv (I.rateLoss_eqv_normalizedLoss k)
  have hmass : I.normalizedLoss k <= I.T.δ k * I.ceilConst :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (I.physCeil k) (I.T.δ_nonneg k)
  exact Q'.le_trans' _ _ _ heq
    (Q'.le_trans' _ _ _ hmass
      (Q'.le_of_eqv (Q'.mul_comm_eqv (I.T.δ k) I.ceilConst)))

/-- The tail identification with the localized full-mode defect gives the
shifted inverse-square estimate consumed by normalized-loss persistence. -/
def toInverseSquareControl (I : SpectralMarginInput b afr N₀) :
    InverseSquareRateLossControl I.toMassNormalizedLossFlow where
  offset :=
    fmCutoff afr (spectralLocalization_defect afr N₀ I.sl) + 2
  offset_at_least_two := by omega
  coefficient :=
    I.ceilConst *
      fmAconst afr (spectralLocalization_defect afr N₀ I.sl)
  coefficient_nonnegative :=
    Q'.mul_nonneg _ _ I.ceiling_nonnegative
      (fmAconst_nonneg afr (spectralLocalization_defect afr N₀ I.sl))
  rateLoss_le := fun k => by
    let defect := spectralLocalization_defect afr N₀ I.sl
    let cutoff := fmCutoff afr defect
    have hphysical := I.rateLoss_le_ceiling_mul_delta k
    have hidentify : I.T.δ k <= defect.d (k + cutoff) :=
      Q'.le_of_eqv (Q'.eqv_of_eq (I.hδ k))
    have hdefect : defect.d (k + cutoff) <=
        fmAconst afr defect * invSqTerm 2 (by decide) (k + cutoff) :=
      fmDefect_invSq afr defect (k + cutoff)
    have hshift :
        fmAconst afr defect * invSqTerm 2 (by decide) (k + cutoff) <=
          fmAconst afr defect * invSqTerm (cutoff + 2) (by omega) k :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_of_eqv (invSqTerm_tail_shift_eqv cutoff k))
        (fmAconst_nonneg afr defect)
    have hdelta : I.T.δ k <=
        fmAconst afr defect * invSqTerm (cutoff + 2) (by omega) k :=
      Q'.le_trans' _ _ _ hidentify
        (Q'.le_trans' _ _ _ hdefect hshift)
    have hscaled : I.ceilConst * I.T.δ k <=
        I.ceilConst *
          (fmAconst afr defect * invSqTerm (cutoff + 2) (by omega) k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hdelta I.ceiling_nonnegative
    exact Q'.le_trans' _ _ _ hphysical
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv I.ceilConst (fmAconst afr defect)
              (invSqTerm (cutoff + 2) (by omega) k)))))

/-- `SpectralMarginInput` therefore constructs the full normalized-loss budget
with an explicit tail modulus. -/
def lossBudget (I : SpectralMarginInput b afr N₀) :=
  I.toInverseSquareControl.lossBudget

@[simp] theorem lossBudget_cap (I : SpectralMarginInput b afr N₀) :
    I.lossBudget.cap =
      (I.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ I.sl)) *
        pot
          (fmCutoff afr (spectralLocalization_defect afr N₀ I.sl) + 2)
          (by omega) 0 := rfl

/-- Anchor dominance against the shifted, ceiling-scaled cap gives an additive
normalized-loss persistence witness for the same physical mass sequence. -/
def persistence
    (I : SpectralMarginInput b afr N₀)
    (anchorDominates :
      (I.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ I.sl)) *
        pot
          (fmCutoff afr (spectralLocalization_defect afr N₀ I.sl) + 2)
          (by omega) 0 < I.g 0) :
    MassNormalizedLossPersistence I.toMassNormalizedLossFlow :=
  I.toInverseSquareControl.persistence anchorDominates

theorem persistent_floor_pos
    (I : SpectralMarginInput b afr N₀)
    (anchorDominates :
      (I.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ I.sl)) *
        pot
          (fmCutoff afr (spectralLocalization_defect afr N₀ I.sl) + 2)
          (by omega) 0 < I.g 0) :
    (0 : Q') < (I.persistence anchorDominates).floorWitness :=
  I.toInverseSquareControl.persistent_floor_pos anchorDominates

theorem persistent_floor_le_mass
    (I : SpectralMarginInput b afr N₀)
    (anchorDominates :
      (I.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ I.sl)) *
        pot
          (fmCutoff afr (spectralLocalization_defect afr N₀ I.sl) + 2)
          (by omega) 0 < I.g 0)
    (k : Nat) :
    (I.persistence anchorDominates).floorWitness <= I.g k :=
  I.toInverseSquareControl.persistent_floor_le_mass anchorDominates k

end YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput

#print axioms YMGap.Continuum.SpectralMarginInputMassNormalizedLoss.invSqTerm_tail_shift_eqv
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.additive_step
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.toMassNormalizedLossFlow
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.rateLoss_eqv_normalizedLoss
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.rateLoss_le_ceiling_mul_delta
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.toInverseSquareControl
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.lossBudget
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.persistence
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.persistent_floor_pos
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.persistent_floor_le_mass
