/-
M3o -- from a localized multiplicative physical-margin recursion to an
additive normalized-loss budget.

A dimensionless spectral defect does not by itself have the units of a
physical mass loss.  The multiplicative recursion

  (1 - d_k) * M_k <= M_(k+1)

instead yields the additive loss `d_k * M_k`.  With a uniform physical ceiling
`M_k <= C`, this loss is at most `C * d_k`.  For the graded localized defect,
the already-proved AF quadratic estimate therefore gives the inverse-square
physical-loss coefficient `C * fmAconst`.

This file formalizes that unit-sensitive conversion.  Spectral localization,
the same-object physical-margin recursion, and the anchor dominance remain
explicit analytic inputs.
-/

import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.InverseSquareMassNormalizedLossPersistence

namespace YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss

open YMGap.Constructive
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.SummableInverseSquare

/-! ## Rational algebra for the multiplicative-to-additive conversion -/

/-- Dividing `x * q` by the positive factor `q` recovers `x` semantically. -/
theorem divPos_mul_right_eqv (x q : Q') (hq : (0 : Q') < q) :
    (Q'.divPos (x * q) q hq).eqv x := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv x q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv x

/-- Adding back the multiplicative loss collapses
`(1-d)*m + d*m` to `m`. -/
theorem oneSubMul_add_loss_eqv (d m : Q') :
    ((1 - d) * m + d * m).eqv m := by
  have hdist : ((1 - d) * m).eqv (1 * m + -(d * m)) :=
    Q'.sub_mul_eqv 1 d m
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (d * m) hdist) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (1 * m) (-(d * m)) (d * m)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 * m) _ _ (Q'.neg_add_self_eqv (d * m))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' (1 * m))) ?_
  exact Q'.one_mul_eqv m

/-! ## Same-object localized physical-margin flow -/

/-- A physical mass sequence obeying the multiplicative recursion for one
graded spectral-localization defect.  `massCeiling` carries the physical units
needed to turn the dimensionless defect into an additive mass-loss bound. -/
structure SpectralLocalizedPhysicalMarginFlow : Type where
  afRate : AFRateModulus
  modeCutoff : Nat
  localization : SpectralLocalization afRate modeCutoff
  spacing : Nat -> Q'
  spacing_pos : forall k : Nat, (0 : Q') < spacing k
  mass : Nat -> Q'
  mass_nonnegative : forall k : Nat, (0 : Q') <= mass k
  massCeiling : Q'
  massCeiling_nonnegative : (0 : Q') <= massCeiling
  mass_le_ceiling : forall k : Nat, mass k <= massCeiling
  recursion : forall k : Nat,
    (1 - localization.gapDefect k) * mass k <= mass (k + 1)

namespace SpectralLocalizedPhysicalMarginFlow

/-- The dimensionful additive loss forced by the multiplicative recursion. -/
def normalizedLoss (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) : Q' :=
  flow.localization.gapDefect k * flow.mass k

/-- Store the dimensionful normalized loss as a logarithmic loss by multiplying
by the next physical spacing; division by that spacing recovers it exactly up
to rational semantic equivalence. -/
def logLoss (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) : Q' :=
  flow.normalizedLoss k * flow.spacing (k + 1)

theorem normalizedLoss_nonnegative
    (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) :
    (0 : Q') <= flow.normalizedLoss k :=
  Q'.mul_nonneg _ _ (flow.localization.gapDefect_nonneg k)
    (flow.mass_nonnegative k)

theorem logLoss_nonnegative
    (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) :
    (0 : Q') <= flow.logLoss k :=
  Q'.mul_nonneg _ _ (flow.normalizedLoss_nonnegative k)
    (Q'.le_of_lt (flow.spacing_pos (k + 1)))

/-- The multiplicative recursion, rewritten as the additive loss step consumed
by `MassNormalizedLossFlow`. -/
theorem additive_step (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) :
    flow.mass k <= flow.mass (k + 1) +
      Q'.divPos (flow.logLoss k) (flow.spacing (k + 1))
        (flow.spacing_pos (k + 1)) := by
  have hadded :
      (1 - flow.localization.gapDefect k) * flow.mass k +
          flow.normalizedLoss k <=
        flow.mass (k + 1) + flow.normalizedLoss k :=
    Q'.add_le_add_right _ _ _ (flow.recursion k)
  have hraw : flow.mass k <=
      flow.mass (k + 1) + flow.normalizedLoss k :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (oneSubMul_add_loss_eqv
          (flow.localization.gapDefect k) (flow.mass k)))
      hadded
  have hquot :
      (Q'.divPos (flow.logLoss k) (flow.spacing (k + 1))
        (flow.spacing_pos (k + 1))).eqv (flow.normalizedLoss k) := by
    exact divPos_mul_right_eqv
      (flow.normalizedLoss k) (flow.spacing (k + 1))
        (flow.spacing_pos (k + 1))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.add_le_add_left _ _ _ (Q'.ge_of_eqv hquot))

/-- The canonical direction-neutral normalized-loss flow attached to the
multiplicative physical-margin recursion. -/
def toMassNormalizedLossFlow
    (flow : SpectralLocalizedPhysicalMarginFlow) : MassNormalizedLossFlow where
  spacing := flow.spacing
  spacing_pos := flow.spacing_pos
  mass := flow.mass
  mass_nonnegative := flow.mass_nonnegative
  logLoss := flow.logLoss
  logLoss_nonnegative := flow.logLoss_nonnegative
  step := flow.additive_step

/-- Its charged rate loss is exactly `gapDefect k * mass k` semantically. -/
theorem rateLoss_eqv_normalizedLoss
    (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) :
    (flow.toMassNormalizedLossFlow.rateLoss k).eqv (flow.normalizedLoss k) := by
  exact divPos_mul_right_eqv
    (flow.normalizedLoss k) (flow.spacing (k + 1))
      (flow.spacing_pos (k + 1))

/-- The physical ceiling supplies the correctly scaled pointwise defect bound
`rateLoss k <= massCeiling * gapDefect k`. -/
theorem rateLoss_le_ceiling_mul_gapDefect
    (flow : SpectralLocalizedPhysicalMarginFlow) (k : Nat) :
    flow.toMassNormalizedLossFlow.rateLoss k <=
      flow.massCeiling * flow.localization.gapDefect k := by
  have heq : flow.toMassNormalizedLossFlow.rateLoss k <=
      flow.normalizedLoss k :=
    Q'.le_of_eqv (flow.rateLoss_eqv_normalizedLoss k)
  have hmass : flow.normalizedLoss k <=
      flow.localization.gapDefect k * flow.massCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (flow.mass_le_ceiling k)
      (flow.localization.gapDefect_nonneg k)
  exact Q'.le_trans' _ _ _ heq
    (Q'.le_trans' _ _ _ hmass
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (flow.localization.gapDefect k) flow.massCeiling)))

/-- The localized quadratic estimate gives an inverse-square bound with the
unit-correct coefficient `massCeiling * fmAconst`. -/
def toInverseSquareControl
    (flow : SpectralLocalizedPhysicalMarginFlow) :
    InverseSquareRateLossControl flow.toMassNormalizedLossFlow where
  offset := 2
  offset_at_least_two := by decide
  coefficient :=
    flow.massCeiling *
      fmAconst flow.afRate
        (spectralLocalization_defect
          flow.afRate flow.modeCutoff flow.localization)
  coefficient_nonnegative :=
    Q'.mul_nonneg _ _ flow.massCeiling_nonnegative
      (fmAconst_nonneg flow.afRate
        (spectralLocalization_defect
          flow.afRate flow.modeCutoff flow.localization))
  rateLoss_le := fun k => by
    let defect := spectralLocalization_defect
      flow.afRate flow.modeCutoff flow.localization
    have hphysical := flow.rateLoss_le_ceiling_mul_gapDefect k
    have hdefect : flow.localization.gapDefect k <=
        fmAconst flow.afRate defect * invSqTerm 2 (by decide) k :=
      fmDefect_invSq flow.afRate defect k
    have hscaled :
        flow.massCeiling * flow.localization.gapDefect k <=
          flow.massCeiling *
            (fmAconst flow.afRate defect * invSqTerm 2 (by decide) k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hdefect
        flow.massCeiling_nonnegative
    exact Q'.le_trans' _ _ _ hphysical
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              flow.massCeiling (fmAconst flow.afRate defect)
                (invSqTerm 2 (by decide) k)))))

/-- The same-object localized recursion constructs a complete physical-loss
budget, including an explicit tail modulus. -/
def lossBudget (flow : SpectralLocalizedPhysicalMarginFlow) :=
  flow.toInverseSquareControl.lossBudget

@[simp] theorem lossBudget_cap
    (flow : SpectralLocalizedPhysicalMarginFlow) :
    flow.lossBudget.cap =
      (flow.massCeiling *
          fmAconst flow.afRate
            (spectralLocalization_defect
              flow.afRate flow.modeCutoff flow.localization)) *
        pot 2 (by decide) 0 := rfl

/-- If the physical anchor exceeds the ceiling-scaled inverse-square cap, the
physical mass persists uniformly. -/
def persistence
    (flow : SpectralLocalizedPhysicalMarginFlow)
    (anchorDominates :
      (flow.massCeiling *
          fmAconst flow.afRate
            (spectralLocalization_defect
              flow.afRate flow.modeCutoff flow.localization)) *
        pot 2 (by decide) 0 < flow.mass 0) :
    MassNormalizedLossPersistence flow.toMassNormalizedLossFlow :=
  flow.toInverseSquareControl.persistence anchorDominates

@[simp] theorem persistence_floorWitness
    (flow : SpectralLocalizedPhysicalMarginFlow)
    (anchorDominates :
      (flow.massCeiling *
          fmAconst flow.afRate
            (spectralLocalization_defect
              flow.afRate flow.modeCutoff flow.localization)) *
        pot 2 (by decide) 0 < flow.mass 0) :
    (flow.persistence anchorDominates).floorWitness =
      flow.mass 0 +
        -((flow.massCeiling *
            fmAconst flow.afRate
              (spectralLocalization_defect
                flow.afRate flow.modeCutoff flow.localization)) *
          pot 2 (by decide) 0) := rfl

theorem persistent_floor_pos
    (flow : SpectralLocalizedPhysicalMarginFlow)
    (anchorDominates :
      (flow.massCeiling *
          fmAconst flow.afRate
            (spectralLocalization_defect
              flow.afRate flow.modeCutoff flow.localization)) *
        pot 2 (by decide) 0 < flow.mass 0) :
    (0 : Q') < (flow.persistence anchorDominates).floorWitness :=
  flow.toInverseSquareControl.persistent_floor_pos anchorDominates

theorem persistent_floor_le_mass
    (flow : SpectralLocalizedPhysicalMarginFlow)
    (anchorDominates :
      (flow.massCeiling *
          fmAconst flow.afRate
            (spectralLocalization_defect
              flow.afRate flow.modeCutoff flow.localization)) *
        pot 2 (by decide) 0 < flow.mass 0)
    (k : Nat) :
    (flow.persistence anchorDominates).floorWitness <= flow.mass k :=
  flow.toInverseSquareControl.persistent_floor_le_mass anchorDominates k

end SpectralLocalizedPhysicalMarginFlow

end YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss

#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.divPos_mul_right_eqv
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.oneSubMul_add_loss_eqv
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.additive_step
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.toMassNormalizedLossFlow
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.rateLoss_eqv_normalizedLoss
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.rateLoss_le_ceiling_mul_gapDefect
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.toInverseSquareControl
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.lossBudget
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.persistence
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.persistent_floor_pos
#print axioms YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss.SpectralLocalizedPhysicalMarginFlow.persistent_floor_le_mass
