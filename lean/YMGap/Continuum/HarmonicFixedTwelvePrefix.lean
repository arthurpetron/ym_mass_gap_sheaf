/- Fixed twelve-head evidence using the symbolic variable-anchor PF2 engine. -/

import YMGap.Continuum.HarmonicFixedElevenPrefix
import YMGap.Continuum.HarmonicVariableAnchorRetune

namespace YMGap.Continuum.HarmonicFixedTwelvePrefix

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicVariableAnchorRetune
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

theorem fixed_twelve_checks_k34 :
    adjCorr (harmW 34) 12 ≤ retuneCube (harmW 34) * coordNormSq (harmW 34) 11 ∧
      Q'.ofNat 13 * qpow (harmW 34) 25 ≤
        retuneCube (harmW 34) * Q'.ofNat 12 := by constructor <;> decide
theorem fixed_twelve_checks_k35 :
    adjCorr (harmW 35) 12 ≤ retuneCube (harmW 35) * coordNormSq (harmW 35) 11 ∧
      Q'.ofNat 13 * qpow (harmW 35) 25 ≤
        retuneCube (harmW 35) * Q'.ofNat 12 := by constructor <;> decide
theorem fixed_twelve_checks_k36 :
    adjCorr (harmW 36) 12 ≤ retuneCube (harmW 36) * coordNormSq (harmW 36) 11 ∧
      Q'.ofNat 13 * qpow (harmW 36) 25 ≤
        retuneCube (harmW 36) * Q'.ofNat 12 := by constructor <;> decide
theorem fixed_twelve_checks_k37 :
    adjCorr (harmW 37) 12 ≤ retuneCube (harmW 37) * coordNormSq (harmW 37) 11 ∧
      Q'.ofNat 13 * qpow (harmW 37) 25 ≤
        retuneCube (harmW 37) * Q'.ofNat 12 := by constructor <;> decide
theorem fixed_twelve_checks_k38 :
    adjCorr (harmW 38) 12 ≤ retuneCube (harmW 38) * coordNormSq (harmW 38) 11 ∧
      Q'.ofNat 13 * qpow (harmW 38) 25 ≤
        retuneCube (harmW 38) * Q'.ofNat 12 := by constructor <;> decide

/-- The retained head, not the scalar tail cross, is the first failure. -/
theorem fixed_twelve_head_k39_fails :
    ¬ adjCorr (harmW 39) 12 ≤
      retuneCube (harmW 39) * coordNormSq (harmW 39) 11 := by decide

theorem fixed_twelve_scalar_cross_k39 :
    Q'.ofNat 13 * qpow (harmW 39) 25 ≤
      retuneCube (harmW 39) * Q'.ofNat 12 := by decide

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

theorem harmonic_retune_cutoff_k34 :
    adjCorr (harmW 34) (Ncut 34) ≤
      retuneCube (harmW 34) * coordNormSq (harmW 34) (Ncut 34) := by
  simpa [Ncut] using variable_anchor_all_later_cutoffs 11 1284
    (harmW_nonneg 34) (harmW_le_one 34) (harmW_pos 34)
    (retuneCube_nonneg _ (harmW_nonneg 34))
    fixed_twelve_checks_k34.1 fixed_twelve_checks_k34.2
theorem harmonic_retune_cutoff_k35 :
    adjCorr (harmW 35) (Ncut 35) ≤
      retuneCube (harmW 35) * coordNormSq (harmW 35) (Ncut 35) := by
  simpa [Ncut] using variable_anchor_all_later_cutoffs 11 1357
    (harmW_nonneg 35) (harmW_le_one 35) (harmW_pos 35)
    (retuneCube_nonneg _ (harmW_nonneg 35))
    fixed_twelve_checks_k35.1 fixed_twelve_checks_k35.2
theorem harmonic_retune_cutoff_k36 :
    adjCorr (harmW 36) (Ncut 36) ≤
      retuneCube (harmW 36) * coordNormSq (harmW 36) (Ncut 36) := by
  simpa [Ncut] using variable_anchor_all_later_cutoffs 11 1432
    (harmW_nonneg 36) (harmW_le_one 36) (harmW_pos 36)
    (retuneCube_nonneg _ (harmW_nonneg 36))
    fixed_twelve_checks_k36.1 fixed_twelve_checks_k36.2
theorem harmonic_retune_cutoff_k37 :
    adjCorr (harmW 37) (Ncut 37) ≤
      retuneCube (harmW 37) * coordNormSq (harmW 37) (Ncut 37) := by
  simpa [Ncut] using variable_anchor_all_later_cutoffs 11 1509
    (harmW_nonneg 37) (harmW_le_one 37) (harmW_pos 37)
    (retuneCube_nonneg _ (harmW_nonneg 37))
    fixed_twelve_checks_k37.1 fixed_twelve_checks_k37.2
theorem harmonic_retune_cutoff_k38 :
    adjCorr (harmW 38) (Ncut 38) ≤
      retuneCube (harmW 38) * coordNormSq (harmW 38) (Ncut 38) := by
  simpa [Ncut] using variable_anchor_all_later_cutoffs 11 1588
    (harmW_nonneg 38) (harmW_le_one 38) (harmW_pos 38)
    (retuneCube_nonneg _ (harmW_nonneg 38))
    fixed_twelve_checks_k38.1 fixed_twelve_checks_k38.2

private theorem harmonic_lamPW_le_retune_of_cutoff (k : Nat)
    (hcorr : adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k)) :
    lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k) := by
  have heq : lamPW (harmW k) (Ncut k) 1 ≈
      Q'.divPos (adjCorr (harmW k) (Ncut k))
        (coordNormSq (harmW k) (Ncut k))
        (coordNormSq_pos (harmW_nonneg k) (Ncut k)) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 (harmW_nonneg k) (harmW_le_one k) (Ncut k) 0)
      (vacNorm_fundamental_eq_ratio (harmW_nonneg k) (harmW_le_one k) (Ncut k))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.divPos_le_of_le_mul _ _ _ hcorr)

theorem harmonic_lamPW_le_retune_k34 :
    lamPW (harmW 34) (Ncut 34) 1 ≤ retuneCube (harmW 34) :=
  harmonic_lamPW_le_retune_of_cutoff 34 harmonic_retune_cutoff_k34
theorem harmonic_lamPW_le_retune_k35 :
    lamPW (harmW 35) (Ncut 35) 1 ≤ retuneCube (harmW 35) :=
  harmonic_lamPW_le_retune_of_cutoff 35 harmonic_retune_cutoff_k35
theorem harmonic_lamPW_le_retune_k36 :
    lamPW (harmW 36) (Ncut 36) 1 ≤ retuneCube (harmW 36) :=
  harmonic_lamPW_le_retune_of_cutoff 36 harmonic_retune_cutoff_k36
theorem harmonic_lamPW_le_retune_k37 :
    lamPW (harmW 37) (Ncut 37) 1 ≤ retuneCube (harmW 37) :=
  harmonic_lamPW_le_retune_of_cutoff 37 harmonic_retune_cutoff_k37
theorem harmonic_lamPW_le_retune_k38 :
    lamPW (harmW 38) (Ncut 38) 1 ≤ retuneCube (harmW 38) :=
  harmonic_lamPW_le_retune_of_cutoff 38 harmonic_retune_cutoff_k38

private theorem harmonic_mass_floor_of_lamPW (k : Nat)
    (h : lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

theorem harmonicMass_k34_twelve_floor :
    (1 : Q') - retuneCube (harmW 34) ≤ harmonicMass 34 :=
  harmonic_mass_floor_of_lamPW 34 harmonic_lamPW_le_retune_k34
theorem harmonicMass_k35_twelve_floor :
    (1 : Q') - retuneCube (harmW 35) ≤ harmonicMass 35 :=
  harmonic_mass_floor_of_lamPW 35 harmonic_lamPW_le_retune_k35
theorem harmonicMass_k36_twelve_floor :
    (1 : Q') - retuneCube (harmW 36) ≤ harmonicMass 36 :=
  harmonic_mass_floor_of_lamPW 36 harmonic_lamPW_le_retune_k36
theorem harmonicMass_k37_twelve_floor :
    (1 : Q') - retuneCube (harmW 37) ≤ harmonicMass 37 :=
  harmonic_mass_floor_of_lamPW 37 harmonic_lamPW_le_retune_k37
theorem harmonicMass_k38_twelve_floor :
    (1 : Q') - retuneCube (harmW 38) ≤ harmonicMass 38 :=
  harmonic_mass_floor_of_lamPW 38 harmonic_lamPW_le_retune_k38

end YMGap.Continuum.HarmonicFixedTwelvePrefix

#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_checks_k34
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_checks_k35
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_checks_k36
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_checks_k37
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_checks_k38
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_head_k39_fails
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.fixed_twelve_scalar_cross_k39
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_retune_cutoff_k34
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_retune_cutoff_k35
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_retune_cutoff_k36
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_retune_cutoff_k37
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_retune_cutoff_k38
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_lamPW_le_retune_k34
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_lamPW_le_retune_k35
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_lamPW_le_retune_k36
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_lamPW_le_retune_k37
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonic_lamPW_le_retune_k38
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonicMass_k34_twelve_floor
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonicMass_k35_twelve_floor
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonicMass_k36_twelve_floor
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonicMass_k37_twelve_floor
#print axioms YMGap.Continuum.HarmonicFixedTwelvePrefix.harmonicMass_k38_twelve_floor
