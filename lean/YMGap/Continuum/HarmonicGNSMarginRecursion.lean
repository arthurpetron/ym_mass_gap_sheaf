/-
# GNS interpretation of the harmonic margin recursion

The all-scale sector-domination theorem makes `harmonicMass` the located gap
margin of the established reflection-positive character GNS transfer, not
only the complement of a finite fused coefficient.  This module carries that
identification through the spacing quotient and the exact scalar absorption
theorem.

Consequently the sole sharp input can be written without a free margin or an
operator-identification field: the coefficient-two, division-free harmonic
cross determinant at every scale.  From it we construct the existing
`HarmonicTrueMarginDrop`, `SingleStepDefectBound`, and positive multiscale
floor for the actual located GNS gap margin divided by the harmonic spacing.
-/

import YMGap.Continuum.HarmonicPolymerBudgetBridge
import YMGap.Continuum.HarmonicTransferSectorDominationAll
import YMGap.Continuum.HarmonicTrueMarginAbsorption

namespace YMGap.Continuum.HarmonicGNSMarginRecursion

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicPolymerBudgetBridge
open YMGap.Continuum.HarmonicTransferSectorDominationAll
open YMGap.Continuum.HarmonicTrueMarginStep
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

/-- The located gap margin of the established reflection-positive character
GNS transfer, expressed in physical harmonic-spacing units. -/
def harmonicGNSMargin (k : Nat) : Q' :=
  Q'.divPos (harmonicCharLocatedGap_all k).gapMargin
    (harmonicSpacing k) (harmonicSpacing_pos k)

/-- The operator-derived GNS margin is definitionally the concrete harmonic
true margin already used by the RG recursion. -/
theorem harmonicGNSMargin_eq_trueMargin (k : Nat) :
    harmonicGNSMargin k = harmonicTrueMargin k := rfl

/-- A coefficient-two cross proof gives the exact multiplicative step for the
located GNS gap margins in physical spacing units. -/
theorem harmonicGNSMargin_singleStep_of_cross
    (H : ∀ j : Nat,
      harmonicMassCross j ≤
        (Q'.ofNat 2 * invSqTerm 2 (by decide) j) *
          (harmonicD j * harmonicD (j + 1)))
    (k : Nat) :
    ((1 : Q') - BondMovingQuadratic.bondMovingDeltaRen 1
        UniformCouplingFromAF.pMult (harmW k)) * harmonicGNSMargin k ≤
      harmonicGNSMargin (k + 1) := by
  rw [harmonicGNSMargin_eq_trueMargin,
    harmonicGNSMargin_eq_trueMargin]
  exact HarmonicTrueMarginAbsorption.harmonicTrueMargin_singleStep_of_mass_drop k
    (harmonicMass_drop_le_two_invSq_of_cross k (H k))

/-- The same determinant proof inhabits the non-weakened harmonic drop
carrier consumed by the canonical AF-tail construction. -/
def harmonicTrueMarginDrop_of_cross
    (H : ∀ j : Nat,
      harmonicMassCross j ≤
        (Q'.ofNat 2 * invSqTerm 2 (by decide) j) *
          (harmonicD j * harmonicD (j + 1))) : HarmonicTrueMarginDrop where
  singleStep := by
    intro k _hk
    exact HarmonicTrueMarginAbsorption.harmonicTrueMargin_singleStep_of_mass_drop k
      (harmonicMass_drop_le_two_invSq_of_cross k (H k))

/-- Therefore the sharp determinant alone reaches the positive multiscale
floor, with the exact rational model budget already discharged. -/
theorem harmonicGNS_multiscale_floor_of_cross
    (H : ∀ j : Nat,
      harmonicMassCross j ≤
        (Q'.ofNat 2 * invSqTerm 2 (by decide) j) *
          (harmonicD j * harmonicD (j + 1))) :
    ∀ k : Nat,
      (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 ≤
          canonicalHarmonicTrueMargin k ∧
        (0 : Q') <
          (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 :=
  harmonic_trueMargin_multiscale_floor (harmonicTrueMarginDrop_of_cross H)

#print axioms harmonicGNSMargin_eq_trueMargin
#print axioms harmonicGNSMargin_singleStep_of_cross
#print axioms harmonicTrueMarginDrop_of_cross
#print axioms harmonicGNS_multiscale_floor_of_cross

end YMGap.Continuum.HarmonicGNSMarginRecursion
