/-
# The physical BF4 macro transfer on the Type-modulated GNS completion

This module specializes `GNSModulusCompletion` to the literal physical BF4
stationary form.  The exact Markov contraction sends explicit null moduli to
explicit null moduli, so the macro transfer descends without any Prop-to-Type
selection.  The canonical forgetful map to the legacy completion intertwines
the two transfers and preserves the full completed inner product.

Consequently self-adjointness, positivity, norm contraction, the normalized
fixed vacuum, and invariance of its orthogonal complement all hold on the
Type-modulated carrier.  No strict gap or cross-model endpoint map is asserted.
-/

import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
import YMGap.Continuum.GNSModulusCompletion

namespace YMGap.Continuum.BF4PhysicalMarkovModulusCompletion

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. The modulated physical carrier and transfer -/

abbrev CentralPhysicalModulatedGNSCompletion
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type :=
  ModulatedGNSCompletionSpace
    (centralPhysicalSmulGNS w hw K half).toGNSData

/-- A contractive physical macro action transports an explicit null modulus
termwise. -/
def centralPhysicalMarkovMapNullModulus
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {X Y : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData}
    (hXY : CauchyNullModulus
      (centralPhysicalSmulGNS w hw K half).toGNSData X Y) :
    CauchyNullModulus
      (centralPhysicalSmulGNS w hw K half).toGNSData
      ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X)
      ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy Y) where
  modulus := hXY.modulus
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _
      (centralPhysicalMarkovApply_distSq_contraction
        w hw K half (X.seq n) (Y.seq n))
      (hXY.close epsilon hepsilon n hn)

/-- The physical BF4 macro transfer descended through the Type-modulated null
quotient. -/
def centralPhysicalModulatedMarkovTransfer
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    CentralPhysicalModulatedGNSCompletion w hw K half →
      CentralPhysicalModulatedGNSCompletion w hw K half :=
  Quotient.lift
    (fun X => Quotient.mk
      (modulatedCauchySetoid
        (centralPhysicalSmulGNS w hw K half).toGNSData)
      ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X))
    (fun _ _ h => by
      rcases h with ⟨hdata⟩
      exact Quotient.sound
        ⟨centralPhysicalMarkovMapNullModulus
          w hw K half hdata⟩)

theorem centralPhysicalModulatedMarkovTransfer_embed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalModulatedMarkovTransfer w hw K half
        (modulatedEmbedV
          (centralPhysicalSmulGNS w hw K half).toGNSData observable) =
      modulatedEmbedV
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalMarkovApply w hw K half observable) := by
  apply Quotient.sound
  exact modulatedCauchyRel_refl
    (centralPhysicalSmulGNS w hw K half).toGNSData
    ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy
      (constCauchy
        (centralPhysicalSmulGNS w hw K half).toGNSData observable))

/-! ## 2. Compatibility with the legacy completed construction -/

/-- Forgetting null moduli commutes exactly with the physical macro transfer. -/
theorem centralPhysicalModulatedMarkovTransfer_toLegacy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half) :
    toLegacyCompletion
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedMarkovTransfer w hw K half vector) =
      centralPhysicalCompletedMarkovTransfer w hw K half
        (toLegacyCompletion
          (centralPhysicalSmulGNS w hw K half).toGNSData vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  rfl

/-- Full inner-product preservation by the forgetful map, specialized to the
physical carrier. -/
theorem centralPhysicalModulatedInner_toLegacy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : CentralPhysicalModulatedGNSCompletion w hw K half) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (toLegacyCompletion
          (centralPhysicalSmulGNS w hw K half).toGNSData left)
        (toLegacyCompletion
          (centralPhysicalSmulGNS w hw K half).toGNSData right) =
      modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData left right :=
  toLegacyCompletion_inner
    (centralPhysicalSmulGNS w hw K half).toGNSData left right

/-! ## 3. Completed operator laws on the modulated carrier -/

theorem centralPhysicalModulatedMarkovTransfer_selfAdjoint
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : CentralPhysicalModulatedGNSCompletion w hw K half) :
    modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedMarkovTransfer w hw K half left) right =
      modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData left
        (centralPhysicalModulatedMarkovTransfer w hw K half right) := by
  rw [← centralPhysicalModulatedInner_toLegacy]
  rw [centralPhysicalModulatedMarkovTransfer_toLegacy]
  rw [centralPhysicalCompletedMarkovTransfer_selfAdjoint]
  rw [← centralPhysicalModulatedInner_toLegacy
    w hw K half left
      (centralPhysicalModulatedMarkovTransfer w hw K half right)]
  rw [centralPhysicalModulatedMarkovTransfer_toLegacy]

theorem centralPhysicalModulatedMarkovTransfer_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half) :
    CReal.RCnonneg
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedMarkovTransfer w hw K half vector)
        vector) := by
  rw [← centralPhysicalModulatedInner_toLegacy]
  rw [centralPhysicalModulatedMarkovTransfer_toLegacy]
  exact centralPhysicalCompletedMarkovTransfer_positive
    w hw K half
      (toLegacyCompletion
        (centralPhysicalSmulGNS w hw K half).toGNSData vector)

theorem centralPhysicalModulatedMarkovTransfer_contraction
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half) :
    CReal.RCle
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedMarkovTransfer w hw K half vector)
        (centralPhysicalModulatedMarkovTransfer w hw K half vector))
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData vector vector) := by
  rw [← centralPhysicalModulatedInner_toLegacy]
  rw [centralPhysicalModulatedMarkovTransfer_toLegacy]
  rw [← centralPhysicalModulatedInner_toLegacy]
  exact centralPhysicalCompletedMarkovTransfer_contraction
    w hw K half
      (toLegacyCompletion
        (centralPhysicalSmulGNS w hw K half).toGNSData vector)

/-! ## 4. Normalized fixed vacuum and its invariant complement -/

def centralPhysicalModulatedVacuum
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    CentralPhysicalModulatedGNSCompletion w hw K half :=
  modulatedEmbedV
    (centralPhysicalSmulGNS w hw K half).toGNSData
    centralPhysicalVacuumCarrier

theorem centralPhysicalModulatedVacuum_inner_self_eq_one
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    modulatedCinnerCompl
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedVacuum w hw K half)
        (centralPhysicalModulatedVacuum w hw K half) =
      Quotient.mk CReal.crealSetoid CReal.cone := by
  change modulatedCinnerCompl
      (centralPhysicalSmulGNS w hw K half).toGNSData
      (modulatedEmbedV
        (centralPhysicalSmulGNS w hw K half).toGNSData
        centralPhysicalVacuumCarrier)
      (modulatedEmbedV
        (centralPhysicalSmulGNS w hw K half).toGNSData
        centralPhysicalVacuumCarrier) = _
  rw [modulatedCinnerCompl_embed]
  apply Quotient.sound
  exact CReal.ofQ'_equiv_of_eqv
    (centralPhysicalWeightedInner_vacuum_one w hw K half)

theorem centralPhysicalModulatedMarkovTransfer_vacuum_fixed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalModulatedMarkovTransfer w hw K half
        (centralPhysicalModulatedVacuum w hw K half) =
      centralPhysicalModulatedVacuum w hw K half := by
  refine Eq.trans
    (centralPhysicalModulatedMarkovTransfer_embed
      w hw K half centralPhysicalVacuumCarrier) ?_
  apply Quotient.sound
  exact constCauchy_modulatedNull_of_rad
    (centralPhysicalSmulGNS w hw K half).toGNSData
    (centralPhysicalVacuumCarrier_rad_fixed w hw K half)

def CentralPhysicalModulatedVacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half) : Prop :=
  modulatedCinnerCompl
      (centralPhysicalSmulGNS w hw K half).toGNSData
      vector (centralPhysicalModulatedVacuum w hw K half) = CReal.RCzero

theorem centralPhysicalModulatedVacuumOrthogonal_preserved
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {vector : CentralPhysicalModulatedGNSCompletion w hw K half}
    (hvector :
      CentralPhysicalModulatedVacuumOrthogonal w hw K half vector) :
    CentralPhysicalModulatedVacuumOrthogonal w hw K half
      (centralPhysicalModulatedMarkovTransfer w hw K half vector) := by
  unfold CentralPhysicalModulatedVacuumOrthogonal at hvector ⊢
  rw [centralPhysicalModulatedMarkovTransfer_selfAdjoint]
  rw [centralPhysicalModulatedMarkovTransfer_vacuum_fixed]
  exact hvector

end YMGap.Continuum.BF4PhysicalMarkovModulusCompletion

#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalMarkovMapNullModulus
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer_toLegacy
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer_contraction
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedVacuum_inner_self_eq_one
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedMarkovTransfer_vacuum_fixed
#print axioms YMGap.Continuum.BF4PhysicalMarkovModulusCompletion.centralPhysicalModulatedVacuumOrthogonal_preserved
