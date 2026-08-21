/-
# The completed physical BF4 cutoff inner form

Representative independence now permits the outer pairing limit to descend to
an `RC = CReal/Equiv`-valued form on the actual completed physical carrier.
This module performs that quotient descent and proves that the completed form
agrees with the original limiting physical pairing on the dense constant
image.

The construction remains at fixed nome and fixed finite half-extent.  Its
algebraic and positivity laws, a cutoff-independent transfer, and every
thermodynamic or continuum claim remain separate frontiers.

## Axiom gate

The only quotient identification is justified by the proved representative
invariance.  No classical choice, noncomputable declaration, custom axiom, or
unproved placeholder is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined
open YMGap.Continuum.CRealSeminormCompletion

/-- The representative pairing limit as an element of the genuine real
quotient. -/
def physicalCauchyPairingLimitR
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : CReal.RC :=
  Quotient.mk CReal.crealSetoid
    (physicalCauchyPairingLimit hw0 hw1 half X Y)

/-- The completed fixed-nome physical BF4 inner form. -/
def centralPhysicalCutoffCompletedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half -> CReal.RC :=
  Quotient.lift₂
    (fun X Y => physicalCauchyPairingLimitR hw0 hw1 half X Y)
    (fun X X' Y Y' hX hY => by
      rcases hX with ⟨hXdata⟩
      rcases hY with ⟨hYdata⟩
      exact Quotient.sound
        (physicalCauchyPairingLimit_welldef
          hw0 hw1 half hXdata hYdata))

@[simp] theorem centralPhysicalCutoffCompletedInner_mk
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid X)
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y) =
      physicalCauchyPairingLimitR hw0 hw1 half X Y := rfl

/-- On constant representatives the outer limit is the original dense
physical limiting pairing. -/
theorem physicalCauchyPairingLimit_constant_equiv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant left)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant right))
      (innerLimit hw0 hw1 half left right) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let X := D.constant left
  let Y := D.constant right
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    physicalCauchyPairingSeq_converges
      hw0 hw1 half X Y epsilon hepsilon
  obtain ⟨K, hK⟩ := hN N (Nat.le_refl _)
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hforward, hbackward⟩ := hK k hk
  exact ⟨hbackward, hforward⟩

/-- The completed form extends the cutoff-removed physical pairing on the
dense finite-linear image. -/
theorem centralPhysicalCutoffCompletedInner_embedRep
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalLinearObservable) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).embedRep left)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).embedRep right) =
      Quotient.mk CReal.crealSetoid
        (innerLimit hw0 hw1 half left right) := by
  exact Quotient.sound
    (physicalCauchyPairingLimit_constant_equiv
      hw0 hw1 half left right)

/-! ## Axiom audit -/

#print axioms physicalCauchyPairingLimitR
#print axioms centralPhysicalCutoffCompletedInner
#print axioms physicalCauchyPairingLimit_constant_equiv
#print axioms centralPhysicalCutoffCompletedInner_embedRep

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
