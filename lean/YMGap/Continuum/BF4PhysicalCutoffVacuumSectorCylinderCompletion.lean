/-
# Completion of the dense BF4 vacuum-sector cylinder union

The finite vacuum-sector realization supplies an actual finite-linear
observable for every coefficient on every canonical root component.  This
module takes the constructive Cauchy completion of their union, using exactly
the squared distance inherited from the already constructed cutoff-removed
physical GNS form.

The inherited-distance definition gives a canonical map from the sector
completion into the global physical completion.  It is injective: a global
closeness witness between two mapped sector Cauchy representatives is
literally a sector closeness witness.  Thus the new type is a concrete
completion of the sector-cylinder union, not a postulated subspace.

The map need not be surjective.  No theorem here says that all global
vacuum-orthogonal vectors belong to this sector, that the completed transfer
preserves it, or that a carrier-independent strict rate exists.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The algebraic union of finite canonical sector cylinders -/

/-- One presentation in the union of all finite canonical vacuum-sector
cylinder spaces.  Only finitely many values of `coefficient` are read: those
whose indices belong to the canonical component at `base`. -/
structure CentralPhysicalVacuumSectorCylinderPresentation
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type where
  base : Nat
  coefficient : Nat → Q'

/-- Interpret a sector presentation as the literal finite-linear cylinder
observable constructed by the preceding realization theorem. -/
def CentralPhysicalVacuumSectorCylinderPresentation.toLinearObservable
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation :
      CentralPhysicalVacuumSectorCylinderPresentation w hw half) :
    CentralPhysicalLinearObservable :=
  centralPhysicalFiniteVacuumSectorLinearObservable
    w hw presentation.base half presentation.coefficient

/-- The sector union carries exactly the squared seminorm induced by its
image in the global cutoff-removed finite-linear carrier. -/
def centralPhysicalVacuumSectorCylinderSquaredSeminorm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : SquaredSeminorm where
  Carrier := CentralPhysicalVacuumSectorCylinderPresentation
    w (Q'.le_of_lt hw0) half
  distSq left right := physicalLinearDistSq hw0 hw1 half
    left.toLinearObservable right.toLinearObservable
  distSq_refl presentation :=
    physicalLinearDistSq_refl hw0 hw1 half
      presentation.toLinearObservable
  distSq_symm left right :=
    physicalLinearDistSq_symm hw0 hw1 half
      left.toLinearObservable right.toLinearObservable
  distSq_nonneg left right :=
    physicalLinearDistSq_nonneg hw0 hw1 half
      left.toLinearObservable right.toLinearObservable
  distSq_triangle first middle last :=
    physicalLinearDistSq_triangle hw0 hw1 half
      first.toLinearObservable middle.toLinearObservable
      last.toLinearObservable
  null_congr hleft hright :=
    physicalLinearDistSq_null_congr hw0 hw1 half hleft hright

/-- The choice-free explicit-modulus completion of the union of all finite
canonical vacuum-sector cylinder presentations. -/
abbrev CentralPhysicalCutoffVacuumSectorCylinderCompletion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type :=
  (centralPhysicalVacuumSectorCylinderSquaredSeminorm
    hw0 hw1 half).Completion

/-! ## 2. The canonical inherited-distance embedding -/

/-- A sector Cauchy representative is a global physical Cauchy representative
after applying the cylinder realization term by term. -/
def centralPhysicalVacuumSectorCylinderCauchyToGlobal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := (X.seq stage).toLinearObservable
  modulus := X.modulus
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    exact X.isCauchy epsilon hepsilon first second hfirst hsecond

/-- Sector closeness is preserved by the termwise global realization. -/
def centralPhysicalVacuumSectorCylinderCloseToGlobal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X Y) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y) where
  modulus := h.modulus
  close := by
    intro epsilon hepsilon stage hstage
    simpa only [centralPhysicalCutoffLinearSquaredSeminorm,
      centralPhysicalVacuumSectorCylinderSquaredSeminorm,
      centralPhysicalVacuumSectorCylinderCauchyToGlobal] using
        (h.close epsilon hepsilon stage hstage)

/-- Conversely, global closeness of two realized sector representatives is
already sector closeness because both squared distances are definitionally
the inherited one. -/
def centralPhysicalVacuumSectorCylinderCloseOfGlobal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y)) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X Y where
  modulus := h.modulus
  close := by
    intro epsilon hepsilon stage hstage
    simpa only [centralPhysicalCutoffLinearSquaredSeminorm,
      centralPhysicalVacuumSectorCylinderSquaredSeminorm,
      centralPhysicalVacuumSectorCylinderCauchyToGlobal] using
        (h.close epsilon hepsilon stage hstage)

/-- Canonical map from the completed sector-cylinder union into the existing
global cutoff-removed physical completion. -/
def centralPhysicalVacuumSectorCylinderCompletionToGlobal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half →
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  Quotient.lift
    (fun X => Quotient.mk
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).completionSetoid
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X))
    (fun X Y h => by
      rcases h with ⟨hclose⟩
      exact Quotient.sound
        ⟨centralPhysicalVacuumSectorCylinderCloseToGlobal hclose⟩)

@[simp] theorem
    centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation) =
      embedCentralPhysicalLinearObservable hw0 hw1 half
        presentation.toLinearObservable := rfl

/-- The canonical map loses no completed sector information. -/
theorem centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} :
    Function.Injective
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (hw0 := hw0) (hw1 := hw1) (half := half)) := by
  intro left right heq
  refine Quotient.inductionOn₂ left right ?_ heq
  intro X Y hxy
  apply Quotient.sound
  have hglobal :
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).CompletionRel
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y) :=
    Quotient.exact hxy
  rcases hglobal with ⟨hclose⟩
  exact ⟨centralPhysicalVacuumSectorCylinderCloseOfGlobal hclose⟩

/-! ## 3. Dense sector norms inside the global completed pairing -/

private theorem cReal_equiv_of_eventual_approx_eqv
    {left right : CReal} (start : Nat)
    (h : ∀ stage, start ≤ stage →
      left.approx stage ≈ right.approx stage) :
    CReal.Equiv left right := by
  intro epsilon hepsilon
  refine ⟨start, fun stage hstage => ?_⟩
  have heq := h stage hstage
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm heq))
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-- The global dense limiting norm of one realized sector presentation is the
same Bishop real as its pulled sector diagonal cutoff limit. -/
theorem centralPhysicalVacuumSectorCylinder_innerLimit_equiv_pulledDiagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (innerLimit hw0 hw1 half
        presentation.toLinearObservable presentation.toLinearObservable)
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
        hw0 hw1 presentation.base half presentation.coefficient) := by
  apply cReal_equiv_of_eventual_approx_eqv presentation.base
  intro later hcutoff
  refine Q'.eqv_trans _
    ((centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) later half).toGNSData.B
      presentation.toLinearObservable.value
      presentation.toLinearObservable.value) _ ?_ ?_
  · exact innerLimit_approx_eqv_stage
      hw0 hw1 half later
      presentation.toLinearObservable presentation.toLinearObservable
  refine Q'.eqv_trans _
    (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
      presentation.toLinearObservable.value
      presentation.toLinearObservable.value) _ ?_ ?_
  · exact Q'.eqv_of_eq (centralPhysicalSmulGNS_B_eq
      w (Q'.le_of_lt hw0) later half _ _)
  · exact centralPhysicalFiniteVacuumSectorLinearObservable_diagonal_eqv_pulled
      hcutoff presentation.coefficient

/-- On dense sector constants, the actual global completed inner product is
represented by the pulled sector diagonal cutoff limit. -/
theorem centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation)) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  rw [centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep]
  exact Eq.trans
    (centralPhysicalCutoffCompletedInner_embedRep
      hw0 hw1 half presentation.toLinearObservable
        presentation.toLinearObservable)
    (Quotient.sound
      (centralPhysicalVacuumSectorCylinder_innerLimit_equiv_pulledDiagonal
        hw0 hw1 half presentation))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion.centralPhysicalVacuumSectorCylinderSquaredSeminorm
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion.centralPhysicalVacuumSectorCylinderCompletionToGlobal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion.centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion.centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled
