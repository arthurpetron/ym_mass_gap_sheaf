/-
# The vacuum complement in the completed physical BF4 cutoff carrier

The constant-one lower observable is already present in the finite-linear
physical syntax.  This file embeds it into the actual fixed-nome,
fixed-half-extent completion, proves that its completed norm is exactly one,
and defines orthogonality to it using the completed `RC`-valued inner form.

The orthogonal vectors are closed under the completed rational module
operations, so they form an explicit subtype with inherited rational module
data.  The normalized vacuum is proved not to lie in that subtype.  No
cutoff-independent transfer or spectral contraction is asserted here.

## Axiom gate

Only finite physical normalization, constructive-real equivalence, quotient
descent, and the proved completed inner/module laws are used.  There is no
classical choice, noncomputable declaration, custom axiom, or unproved
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The normalized completed vacuum -/

/-- The constant-one physical observable inside the finite-linear syntax. -/
def centralPhysicalLinearVacuum : CentralPhysicalLinearObservable :=
  atom centralPhysicalUnitObservable

/-- The constant-one vector in the actual cutoff-removed completion. -/
def centralPhysicalCutoffCompletedVacuum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  embedCentralPhysicalLinearObservable hw0 hw1 half
    centralPhysicalLinearVacuum

theorem centralPhysicalLinearVacuum_inner_self_equiv_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CReal.Equiv
      (innerLimit hw0 hw1 half
        centralPhysicalLinearVacuum centralPhysicalLinearVacuum)
      CReal.cone := by
  apply Equiv_of_approx_eqv
  intro cutoff
  have hstage := innerLimit_approx_eqv_stage hw0 hw1 half cutoff
    centralPhysicalLinearVacuum centralPhysicalLinearVacuum
  change
    (innerLimit hw0 hw1 half
      centralPhysicalLinearVacuum centralPhysicalLinearVacuum).approx cutoff ≈
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half
          centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier at hstage
  exact Q'.eqv_trans _ _ _ hstage
    (centralPhysicalWeightedInner_vacuum_one
      w (Q'.le_of_lt hw0) cutoff half)

/-- The completed constant-one physical vector has exactly unit norm. -/
theorem centralPhysicalCutoffCompletedVacuum_inner_self_eq_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      Quotient.mk CReal.crealSetoid CReal.cone := by
  unfold centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable
  rw [centralPhysicalCutoffCompletedInner_embedRep]
  exact Quotient.sound
    (centralPhysicalLinearVacuum_inner_self_equiv_one hw0 hw1 half)

/-! ## 2. The completed vacuum complement -/

/-- Orthogonality to the normalized vacuum in the actual completed carrier. -/
def CentralPhysicalCutoffCompletedVacuumOrthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) : Prop :=
  centralPhysicalCutoffCompletedInner hw0 hw1 half vector
      (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) = CReal.RCzero

/-- The corresponding dense finite-linear orthogonality condition. -/
def CentralPhysicalLinearVacuumOrthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (vector : CentralPhysicalLinearObservable) : Prop :=
  CReal.Equiv
    (innerLimit hw0 hw1 half vector centralPhysicalLinearVacuum)
    CReal.czero

/-- Every dense vacuum-orthogonal vector embeds into the completed vacuum
complement. -/
theorem centralPhysicalCutoffCompletedVacuumOrthogonal_embed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (vector : CentralPhysicalLinearObservable)
    (horthogonal : CentralPhysicalLinearVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (embedCentralPhysicalLinearObservable hw0 hw1 half vector) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable
  rw [centralPhysicalCutoffCompletedInner_embedRep]
  exact Quotient.sound horthogonal

private theorem RCadd_zero_zero :
    CReal.RCadd CReal.RCzero CReal.RCzero = CReal.RCzero := by
  exact Quotient.sound
    (Equiv_of_approx_eqv
      (fun _ => Q'.eqv_of_eq (Q'.zero_add' 0)))

theorem centralPhysicalCutoffCompletedVacuumOrthogonal_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (completedPhysicalLinearZero hw0 hw1 half) := by
  exact centralPhysicalCutoffCompletedVacuumOrthogonal_embed
    hw0 hw1 half zero (CReal.Equiv.refl CReal.czero)

theorem centralPhysicalCutoffCompletedVacuumOrthogonal_add
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hleft : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half left)
    (hright : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half right) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (completedPhysicalLinearAdd hw0 hw1 half left right) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal at hleft hright ⊢
  rw [centralPhysicalCutoffCompletedInner_add_left, hleft, hright]
  exact RCadd_zero_zero

theorem centralPhysicalCutoffCompletedVacuumOrthogonal_smul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hvector : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (completedPhysicalLinearSmul hw0 hw1 half scalar vector) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal at hvector ⊢
  rw [centralPhysicalCutoffCompletedInner_smul_left, hvector]
  exact CReal.RCscale_RCzero scalar

theorem centralPhysicalCutoffCompletedVacuumOrthogonal_neg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hvector : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (completedPhysicalLinearNeg hw0 hw1 half vector) :=
  centralPhysicalCutoffCompletedVacuumOrthogonal_smul
    hw0 hw1 half (-1) hvector

/-- The completed vacuum complement as an actual subtype. -/
def CentralPhysicalCutoffCompletedVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type :=
  {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half //
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half vector}

def centralPhysicalCutoffCompletedVacuumComplementZero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  ⟨completedPhysicalLinearZero hw0 hw1 half,
    centralPhysicalCutoffCompletedVacuumOrthogonal_zero hw0 hw1 half⟩

def centralPhysicalCutoffCompletedVacuumComplementAdd
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
        CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun left right =>
    ⟨completedPhysicalLinearAdd hw0 hw1 half left.1 right.1,
      centralPhysicalCutoffCompletedVacuumOrthogonal_add
        hw0 hw1 half left.2 right.2⟩

def centralPhysicalCutoffCompletedVacuumComplementNeg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun vector =>
    ⟨completedPhysicalLinearNeg hw0 hw1 half vector.1,
      centralPhysicalCutoffCompletedVacuumOrthogonal_neg
        hw0 hw1 half vector.2⟩

def centralPhysicalCutoffCompletedVacuumComplementSmul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Q' ->
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun scalar vector =>
    ⟨completedPhysicalLinearSmul hw0 hw1 half scalar vector.1,
      centralPhysicalCutoffCompletedVacuumOrthogonal_smul
        hw0 hw1 half scalar vector.2⟩

/-! ## 3. Inherited rational module and properness -/

/-- The completed vacuum complement inherits the actual rational-module laws
from the ambient completion. -/
def centralPhysicalCutoffCompletedVacuumComplementQModule
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CompletedQModuleData where
  Carrier := CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half
  zero := centralPhysicalCutoffCompletedVacuumComplementZero hw0 hw1 half
  add := centralPhysicalCutoffCompletedVacuumComplementAdd hw0 hw1 half
  neg := centralPhysicalCutoffCompletedVacuumComplementNeg hw0 hw1 half
  smul := centralPhysicalCutoffCompletedVacuumComplementSmul hw0 hw1 half
  add_zero_right := by
    intro vector
    apply Subtype.ext
    exact completedPhysicalLinearAdd_zero_right hw0 hw1 half vector.1
  add_zero_left := by
    intro vector
    apply Subtype.ext
    exact completedPhysicalLinearAdd_zero_left hw0 hw1 half vector.1
  neg_add := by
    intro vector
    apply Subtype.ext
    exact completedPhysicalLinearNeg_add_self hw0 hw1 half vector.1
  add_comm := by
    intro left right
    apply Subtype.ext
    exact completedPhysicalLinearAdd_comm hw0 hw1 half left.1 right.1
  add_assoc := by
    intro first second third
    apply Subtype.ext
    exact completedPhysicalLinearAdd_assoc
      hw0 hw1 half first.1 second.1 third.1
  smul_one := by
    intro vector
    apply Subtype.ext
    exact completedPhysicalLinearSmul_one hw0 hw1 half vector.1
  smul_zero := by
    intro vector
    apply Subtype.ext
    exact completedPhysicalLinearSmul_zero hw0 hw1 half vector.1
  smul_mul := by
    intro first second vector
    apply Subtype.ext
    exact completedPhysicalLinearSmul_mul
      hw0 hw1 half first second vector.1
  add_scalar_smul := by
    intro first second vector
    apply Subtype.ext
    exact completedPhysicalLinear_add_scalar_smul
      hw0 hw1 half first second vector.1
  smul_add := by
    intro scalar left right
    apply Subtype.ext
    exact completedPhysicalLinearSmul_add
      hw0 hw1 half scalar left.1 right.1

private theorem RCone_ne_RCzero :
    (Quotient.mk CReal.crealSetoid CReal.cone : CReal.RC) ≠ CReal.RCzero := by
  intro hequal
  have hequiv : CReal.Equiv CReal.cone CReal.czero := Quotient.exact hequal
  obtain ⟨N, hN⟩ := hequiv HalfPow.half
    (by decide : (0 : Q') < HalfPow.half)
  have hbad := (hN N (Nat.le_refl N)).1
  have hnot : ¬ ((1 : Q') <= (0 : Q') + HalfPow.half) := by decide
  exact hnot hbad

/-- Unit normalization makes the completed vacuum complement proper: the
vacuum itself is not orthogonal to the vacuum. -/
theorem centralPhysicalCutoffCompletedVacuum_not_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    ¬ CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
  rw [centralPhysicalCutoffCompletedVacuum_inner_self_eq_one]
  exact RCone_ne_RCzero

/-! ## Axiom audit -/

#print axioms centralPhysicalLinearVacuum_inner_self_equiv_one
#print axioms centralPhysicalCutoffCompletedVacuum_inner_self_eq_one
#print axioms centralPhysicalCutoffCompletedVacuumOrthogonal_embed
#print axioms centralPhysicalCutoffCompletedVacuumOrthogonal_add
#print axioms centralPhysicalCutoffCompletedVacuumOrthogonal_smul
#print axioms centralPhysicalCutoffCompletedVacuumComplementQModule
#print axioms centralPhysicalCutoffCompletedVacuum_not_orthogonal

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
