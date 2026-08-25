/-
# Exact finite deficit compiler for canonical BF4 correlated capacity debt

The regional interfaces expose five pointwise inequalities, but those
inequalities need not remain analytic inputs.  At every cutoff transition the
carriers are finite and the correlated debt is an explicit rational.  We can
therefore compute the exact maximum one-step deficit on the transported-old
region and on each of the three shell return faces.

This module constructs those four rational streams.  Their located finite
maxima automatically inhabit all regional pointwise envelopes.  The remaining
analytic inputs are precisely four `AntitoneTailControl` witnesses asserting
that the computed deficit streams are summable.  These witnesses may be proved
in parallel, yet they stay connected to the same exact debt observable and
rejoin the existing single-envelope, maximum, budget, and completed-family
path.

No tail-control witness, total budget, or initial slack is supplied.  The
fixed strong-coupling anchor is not the physical AF/grouped-BF4 trajectory,
and no thermodynamic, continuum, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation

private theorem le_add_of_abs_sub_le_local
    {left right bound : Q'}
    (hbound : Q'.abs (left + -right) <= bound) :
    left <= right + bound := by
  have hsub : left + -right <= bound :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (left + -right)) hbound
  have hadd : (left + -right) + right <= bound + right :=
    Q'.add_le_add_right (left + -right) bound right hsub
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv bound right)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-right) right) ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left left (-right + right) 0
      (Q'.neg_add_self_eqv right)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' left)

private def oldNewShellPairDecidable
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInOldNewShell scale pair) := by
  unfold AnchorPairInOldNewShell AnchorIndexInNewShell
  infer_instance

private def newOldShellPairDecidable
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInNewOldShell scale pair) := by
  unfold AnchorPairInNewOldShell AnchorIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInNewNewShell scale pair) := by
  unfold AnchorPairInNewNewShell AnchorIndexInNewShell
  infer_instance

local instance oldNewShellPairDecidableInstance
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInOldNewShell scale pair) :=
  oldNewShellPairDecidable scale pair

local instance newOldShellPairDecidableInstance
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInNewOldShell scale pair) :=
  newOldShellPairDecidable scale pair

local instance newNewShellPairDecidableInstance
    (scale : Nat) (pair : Nat × Nat) :
    Decidable (AnchorPairInNewNewShell scale pair) :=
  newNewShellPairDecidable scale pair

/-! ## 1. Exact transported-old two-sided deficit -/

def anchorTransportedCapacityDebtDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let current := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence scale pair
  let next := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  Q'.max' (Q'.abs (current + -next)) (Q'.abs (next + -current))

def anchorTransportedCapacityDebtDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorTransportedCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs scale)

theorem anchorTransportedCapacityDebtDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorTransportedCapacityDebtDeficitMaximum scale := by
  unfold anchorTransportedCapacityDebtDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorTransportedCapacityDebtDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

theorem anchorTransportedCapacityDebtDeficitOnPair_le_maximum
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    anchorTransportedCapacityDebtDeficitOnPair scale pair <=
      anchorTransportedCapacityDebtDeficitMaximum scale := by
  unfold anchorTransportedCapacityDebtDeficitMaximum
  exact le_listQMaxZero_of_mem _ _ hpair

/-- The only open content of the transported-old region is summability of its
explicitly computed finite deficit maximum. -/
structure AnchorCanonicalTransportedCapacityDebtDeficitTail : Type 1 where
  tailControl : AntitoneTailControl
    anchorTransportedCapacityDebtDeficitMaximum

def AnchorCanonicalTransportedCapacityDebtDeficitTail.toEnvelope
    (data : AnchorCanonicalTransportedCapacityDebtDeficitTail) :
    AnchorCanonicalTransportedCapacityDebtEnvelope where
  variation := anchorTransportedCapacityDebtDeficitMaximum
  variation_nonnegative :=
    anchorTransportedCapacityDebtDeficitMaximum_nonnegative
  tailControl := data.tailControl
  current_le_next := by
    intro scale pair hpair
    apply le_add_of_abs_sub_le_local
    exact Q'.le_trans' _ _ _
      (Q'.le_max'_left _ _)
      (anchorTransportedCapacityDebtDeficitOnPair_le_maximum
        scale pair hpair)
  next_le_current := by
    intro scale pair hpair
    apply le_add_of_abs_sub_le_local
    exact Q'.le_trans' _ _ _
      (Q'.le_max'_right _ _)
      (anchorTransportedCapacityDebtDeficitOnPair_le_maximum
        scale pair hpair)

/-! ## 2. Exact shell-face deficits against literal return pairs -/

def anchorOldNewReturnCapacityDebtDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  if AnchorPairInOldNewShell scale pair then
    Q'.abs
      (anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
        -anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence scale
          (anchorOldNewReturnPair scale pair))
  else 0

def anchorNewOldReturnCapacityDebtDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  if AnchorPairInNewOldShell scale pair then
    Q'.abs
      (anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
        -anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence scale
          (anchorNewOldReturnPair scale pair))
  else 0

def anchorNewNewReturnCapacityDebtDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  if AnchorPairInNewNewShell scale pair then
    Q'.abs
      (anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
        -anchorRoutedCapacityDebtOnPair
          anchorCanonicalPositiveRoutingSequence scale
          (anchorNewNewReturnPair scale pair))
  else 0

def anchorOldNewReturnCapacityDebtDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorOldNewReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))

def anchorNewOldReturnCapacityDebtDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorNewOldReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))

def anchorNewNewReturnCapacityDebtDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorNewNewReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))

private theorem oldNewShellPair_mem_next
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInOldNewShell scale pair) :
    pair ∈ anchorVacuumSectorPairs (scale + 1) := by
  change pair ∈
    cartesian (anchorVacuumSectorIndices (scale + 1))
      (anchorVacuumSectorIndices (scale + 1))
  exact (mem_cartesian_iff _ _ pair).mpr
    ⟨anchorEmbeddedOldIndexCarrier_mem_next
        scale pair.1 hpair.1,
      hpair.2.1⟩

private theorem newOldShellPair_mem_next
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewOldShell scale pair) :
    pair ∈ anchorVacuumSectorPairs (scale + 1) := by
  change pair ∈
    cartesian (anchorVacuumSectorIndices (scale + 1))
      (anchorVacuumSectorIndices (scale + 1))
  exact (mem_cartesian_iff _ _ pair).mpr
    ⟨hpair.1.1,
      anchorEmbeddedOldIndexCarrier_mem_next
        scale pair.2 hpair.2⟩

private theorem newNewShellPair_mem_next
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewNewShell scale pair) :
    pair ∈ anchorVacuumSectorPairs (scale + 1) := by
  change pair ∈
    cartesian (anchorVacuumSectorIndices (scale + 1))
      (anchorVacuumSectorIndices (scale + 1))
  exact (mem_cartesian_iff _ _ pair).mpr
    ⟨hpair.1.1, hpair.2.1⟩

theorem anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorOldNewReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorOldNewReturnCapacityDebtDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorOldNewReturnCapacityDebtDeficitOnPair
  by_cases hpair : AnchorPairInOldNewShell scale pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorNewOldReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorNewOldReturnCapacityDebtDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorNewOldReturnCapacityDebtDeficitOnPair
  by_cases hpair : AnchorPairInNewOldShell scale pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorNewNewReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorNewNewReturnCapacityDebtDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorNewNewReturnCapacityDebtDeficitOnPair
  by_cases hpair : AnchorPairInNewNewShell scale pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem anchorOldNewReturnCapacityDebtDeficitOnPair_le_maximum
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInOldNewShell scale pair) :
    Q'.abs
        (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
          -anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorOldNewReturnPair scale pair)) <=
      anchorOldNewReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorOldNewReturnCapacityDebtDeficitMaximum
  have hmax := le_listQMaxZero_of_mem
    (anchorOldNewReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))
    (oldNewShellPair_mem_next scale pair hpair)
  unfold anchorOldNewReturnCapacityDebtDeficitOnPair at hmax
  rw [if_pos hpair] at hmax
  exact hmax

theorem anchorNewOldReturnCapacityDebtDeficitOnPair_le_maximum
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewOldShell scale pair) :
    Q'.abs
        (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
          -anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNewOldReturnPair scale pair)) <=
      anchorNewOldReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorNewOldReturnCapacityDebtDeficitMaximum
  have hmax := le_listQMaxZero_of_mem
    (anchorNewOldReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))
    (newOldShellPair_mem_next scale pair hpair)
  unfold anchorNewOldReturnCapacityDebtDeficitOnPair at hmax
  rw [if_pos hpair] at hmax
  exact hmax

theorem anchorNewNewReturnCapacityDebtDeficitOnPair_le_maximum
    (scale : Nat) (pair : Nat × Nat)
    (hpair : AnchorPairInNewNewShell scale pair) :
    Q'.abs
        (anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
          -anchorRoutedCapacityDebtOnPair
            anchorCanonicalPositiveRoutingSequence scale
            (anchorNewNewReturnPair scale pair)) <=
      anchorNewNewReturnCapacityDebtDeficitMaximum scale := by
  unfold anchorNewNewReturnCapacityDebtDeficitMaximum
  have hmax := le_listQMaxZero_of_mem
    (anchorNewNewReturnCapacityDebtDeficitOnPair scale)
    (anchorVacuumSectorPairs (scale + 1))
    (newNewShellPair_mem_next scale pair hpair)
  unfold anchorNewNewReturnCapacityDebtDeficitOnPair at hmax
  rw [if_pos hpair] at hmax
  exact hmax

/-! ## 3. Four parallel tail controls construct every regional envelope -/

structure AnchorCanonicalOldNewCapacityDebtDeficitTail : Type 1 where
  tailControl : AntitoneTailControl
    anchorOldNewReturnCapacityDebtDeficitMaximum

structure AnchorCanonicalNewOldCapacityDebtDeficitTail : Type 1 where
  tailControl : AntitoneTailControl
    anchorNewOldReturnCapacityDebtDeficitMaximum

structure AnchorCanonicalNewNewCapacityDebtDeficitTail : Type 1 where
  tailControl : AntitoneTailControl
    anchorNewNewReturnCapacityDebtDeficitMaximum

def AnchorCanonicalOldNewCapacityDebtDeficitTail.toReturnEnvelope
    (data : AnchorCanonicalOldNewCapacityDebtDeficitTail) :
    AnchorCanonicalOldNewReturnCapacityDebtEnvelope where
  variation := anchorOldNewReturnCapacityDebtDeficitMaximum
  variation_nonnegative :=
    anchorOldNewReturnCapacityDebtDeficitMaximum_nonnegative
  tailControl := data.tailControl
  next_le_return := by
    intro scale pair hpair
    exact le_add_of_abs_sub_le_local
      (anchorOldNewReturnCapacityDebtDeficitOnPair_le_maximum
        scale pair hpair)

def AnchorCanonicalNewOldCapacityDebtDeficitTail.toReturnEnvelope
    (data : AnchorCanonicalNewOldCapacityDebtDeficitTail) :
    AnchorCanonicalNewOldReturnCapacityDebtEnvelope where
  variation := anchorNewOldReturnCapacityDebtDeficitMaximum
  variation_nonnegative :=
    anchorNewOldReturnCapacityDebtDeficitMaximum_nonnegative
  tailControl := data.tailControl
  next_le_return := by
    intro scale pair hpair
    exact le_add_of_abs_sub_le_local
      (anchorNewOldReturnCapacityDebtDeficitOnPair_le_maximum
        scale pair hpair)

def AnchorCanonicalNewNewCapacityDebtDeficitTail.toReturnEnvelope
    (data : AnchorCanonicalNewNewCapacityDebtDeficitTail) :
    AnchorCanonicalNewNewReturnCapacityDebtEnvelope where
  variation := anchorNewNewReturnCapacityDebtDeficitMaximum
  variation_nonnegative :=
    anchorNewNewReturnCapacityDebtDeficitMaximum_nonnegative
  tailControl := data.tailControl
  next_le_return := by
    intro scale pair hpair
    exact le_add_of_abs_sub_le_local
      (anchorNewNewReturnCapacityDebtDeficitOnPair_le_maximum
        scale pair hpair)

def anchorCanonicalCapacityDebtEnvelopeOfDeficitTails
    (transport : AnchorCanonicalTransportedCapacityDebtDeficitTail)
    (oldNew : AnchorCanonicalOldNewCapacityDebtDeficitTail)
    (newOld : AnchorCanonicalNewOldCapacityDebtDeficitTail)
    (newNew : AnchorCanonicalNewNewCapacityDebtDeficitTail) :
    AnchorCanonicalCapacityDebtEnvelope :=
  anchorCanonicalCapacityDebtEnvelopeOfTransportAndReturns
    transport.toEnvelope
    oldNew.toReturnEnvelope newOld.toReturnEnvelope newNew.toReturnEnvelope

/-! ## 4. The unchanged budget/slack closure -/

def anchorCanonicalCapacityDebtPersistenceOfDeficitTails
    (transport : AnchorCanonicalTransportedCapacityDebtDeficitTail)
    (oldNew : AnchorCanonicalOldNewCapacityDebtDeficitTail)
    (newOld : AnchorCanonicalNewOldCapacityDebtDeficitTail)
    (newNew : AnchorCanonicalNewNewCapacityDebtDeficitTail)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorCanonicalCapacityDebtMaximumVariation
        (anchorCanonicalCapacityDebtEnvelopeOfDeficitTails
          transport oldNew newOld newNew)).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 + budget <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence where
  envelope := anchorCanonicalCapacityDebtEnvelopeOfDeficitTails
    transport oldNew newOld newNew
  budget := budget
  budget_pos := budget_pos
  budget_from_zero := budget_from_zero
  initial_closure := initial_closure

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorTransportedCapacityDebtDeficitMaximum_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.AnchorCanonicalTransportedCapacityDebtDeficitTail.toEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorOldNewReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorNewOldReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorNewNewReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.AnchorCanonicalOldNewCapacityDebtDeficitTail.toReturnEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.AnchorCanonicalNewOldCapacityDebtDeficitTail.toReturnEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.AnchorCanonicalNewNewCapacityDebtDeficitTail.toReturnEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorCanonicalCapacityDebtEnvelopeOfDeficitTails
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.anchorCanonicalCapacityDebtPersistenceOfDeficitTails
