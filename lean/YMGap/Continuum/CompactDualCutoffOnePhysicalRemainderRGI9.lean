/-
# Cutoff-one physical remainder as an RG-I9 distortion stream

The exact physical pushforward module defines the actual cutoff-one
whole-slab remainder and proves only the universal estimate `L1 <= 2`.
This module gives the honest next interface.

A trajectory of cutoff-one slab scale pairs determines the physical error
stream

    n |-> physicalRemainderL1 at scale n.

If that stream is pointwise dominated by a constructively summable majorant,
it inherits the majorant's cap and tail modulus and therefore vanishes
pointwise.  This is the exact handoff to RG-I9.

This does NOT prove the missing majorization, and it does NOT upgrade the
cutoff-one construction to arbitrary representation cutoff.  A genuinely
cutoff-uniform theorem still requires the general-cutoff physical Gibbs
pushforward and a majorant uniform in that cutoff and the volume.

## Axiom gate

Constructive exact-rational and finite-list algebra only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
import YMGap.RG.DominatedSummableDistortion

namespace YMGap.Continuum.CompactDualCutoffOnePhysicalRemainderRGI9

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.RG.DominatedSummableDistortion
open YMGap.RG.StableDynamics

/-- A sequence of physical corrected slabs at the presently constructed
fine representation cutoff one. -/
structure CutoffOnePhysicalRemainderTrajectory : Type where
  slab : Nat → SlabScalePair
  fineCutoff : ∀ n, (slab n).fine.cutoff = 1
  coarseCouplingPositive :
    ∀ n, (0 : Q') < (slab n).coarse.coupling

namespace CutoffOnePhysicalRemainderTrajectory

/-- Actual exact `L1` physical Gibbs-pushforward discrepancy at each scale. -/
def remainderTerm
    (trajectory : CutoffOnePhysicalRemainderTrajectory) : QSeq :=
  fun n =>
    physicalRemainderL1
      (trajectory.slab n)
      (trajectory.fineCutoff n)
      (trajectory.coarseCouplingPositive n)

theorem remainderTerm_nonnegative
    (trajectory : CutoffOnePhysicalRemainderTrajectory)
    (n : Nat) :
    (0 : Q') ≤ trajectory.remainderTerm n := by
  unfold remainderTerm physicalRemainderL1
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.abs_nonneg _

theorem remainderTerm_le_two
    (trajectory : CutoffOnePhysicalRemainderTrajectory)
    (n : Nat) :
    trajectory.remainderTerm n ≤ 2 :=
  physicalRemainderL1_le_two
    (trajectory.slab n)
    (trajectory.fineCutoff n)
    (trajectory.coarseCouplingPositive n)

end CutoffOnePhysicalRemainderTrajectory

/-- The precise remaining cutoff-one analytic estimate: a summable majorant
for the actual physical remainder stream. -/
structure CutoffOnePhysicalRemainderMajorant
    (trajectory : CutoffOnePhysicalRemainderTrajectory) : Type where
  majorant : QSeq
  budget : SummableDistortion majorant
  dominates :
    ∀ n, trajectory.remainderTerm n ≤ majorant n

namespace CutoffOnePhysicalRemainderMajorant

/-- The actual physical remainder inherits a complete RG-I9 distortion
certificate. -/
def physicalDistortion
    {trajectory : CutoffOnePhysicalRemainderTrajectory}
    (estimate : CutoffOnePhysicalRemainderMajorant trajectory) :
    SummableDistortion trajectory.remainderTerm :=
  ofPointwiseDomination
    trajectory.remainderTerm estimate.majorant
    trajectory.remainderTerm_nonnegative
    estimate.dominates estimate.budget

theorem physicalRemainder_vanishes
    {trajectory : CutoffOnePhysicalRemainderTrajectory}
    (estimate : CutoffOnePhysicalRemainderMajorant trajectory)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat)
    (hn : estimate.budget.modulus epsilon ≤ n) :
    trajectory.remainderTerm n ≤ epsilon := by
  exact term_le_after_modulus
    estimate.physicalDistortion epsilon hepsilon n hn

theorem physical_modulus_eq_majorant
    {trajectory : CutoffOnePhysicalRemainderTrajectory}
    (estimate : CutoffOnePhysicalRemainderMajorant trajectory)
    (epsilon : Q') :
    estimate.physicalDistortion.modulus epsilon =
      estimate.budget.modulus epsilon :=
  rfl

#print axioms CutoffOnePhysicalRemainderTrajectory.remainderTerm_nonnegative
#print axioms CutoffOnePhysicalRemainderTrajectory.remainderTerm_le_two
#print axioms physicalDistortion
#print axioms physicalRemainder_vanishes
#print axioms physical_modulus_eq_majorant

end CutoffOnePhysicalRemainderMajorant

end YMGap.Continuum.CompactDualCutoffOnePhysicalRemainderRGI9
