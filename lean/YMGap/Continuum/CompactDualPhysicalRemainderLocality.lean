/-
# Locality forces the corrected-slab remainder to carry cylinder mismatch

The finite corrected-slab remainder algebra permits any nonnegative,
row-normalized, reflection-intertwining, source-dependent kernel.  That
interface alone is too weak for RG: a global finite-law coupling can refresh
from the complete coarse Gibbs law and make the remainder vanish without
implementing a geometric block map.

This module adds the first non-vacuous physical locality test.  For a chosen
fine/coarse Boolean block cylinder, a kernel is required to put zero mass on
pairs with different cylinder values.  Exact finite Fubini then proves:

* the blocked cylinder mass is exactly the fine cylinder mass;
* the difference from the actual coarse Gibbs cylinder is exactly the
  selected mass of the already-defined physical remainder; and
* its absolute value is bounded by the full `L¹` remainder.

Consequently a vanishing physical remainder cannot be obtained from an
event-local kernel unless the corresponding fine and coarse Gibbs cylinder
masses really agree.  This is the fail-closed bridge from the whole-kernel
construction to the uniform remainder estimate.

## Axiom gate

Finite exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualFiniteBlockRemainder
import YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

namespace YMGap.Continuum.CompactDualPhysicalRemainderLocality

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

local infix:50 " ≈ " => Q'.eqv

namespace PhysicalKernel

abbrev SlabLabelling :=
  YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling

/-- Weakest useful geometric test on a corrected-slab kernel: the selected
fine and coarse block cylinders must agree on every pair carrying nonzero
kernel mass. -/
def CylinderLocal
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (fineEvent coarseEvent : SlabLabelling → Bool) : Prop :=
  CylinderSupportLocalOn
    S.fine.physicalLabellings S.coarse.physicalLabellings
    fineEvent coarseEvent K.kernel

/-- Fine physical Gibbs mass of the selected source cylinder. -/
def fineCylinderMass
    {S : SlabScalePair} (_K : SlabScalePair.FiniteSlabKernel S)
    (fineEvent : SlabLabelling → Bool) : Q' :=
  finiteEventMass S.fine.normalizedMass
    S.fine.physicalLabellings fineEvent

/-- Pushed physical mass of the selected coarse cylinder. -/
def blockedCylinderMass
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (coarseEvent : SlabLabelling → Bool) : Q' :=
  finiteEventMass K.blockedMass
    S.coarse.physicalLabellings coarseEvent

/-- Actual coarse physical Gibbs mass of the selected target cylinder. -/
def coarseCylinderMass
    {S : SlabScalePair} (_K : SlabScalePair.FiniteSlabKernel S)
    (coarseEvent : SlabLabelling → Bool) : Q' :=
  finiteEventMass S.coarse.normalizedMass
    S.coarse.physicalLabellings coarseEvent

/-- The part of the actual signed physical remainder selected by a coarse
block cylinder. -/
def cylinderRemainder
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (coarseEvent : SlabLabelling → Bool) : Q' :=
  listQSum
    (fun target => if coarseEvent target then K.remainder target else 0)
    S.coarse.physicalLabellings

/-- Event locality and row normalization force exact transport of the
selected cylinder from the fine physical Gibbs law to the blocked law. -/
theorem blockedCylinderMass_eqv_fineCylinderMass
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (fineEvent coarseEvent : SlabLabelling → Bool)
    (hlocal : CylinderLocal K fineEvent coarseEvent) :
    fineCylinderMass K fineEvent ≈
      blockedCylinderMass K coarseEvent := by
  exact supportLocal_pushforward_forces_eventMass_eqv
    S.fine.normalizedMass S.fine.physicalLabellings
    K.blockedMass S.coarse.physicalLabellings
    fineEvent coarseEvent K.kernel hlocal
    K.row_normalized
    (fun _ _ => Q'.eqv_refl _)

/-- The exact physical pushforward decomposition remains exact after
restriction to any target cylinder. -/
theorem blockedCylinderMass_decomposition
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (coarseEvent : SlabLabelling → Bool) :
    blockedCylinderMass K coarseEvent ≈
      coarseCylinderMass K coarseEvent +
        cylinderRemainder K coarseEvent := by
  unfold blockedCylinderMass coarseCylinderMass cylinderRemainder
    finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (if coarseEvent target then
            S.coarse.normalizedMass target else 0) +
          (if coarseEvent target then K.remainder target else 0))
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    cases hevent : coarseEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
    · simp only [if_true]
      exact K.pushforward_decomposition target
  · exact listQSum_add
      (fun target =>
        if coarseEvent target then
          S.coarse.normalizedMass target else 0)
      (fun target =>
        if coarseEvent target then K.remainder target else 0)
      S.coarse.physicalLabellings

/-- Under cylinder locality, the physical fine/coarse cylinder defect is
literally the selected signed remainder. -/
theorem fineCoarseCylinderDefect_eqv_remainder
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (fineEvent coarseEvent : SlabLabelling → Bool)
    (hlocal : CylinderLocal K fineEvent coarseEvent) :
    fineCylinderMass K fineEvent +
        -(coarseCylinderMass K coarseEvent) ≈
      cylinderRemainder K coarseEvent := by
  refine Q'.eqv_trans _
    (blockedCylinderMass K coarseEvent +
      -(coarseCylinderMass K coarseEvent)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (blockedCylinderMass_eqv_fineCylinderMass K
        fineEvent coarseEvent hlocal)
  refine Q'.eqv_trans _
    ((coarseCylinderMass K coarseEvent +
        cylinderRemainder K coarseEvent) +
      -(coarseCylinderMass K coarseEvent)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (blockedCylinderMass_decomposition K coarseEvent)
  refine Q'.eqv_trans _
    (coarseCylinderMass K coarseEvent +
      (cylinderRemainder K coarseEvent +
        -(coarseCylinderMass K coarseEvent))) _ ?_ ?_
  · exact Q'.add_assoc_eqv _ _ _
  · exact Q'.eqv_symm
      (Q'.add_sub_cancel_eqv
        (cylinderRemainder K coarseEvent)
        (coarseCylinderMass K coarseEvent))

private theorem abs_masked_listQSum_le
    {A : Type} (value : A → Q') (event : A → Bool) :
    ∀ states : List A,
      Q'.abs
          (listQSum
            (fun state => if event state then value state else 0)
            states) ≤
        listQSum (fun state => Q'.abs (value state)) states
  | [] => by
      change Q'.abs (0 : Q') ≤ (0 : Q')
      decide
  | head :: tail => by
      cases hevent : event head
      · simp only [listQSum, hevent, Bool.false_eq_true, if_false]
        rw [Q'.zero_add']
        have htail := abs_masked_listQSum_le value event tail
        have hhead :
            listQSum (fun state => Q'.abs (value state)) tail ≤
              Q'.abs (value head) +
                listQSum (fun state => Q'.abs (value state)) tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (Q'.abs (value head))
            (listQSum (fun state => Q'.abs (value state)) tail)
            (Q'.abs_nonneg (value head))
          rw [Q'.zero_add'] at hadd
          exact hadd
        exact Q'.le_trans' _ _ _ htail hhead
      · simp only [listQSum, hevent, if_true]
        exact Q'.le_trans' _ _ _
          (Q'.abs_add_le' (value head)
            (listQSum
              (fun state => if event state then value state else 0)
              tail))
          (Q'.add_le_add_left _ _ _
            (abs_masked_listQSum_le value event tail))

/-- A selected cylinder cannot contain more signed remainder than the full
physical `L¹` remainder. -/
theorem cylinderRemainder_abs_le_remainderL1
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (coarseEvent : SlabLabelling → Bool) :
    Q'.abs (cylinderRemainder K coarseEvent) ≤ K.remainderL1 := by
  unfold cylinderRemainder
  exact abs_masked_listQSum_le K.remainder coarseEvent
    S.coarse.physicalLabellings

/-- **Locality fence for the physical remainder.**  Every block cylinder
intertwined pointwise by the kernel gives a certified lower bound on the
actual physical remainder.  Therefore a cutoff/volume-uniform vanishing
remainder estimate must in particular control every such physical Gibbs
cylinder mismatch uniformly. -/
theorem fineCoarseCylinderDefect_abs_le_remainderL1
    {S : SlabScalePair} (K : SlabScalePair.FiniteSlabKernel S)
    (fineEvent coarseEvent : SlabLabelling → Bool)
    (hlocal : CylinderLocal K fineEvent coarseEvent) :
    Q'.abs
        (fineCylinderMass K fineEvent +
          -(coarseCylinderMass K coarseEvent)) ≤
      K.remainderL1 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (fineCoarseCylinderDefect_eqv_remainder K
          fineEvent coarseEvent hlocal)))
    (cylinderRemainder_abs_le_remainderL1 K coarseEvent)

end PhysicalKernel

end YMGap.Continuum.CompactDualPhysicalRemainderLocality

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.CompactDualPhysicalRemainderLocality.PhysicalKernel.blockedCylinderMass_eqv_fineCylinderMass
#print axioms YMGap.Continuum.CompactDualPhysicalRemainderLocality.PhysicalKernel.blockedCylinderMass_decomposition
#print axioms YMGap.Continuum.CompactDualPhysicalRemainderLocality.PhysicalKernel.fineCoarseCylinderDefect_eqv_remainder
#print axioms YMGap.Continuum.CompactDualPhysicalRemainderLocality.PhysicalKernel.cylinderRemainder_abs_le_remainderL1
#print axioms YMGap.Continuum.CompactDualPhysicalRemainderLocality.PhysicalKernel.fineCoarseCylinderDefect_abs_le_remainderL1
