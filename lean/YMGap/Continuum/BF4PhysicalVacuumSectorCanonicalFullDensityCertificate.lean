/-
# Canonical full-density certificate and explicit power debt

The finite physical construction already provides a canonical one-step
density on the positive carrier.  This file packages its exact state-level
row and column laws, and records the remaining multi-slab identity as a
separate Type-level debt.  The latter is the statement needed by the
full-factorization adapter; it is not inferred from one-slab normalization.

No factorization, cofinal family, thermodynamic limit, or continuum claim is
constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
import YMGap.Continuum.BF4StationaryDensityBufferSplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical one-step state kernel -/

/-- The canonical state-level one-step density is the exact conditional
density already defined from the reflected physical joint. -/
def canonicalFullDensityOneStepState
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    EdgeLabelling → EdgeLabelling → Q' :=
  centralPhysicalConditionalDensity w hw cutoff half

/-! ## 1a. Indexed totalization on the genuine finite carrier -/

/-- The same canonical density, read through the exact finite index bridge.
The definition is total in its indices; all finite sums below are restricted
to the genuine `List.range` carrier. -/
def canonicalFullDensityOneStepIndex
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half row column : Nat) : Q' :=
  centralPhysicalFiniteFullDensity w hw cutoff half row column

private theorem list_getD_eq_fallback_or_mem_local
    {State : Type} (fallback : State) :
    ∀ (items : List State) (index : Nat),
      items.getD index fallback = fallback ∨
        items.getD index fallback ∈ items
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr List.mem_cons_self
  | head :: tail, index + 1 => by
      cases tail with
      | nil => simp
      | cons first rest =>
          change (first :: rest).getD index fallback = fallback ∨
            (first :: rest).getD index fallback ∈ head :: first :: rest
          rcases list_getD_eq_fallback_or_mem_local fallback
              (first :: rest) index with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem head h)

private theorem list_getD_mem_of_fallback_mem_local
    {State : Type} (fallback : State) :
    ∀ (items : List State) (index : Nat),
      fallback ∈ items → items.getD index fallback ∈ items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | _ :: _, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hmem => by
      cases tail with
      | nil =>
          have hsingle : fallback = head := List.mem_singleton.mp hmem
          subst fallback
          simp
      | cons first rest =>
          change (first :: rest).getD index fallback ∈ head :: first :: rest
          rcases list_getD_eq_fallback_or_mem_local fallback
              (first :: rest) index with hfallback | hmem'
          · simpa only [hfallback] using hmem
          · exact List.mem_cons_of_mem head hmem'

private theorem centralPhysicalFiniteStateAt_mem_positive_total
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) :
    centralPhysicalFiniteStateAt w hw cutoff half index ∈
      centralPositiveHalfStates w hw cutoff half := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum w hw cutoff half
  unfold centralPhysicalFiniteStateAt finiteListStateAt
  rw [hstates]
  exact list_getD_mem_of_fallback_mem_local zeroEdgeLabelling
    (zeroEdgeLabelling :: tail) index List.mem_cons_self

/-- On an in-range source, the indexed density has exactly normalized
weighted row mass.  This is the first part of the totalization wiring that
the full-factorization adapter requires. -/
theorem canonicalFullDensityOneStepIndex_row
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half row : Nat} :
    listQSum
        (fun column =>
          centralPhysicalFiniteWeight w hw cutoff half column *
            canonicalFullDensityOneStepIndex
              w hw cutoff half row column)
        (centralPhysicalFiniteIndexCarrier w hw cutoff half) ≈ 1 := by
  let states := centralPositiveHalfStates w hw cutoff half
  let source := centralPhysicalFiniteStateAt w hw cutoff half row
  have hsource : source ∈ states :=
    centralPhysicalFiniteStateAt_mem_positive_total w hw cutoff half row
  unfold canonicalFullDensityOneStepIndex centralPhysicalFiniteFullDensity
    centralPhysicalFiniteWeight centralPhysicalFiniteIndexCarrier
      centralPhysicalFiniteStateAt
  change listQSum
      (fun column =>
        centralPhysicalRowMarginal w hw cutoff half
            (finiteListStateAt states zeroEdgeLabelling column) *
          centralPhysicalConditionalDensity w hw cutoff half
            (finiteListStateAt states zeroEdgeLabelling row)
            (finiteListStateAt states zeroEdgeLabelling column))
      (List.range states.length) ≈ 1
  refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          centralPhysicalRowMarginal w hw cutoff half target *
            centralPhysicalConditionalDensity w hw cutoff half source target)
        states) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states zeroEdgeLabelling
        (fun target =>
          centralPhysicalRowMarginal w hw cutoff half target *
            centralPhysicalConditionalDensity w hw cutoff half source target))
  · exact centralPhysicalConditionalDensity_row_normalized hsource

/-- On an in-range target, the indexed density has exactly normalized
weighted column mass. -/
theorem canonicalFullDensityOneStepIndex_column
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half column : Nat} :
    listQSum
        (fun row =>
          centralPhysicalFiniteWeight w hw cutoff half row *
            canonicalFullDensityOneStepIndex
              w hw cutoff half row column)
        (centralPhysicalFiniteIndexCarrier w hw cutoff half) ≈ 1 := by
  let states := centralPositiveHalfStates w hw cutoff half
  let target := centralPhysicalFiniteStateAt w hw cutoff half column
  have htarget : target ∈ states :=
    centralPhysicalFiniteStateAt_mem_positive_total w hw cutoff half column
  unfold canonicalFullDensityOneStepIndex centralPhysicalFiniteFullDensity
    centralPhysicalFiniteWeight centralPhysicalFiniteIndexCarrier
      centralPhysicalFiniteStateAt
  change listQSum
      (fun row =>
        centralPhysicalRowMarginal w hw cutoff half
            (finiteListStateAt states zeroEdgeLabelling row) *
          centralPhysicalConditionalDensity w hw cutoff half
            (finiteListStateAt states zeroEdgeLabelling row)
            (finiteListStateAt states zeroEdgeLabelling column))
      (List.range states.length) ≈ 1
  refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          centralPhysicalRowMarginal w hw cutoff half source *
            centralPhysicalConditionalDensity w hw cutoff half source target)
        states) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states zeroEdgeLabelling
        (fun source =>
          centralPhysicalRowMarginal w hw cutoff half source *
            centralPhysicalConditionalDensity w hw cutoff half source target))
  · exact centralPhysicalConditionalDensity_column_normalized htarget

/-- The indexed canonical density is zero on the outgoing complement of the
canonical vacuum component.  This is the adapter's outgoing-closure seam,
with the finite index membership hypotheses kept explicit. -/
theorem canonicalFullDensityOneStepIndex_outgoing_closed
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    canonicalFullDensityOneStepIndex w hw cutoff half source target ≈ 0 :=
  centralPhysicalFiniteFullDensity_eqv_zero_of_sector_complement
    hsource htarget houtside

/-- The incoming complement is also zero.  The support component is built
from the symmetric reflected physical kernel, so the already-proved outgoing
closure transports through the kernel symmetry before the two positive-row
divisions are exposed. -/
theorem canonicalFullDensityOneStepIndex_incoming_closed
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (houtside : source ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    canonicalFullDensityOneStepIndex w hw cutoff half source target ≈ 0 := by
  have hsourceLt : source <
      centralPhysicalFiniteCarrierSize w hw cutoff half :=
    List.mem_range.mp hsource
  have htargetLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw cutoff half htarget
  have hsourceState := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half hsourceLt
  have htargetState := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half htargetLt
  have hsourceHalf := (mem_centralPositiveHalfStates_iff.mp hsourceState).1
  have htargetHalf := (mem_centralPositiveHalfStates_iff.mp htargetState).1
  have hsourcePos := (mem_centralPositiveHalfStates_iff.mp hsourceState).2
  have htargetPos := (mem_centralPositiveHalfStates_iff.mp htargetState).2
  have hrawReverse := centralPhysicalFiniteVacuumSector_rowClosed
    w hw cutoff half htarget hsourceLt houtside
  have hraw : centralPhysicalFiniteRawKernel w hw cutoff half source target ≈ 0 := by
    unfold centralPhysicalFiniteRawKernel at hrawReverse ⊢
    exact Q'.eqv_trans _ _ _
      (centralPhysicalReflectedKernel_symm w hsourceHalf htargetHalf)
      hrawReverse
  change (0 : Q') < centralPhysicalRowMarginal w hw cutoff half
      (centralPhysicalFiniteStateAt w hw cutoff half source) at hsourcePos
  unfold canonicalFullDensityOneStepIndex centralPhysicalFiniteFullDensity
  rw [centralPhysicalConditionalDensity_eq_divPos htargetPos]
  rw [centralPhysicalConditionalKernel_eq_divPos hsourcePos]
  have hnormalized :
      centralNormalizedPhysicalReflectedKernel w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source)
          (centralPhysicalFiniteStateAt w hw cutoff half target) ≈ 0 := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    unfold centralPhysicalFiniteRawKernel at hraw
    refine Q'.eqv_trans _
      (0 * Q'.recipPos
        (slabParametricKPhysicalPartition
          w cutoff (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw cutoff (centralExtent half))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hraw
    · exact Q'.zero_mul_eqv _
  have hconditional :
      Q'.divPos
          (centralNormalizedPhysicalReflectedKernel w hw cutoff half
            (centralPhysicalFiniteStateAt w hw cutoff half source)
            (centralPhysicalFiniteStateAt w hw cutoff half target))
          (centralPhysicalRowMarginal w hw cutoff half
            (centralPhysicalFiniteStateAt w hw cutoff half source))
          hsourcePos ≈ 0 := by
    unfold Q'.divPos
    refine Q'.eqv_trans _
      (0 * Q'.recipPos
        (centralPhysicalRowMarginal w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source))
        hsourcePos) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hnormalized
    · exact Q'.zero_mul_eqv _
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (centralPhysicalRowMarginal w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half target))
      htargetPos) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hconditional
  · exact Q'.zero_mul_eqv _

/-- Exact weighted row normalization on the complete positive physical
carrier. -/
theorem canonicalFullDensityOneStepState_row
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half) :
    listQSum
        (fun target =>
          centralPhysicalRowMarginal w hw cutoff half target *
            canonicalFullDensityOneStepState w hw cutoff half source target)
        (centralPositiveHalfStates w hw cutoff half) ≈ 1 :=
  centralPhysicalConditionalDensity_row_normalized hsource

/-- Exact weighted column normalization on the complete positive physical
carrier. -/
theorem canonicalFullDensityOneStepState_column
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {target : EdgeLabelling}
    (htarget : target ∈ centralPositiveHalfStates w hw cutoff half) :
    listQSum
        (fun source =>
          centralPhysicalRowMarginal w hw cutoff half source *
            canonicalFullDensityOneStepState w hw cutoff half source target)
        (centralPositiveHalfStates w hw cutoff half) ≈ 1 :=
  centralPhysicalConditionalDensity_column_normalized htarget

/-- The canonical density reconstructs the normalized reflected joint on
positive endpoints. -/
theorem canonicalFullDensityOneStepState_reconstructs_joint
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source target : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half)
    (htarget : target ∈ centralPositiveHalfStates w hw cutoff half) :
    centralNormalizedPhysicalReflectedKernel
        w hw cutoff half source target ≈
      (centralPhysicalRowMarginal w hw cutoff half source *
        centralPhysicalRowMarginal w hw cutoff half target) *
          canonicalFullDensityOneStepState
            w hw cutoff half source target :=
  normalizedJoint_eq_marginals_mul_density hsource htarget

/-! ## 2. The remaining constructive debt -/

/-- The exact multi-slab power identity still required to turn the canonical
one-step density into the adapter's full factorization.  This is a
Type-level certificate: an inhabitant must supply the actual identity for the
same physical carrier, not merely a normalization law. -/
structure CanonicalFullDensityPowerDebt
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half depth : Nat) : Type 1 where
  depth_at_least_three : 3 ≤ depth
  full_density_power : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    centralPhysicalFiniteFullDensity w hw cutoff half source target ≈
      finiteWeightedDensityPower
        (centralPhysicalFiniteIndexCarrier w hw cutoff half)
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteFullDensity w hw cutoff half)
        (depth - 1) source target

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepIndex_row
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepIndex_column
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepIndex_outgoing_closed
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepIndex_incoming_closed
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_row
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_column
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate.canonicalFullDensityOneStepState_reconstructs_joint
