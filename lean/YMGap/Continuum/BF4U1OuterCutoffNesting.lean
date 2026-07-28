/-
# Exact outer-cutoff nesting for the finite BF4 U(1) slab

For a fixed rational nome and corrected-slab geometry, this module packages
the finite U(1) laws at charge cutoffs `K = 0,1,2,...` into one canonical
family.  If `K ≤ L`, filtering the literal cutoff-`L` Cartesian carrier by
the old alternating-label bound recovers the cutoff-`K` carrier as an exact
list equality.  The physical summand itself is independent of the carrier
cutoff, so the larger partition splits into the old partition plus the
nonnegative genuinely new sector.

This is the algebraic precursor to an outer-cutoff-uniform tensor heat-tail
estimate.  It proves nesting and monotonicity only; it supplies no numerical
tail bound and takes no continuum or spacing limit.

All constructions use finite lists, natural numbers, and exact `Q'`
arithmetic.  There is no `Classical.*`, `Real`, `native_decide`, custom
axiom, `noncomputable`, or placeholder.
-/

import YMGap.Continuum.BF4U1SameCarrierPushforward
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

namespace YMGap.Continuum.BF4U1OuterCutoffNesting

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The canonical fixed-nome slab family -/

/-- The finite U(1) slab at charge cutoff `K`, with nome and geometry fixed
throughout the directed family. -/
def canonicalU1Slab
    (w : Q') (hw : (0 : Q') ≤ w) (half K : Nat) :
    U1SlabData where
  coupling := w
  coupling_nonnegative := hw
  chargeCutoff := K
  half := half

/-- The old alternating-label window on the fixed physical face list.
Natural labels `0,...,2K` are exactly the signed charges of magnitude at most
`K`. -/
def oldChargeWindow
    (half K : Nat) (state : ChargeLabelling) : Bool :=
  labelWithinB (2 * K)
    (slabPhysicalFaceEdges (centralExtent half)) state

/-- The genuinely new cutoff-`L` sector relative to cutoff `K`. -/
def newChargeSector
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat) : List ChargeLabelling :=
  (canonicalU1Slab w hw half L).states.filter
    (fun state => !(oldChargeWindow half K state))

/-- Total physical weight of the genuinely new cutoff-`L` sector. -/
def newChargeSectorMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat) : Q' :=
  listQSum
    (canonicalU1Slab w hw half L).physicalTerm
    (newChargeSector w hw half K L)

/-! ## 2. Exact carrier nesting -/

private theorem rangeNodupLocal : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨rangeNodupLocal n,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl n) (List.mem_range.mp hleft)

/-- The physical face list is independent of the charge cutoff. -/
theorem canonicalU1Slab_faceEdges
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat) :
    (canonicalU1Slab w hw half K).faceEdges =
      slabPhysicalFaceEdges (centralExtent half) :=
  rfl

/-- The literal carrier is the bounded Cartesian enumeration with natural
label cutoff `2K`. -/
theorem canonicalU1Slab_states
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat) :
    (canonicalU1Slab w hw half K).states =
      boundedEdgeLabellings (2 * K)
        (slabPhysicalFaceEdges (centralExtent half)) :=
  rfl

/-- Exact directed-system law: the old carrier is the old-label filter of
the larger carrier, with enumeration order preserved. -/
theorem canonicalU1Slab_states_filter
    (w : Q') (hw : (0 : Q') ≤ w)
    (half : Nat) {K L : Nat} (hKL : K ≤ L) :
    (canonicalU1Slab w hw half L).states.filter
        (oldChargeWindow half K) =
      (canonicalU1Slab w hw half K).states := by
  rw [canonicalU1Slab_states, canonicalU1Slab_states]
  unfold oldChargeWindow
  exact
    boundedEdgeLabellings_filter_cutoff
      (K := 2 * K) (L := 2 * L) (by omega)
      (slabPhysicalFaceEdges (centralExtent half))
      (by
        unfold slabPhysicalFaceEdges
        exact rangeNodupLocal _)

/-! ## 3. Cutoff-independent physical summand -/

/-- Once a labelling is named, its U(1) physical weight depends only on the
fixed nome and geometry, not on which finite carrier contains it. -/
theorem canonicalU1Slab_physicalTerm_stable
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat) (state : ChargeLabelling) :
    (canonicalU1Slab w hw half L).physicalTerm state =
      (canonicalU1Slab w hw half K).physicalTerm state :=
  rfl

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

/-- Every new-sector contribution is nonnegative. -/
theorem newChargeSectorMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K L : Nat) :
    (0 : Q') ≤ newChargeSectorMass w hw half K L := by
  unfold newChargeSectorMass
  exact
    listQSum_nonnegative_local
      (canonicalU1Slab w hw half L).physicalTerm
      (canonicalU1Slab w hw half L).physicalTerm_nonnegative
      (newChargeSector w hw half K L)

/-! ## 4. Exact partition decomposition and monotonicity -/

/-- At every larger outer cutoff, the partition is exactly the old partition
plus the nonnegative new-sector mass. -/
theorem canonicalU1Slab_partition_decomposition
    (w : Q') (hw : (0 : Q') ≤ w)
    (half : Nat) {K L : Nat} (hKL : K ≤ L) :
    (canonicalU1Slab w hw half L).partition ≈
      (canonicalU1Slab w hw half K).partition +
        newChargeSectorMass w hw half K L := by
  let large := canonicalU1Slab w hw half L
  let small := canonicalU1Slab w hw half K
  have hsplit :=
    listQSum_filter_partition
      large.physicalTerm
      (oldChargeWindow half K)
      large.states
  have holdCarrier :
      large.states.filter (oldChargeWindow half K) =
        small.states := by
    exact canonicalU1Slab_states_filter w hw half hKL
  have holdMass :
      listQSum large.physicalTerm
          (large.states.filter (oldChargeWindow half K)) ≈
        small.partition := by
    rw [holdCarrier]
    unfold U1SlabData.partition
    exact
      listQSum_congr
        (fun state =>
          Q'.eqv_of_eq
            (canonicalU1Slab_physicalTerm_stable
              w hw half K L state))
        small.states
  exact Q'.eqv_trans _ _ _
    hsplit
    (Q'.add_eqv_congr'
      holdMass
      (Q'.eqv_refl
        (newChargeSectorMass w hw half K L)))

/-- The fixed-nome finite U(1) partitions are monotone in the outer charge
cutoff. -/
theorem canonicalU1Slab_partition_monotone
    (w : Q') (hw : (0 : Q') ≤ w)
    (half : Nat) {K L : Nat} (hKL : K ≤ L) :
    (canonicalU1Slab w hw half K).partition ≤
      (canonicalU1Slab w hw half L).partition := by
  have hnew :=
    newChargeSectorMass_nonnegative w hw half K L
  have hadd :
      (canonicalU1Slab w hw half K).partition ≤
        (canonicalU1Slab w hw half K).partition +
          newChargeSectorMass w hw half K L :=
    Q'.add_le_self_of_nonneg
      (canonicalU1Slab w hw half K).partition
      (newChargeSectorMass w hw half K L)
      hnew
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (canonicalU1Slab_partition_decomposition
        w hw half hKL))

end YMGap.Continuum.BF4U1OuterCutoffNesting

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1OuterCutoffNesting.canonicalU1Slab_states_filter
#print axioms YMGap.Continuum.BF4U1OuterCutoffNesting.canonicalU1Slab_physicalTerm_stable
#print axioms YMGap.Continuum.BF4U1OuterCutoffNesting.newChargeSectorMass_nonnegative
#print axioms YMGap.Continuum.BF4U1OuterCutoffNesting.canonicalU1Slab_partition_decomposition
#print axioms YMGap.Continuum.BF4U1OuterCutoffNesting.canonicalU1Slab_partition_monotone
