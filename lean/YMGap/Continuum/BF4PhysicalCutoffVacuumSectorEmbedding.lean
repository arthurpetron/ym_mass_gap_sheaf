/-
# Canonical physical vacuum-sector embedding across representation cutoffs

An old positive-row state persists at every larger representation cutoff.
This file locates that same literal state in the later finite carrier by its
faithful mixed-radix code.  The resulting explicit index map preserves the
vacuum root and every true edge of the symmetrized production-kernel support
graph.  Constructive rooted-component transport therefore sends the old
canonical vacuum component into the later one, with literal state equality.

This is qualitative carrier and component compatibility at fixed coupling
and fixed finite volume.  The physical weights and kernel values change with
the cutoff; no exact form intertwining or cutoff-uniform contraction rate is
asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
import YMGap.Continuum.FiniteBoolGraphRootComponentMap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponentMap
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Explicit old-to-new carrier index map -/

/-- Constructive first-occurrence locator for natural-number codes.  The
empty-list fallback is zero, but every use below carries a membership proof. -/
def firstNatCodeIndex (target : Nat) : List Nat → Nat
  | [] => 0
  | head :: tail =>
      if target = head then 0 else firstNatCodeIndex target tail + 1

private theorem firstNatCodeIndex_lt_length_of_mem (target : Nat) :
    ∀ {items : List Nat}, target ∈ items →
      firstNatCodeIndex target items < items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases heq : target = head
      · simp [firstNatCodeIndex, heq]
      · have htail : target ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail
        have ih := firstNatCodeIndex_lt_length_of_mem target htail
        simp only [firstNatCodeIndex, heq, if_false, List.length_cons]
        omega

private theorem firstNatCodeIndex_getElem_eq (target : Nat) :
    ∀ {items : List Nat} (hmem : target ∈ items),
      items[firstNatCodeIndex target items]'(
        firstNatCodeIndex_lt_length_of_mem target hmem) = target
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases heq : target = head
      · subst target
        simp [firstNatCodeIndex]
      · have htail : target ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail
        simpa only [firstNatCodeIndex, heq, if_false,
          List.getElem_cons_succ] using
            (firstNatCodeIndex_getElem_eq target htail)

/-- Locate an old finite-carrier state in the later positive carrier by the
faithful code computed with the later cutoff. -/
def centralPhysicalFiniteCutoffIndexMap
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half index : Nat) : Nat :=
  let source := centralPhysicalFiniteStateAt w hw base half index
  let targetCodes :=
    (centralPositiveHalfStates w hw later half).map
      (bf4StateCode later half)
  firstNatCodeIndex (bf4StateCode later half source) targetCodes

private theorem centralPhysicalFiniteStateAt_mem_later_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFiniteStateAt w hw base half index ∈
      centralPositiveHalfStates w hw later half := by
  exact mem_centralPositiveHalfStates_of_le hw hcutoff
    (centralPhysicalFiniteStateAt_mem_positive
      w hw base half hindex)

/-- Every in-range old carrier index maps to an in-range later index. -/
theorem centralPhysicalFiniteCutoffIndexMap_lt
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFiniteCutoffIndexMap
        w hw base later half index <
      centralPhysicalFiniteCarrierSize w hw later half := by
  have hsourceLater :=
    centralPhysicalFiniteStateAt_mem_later_positive hcutoff hindex
  unfold centralPhysicalFiniteCutoffIndexMap
  change
    firstNatCodeIndex
        (bf4StateCode later half
          (centralPhysicalFiniteStateAt w hw base half index))
        ((centralPositiveHalfStates w hw later half).map
          (bf4StateCode later half)) <
      (centralPositiveHalfStates w hw later half).length
  rw [← List.length_map (bf4StateCode later half)]
  exact firstNatCodeIndex_lt_length_of_mem _
    (List.mem_map.mpr
      ⟨centralPhysicalFiniteStateAt w hw base half index,
        hsourceLater, rfl⟩)

/-- The explicit later index represents literally the same old physical
state. -/
theorem centralPhysicalFiniteStateAt_cutoffIndexMap_eq
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFiniteStateAt w hw later half
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half index) =
      centralPhysicalFiniteStateAt w hw base half index := by
  let laterStates := centralPositiveHalfStates w hw later half
  let source := centralPhysicalFiniteStateAt w hw base half index
  let laterCodes := laterStates.map (bf4StateCode later half)
  have hsourceLater : source ∈ laterStates := by
    exact centralPhysicalFiniteStateAt_mem_later_positive hcutoff hindex
  have hcodeMem : bf4StateCode later half source ∈ laterCodes :=
    List.mem_map.mpr ⟨source, hsourceLater, rfl⟩
  have hltCodes :
      firstNatCodeIndex (bf4StateCode later half source) laterCodes <
        laterCodes.length :=
    firstNatCodeIndex_lt_length_of_mem _ hcodeMem
  have hltStates :
      firstNatCodeIndex (bf4StateCode later half source) laterCodes <
        laterStates.length := by
    simpa [laterCodes] using hltCodes
  have hcodeEq :
      laterCodes[firstNatCodeIndex
        (bf4StateCode later half source) laterCodes] =
        bf4StateCode later half source :=
    firstNatCodeIndex_getElem_eq _ hcodeMem
  have htargetLater :
      laterStates.getD
          (firstNatCodeIndex (bf4StateCode later half source) laterCodes)
          zeroEdgeLabelling ∈ laterStates := by
    rw [← List.getElem_eq_getD
      (l := laterStates)
      (i := firstNatCodeIndex (bf4StateCode later half source) laterCodes)
      (h := hltStates)
      zeroEdgeLabelling]
    exact List.getElem_mem hltStates
  have htargetCode :
      bf4StateCode later half
          (laterStates.getD
            (firstNatCodeIndex (bf4StateCode later half source) laterCodes)
            zeroEdgeLabelling) =
        bf4StateCode later half source := by
    rw [← List.getElem_eq_getD
      (l := laterStates)
      (i := firstNatCodeIndex (bf4StateCode later half source) laterCodes)
      (h := hltStates)
      zeroEdgeLabelling]
    simpa [laterCodes] using hcodeEq
  have hstateEq :
      laterStates.getD
          (firstNatCodeIndex (bf4StateCode later half source) laterCodes)
          zeroEdgeLabelling = source :=
    bf4StateCode_injective_on_positive
      htargetLater hsourceLater htargetCode
  simpa [centralPhysicalFiniteStateAt,
    centralPhysicalFiniteCutoffIndexMap, laterStates, laterCodes, source]
    using hstateEq

/-- The explicit cutoff map fixes the distinguished vacuum index. -/
theorem centralPhysicalFiniteCutoffIndexMap_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteCutoffIndexMap
      w hw base later half 0 = 0 := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum w hw later half
  unfold centralPhysicalFiniteCutoffIndexMap
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum w hw base half,
    hstates]
  simp [firstNatCodeIndex]

/-! ## 2. Support-graph homomorphism -/

/-- A directed nonzero support test at the old cutoff remains true after both
endpoints are sent to their later carrier indices. -/
theorem centralPhysicalFiniteKernelNonzeroB_cutoffIndexMap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half row column : Nat}
    (hcutoff : base ≤ later)
    (hrow : row < centralPhysicalFiniteCarrierSize w hw base half)
    (hcolumn : column < centralPhysicalFiniteCarrierSize w hw base half)
    (hnonzero : centralPhysicalFiniteKernelNonzeroB
      w hw base half row column = true) :
    centralPhysicalFiniteKernelNonzeroB w hw later half
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half row)
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half column) = true := by
  have hrawNonzero : ¬
      centralPhysicalFiniteRawKernel w hw base half row column ≈ 0 := by
    simpa only [centralPhysicalFiniteKernelNonzeroB,
      decide_eq_true_eq] using hnonzero
  have hrowHalf :
      centralPhysicalFiniteStateAt w hw base half row ∈
        centralHalfStates base half :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive
        w hw base half hrow)).1
  have hcolumnHalf :
      centralPhysicalFiniteStateAt w hw base half column ∈
        centralHalfStates base half :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive
        w hw base half hcolumn)).1
  have hlaterNonzero : ¬
      centralPhysicalReflectedKernel w later half
          (centralPhysicalFiniteStateAt w hw base half row)
          (centralPhysicalFiniteStateAt w hw base half column) ≈ 0 := by
    apply centralPhysicalReflectedKernel_not_eqv_zero_of_le
      hw hcutoff hrowHalf hcolumnHalf
    simpa only [centralPhysicalFiniteRawKernel] using hrawNonzero
  unfold centralPhysicalFiniteKernelNonzeroB
    centralPhysicalFiniteRawKernel
  rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      hcutoff hrow,
    centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      hcutoff hcolumn]
  simp only [decide_eq_true_eq]
  exact hlaterNonzero

/-- Every true edge of the symmetrized old support graph maps to a true edge
of the later support graph. -/
theorem centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half row column : Nat}
    (hcutoff : base ≤ later)
    (hrow : row < centralPhysicalFiniteCarrierSize w hw base half)
    (hcolumn : column < centralPhysicalFiniteCarrierSize w hw base half)
    (hadjacent : centralPhysicalFiniteSupportAdjacentB
      w hw base half row column = true) :
    centralPhysicalFiniteSupportAdjacentB w hw later half
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half row)
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half column) = true := by
  unfold centralPhysicalFiniteSupportAdjacentB at hadjacent ⊢
  simp only [Bool.or_eq_true] at hadjacent ⊢
  rcases hadjacent with hforward | hreverse
  · exact Or.inl
      (centralPhysicalFiniteKernelNonzeroB_cutoffIndexMap
        hcutoff hrow hcolumn hforward)
  · exact Or.inr
      (centralPhysicalFiniteKernelNonzeroB_cutoffIndexMap
        hcutoff hcolumn hrow hreverse)

/-- The explicit cutoff index map is a rooted homomorphism of the two finite
physical support graphs. -/
def centralPhysicalFiniteCutoffRootedGraphHom
    (w : Q') (hw : (0 : Q') ≤ w)
    {base later half : Nat} (hcutoff : base ≤ later) :
    RootedFiniteBoolGraphHom
      (centralPhysicalFiniteSupportAdjacentB w hw base half)
      (centralPhysicalFiniteIndexCarrier w hw base half) 0
      (centralPhysicalFiniteSupportAdjacentB w hw later half)
      (centralPhysicalFiniteIndexCarrier w hw later half) 0 where
  toFun := centralPhysicalFiniteCutoffIndexMap
    w hw base later half
  map_root := centralPhysicalFiniteCutoffIndexMap_zero
    w hw base later half
  map_vertex := by
    intro index hindex
    apply List.mem_range.mpr
    exact centralPhysicalFiniteCutoffIndexMap_lt hcutoff
      (List.mem_range.mp hindex)
  map_edge := by
    intro row column hrow hcolumn hadjacent
    exact centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      hcutoff (List.mem_range.mp hrow) (List.mem_range.mp hcolumn)
      hadjacent

/-! ## 3. Canonical vacuum-component compatibility -/

/-- Every index in the old canonical vacuum component maps into the later
canonical vacuum component. -/
theorem centralPhysicalFiniteVacuumSectorIndexMap_mem
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    centralPhysicalFiniteCutoffIndexMap w hw base later half index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw later half := by
  exact RootedFiniteBoolGraphHom.map_mem_targetRootComponent
    (centralPhysicalFiniteCutoffRootedGraphHom w hw hcutoff)
    (centralPhysicalFiniteSupportAdjacentB_symmetric w hw base half)
    (centralPhysicalFiniteSupportAdjacentB_symmetric w hw later half)
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw base half)
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw later half)
    hindex

/-- State-level monotonicity of the canonical physical vacuum sector at fixed
coupling and fixed finite volume. -/
theorem centralPhysicalFiniteVacuumSectorStates_mono
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    {state : EdgeLabelling}
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorStates w hw base half) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w hw later half := by
  rcases List.mem_map.mp hstate with ⟨index, hcomponent, hstateEq⟩
  have hindex := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hcomponent
  have hmapped := centralPhysicalFiniteVacuumSectorIndexMap_mem
    hcutoff hcomponent
  apply centralPhysicalFiniteVacuumSectorState_mem_of_index
    w hw later half hmapped
  exact (centralPhysicalFiniteStateAt_cutoffIndexMap_eq
    hcutoff hindex).trans hstateEq

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding.centralPhysicalFiniteCutoffIndexMap_lt
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding.centralPhysicalFiniteStateAt_cutoffIndexMap_eq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding.centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding.centralPhysicalFiniteVacuumSectorIndexMap_mem
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding.centralPhysicalFiniteVacuumSectorStates_mono
