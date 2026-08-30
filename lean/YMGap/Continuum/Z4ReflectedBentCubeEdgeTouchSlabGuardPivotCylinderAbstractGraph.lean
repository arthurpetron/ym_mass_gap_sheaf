/-
# A parametric color-preserving graph for every pivot-cylinder target

Keep the written slab-link list abstract.  Cylinder membership pins the unique
pivot coordinate and leaves every other coordinate free.  The realized local
edge lists can therefore be concatenated structurally without normalizing the
large concrete extent-five dependent product.

Constructive contract: dependent-list recursion, local accepted realizations,
and finite edge projection only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderAbstractGraph

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. Every occurrence of the pivot is pinned -/

def ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) → Prop
  | [], _ => True
  | linked :: rest, target =>
      (linked.1 = reflectedBentSwitchPivot →
        target.1 = reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked) ∧
      ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
        D hcutoff hextent state rest target.2

theorem reflectedBentGuardGraftEveryPivotPinnedAtCutoff_of_pivot_not_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      reflectedBentSwitchPivotLinked ∉ linkedList →
      ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
        D hcutoff hextent state linkedList target
  | [], _, _ => True.intro
  | linked :: rest, target, hpivotNotMem => by
      constructor
      · intro hpivot
        have hlinked : linked = reflectedBentSwitchPivotLinked :=
          Subtype.ext hpivot
        exact False.elim
          (hpivotNotMem (List.mem_cons.mpr (Or.inl hlinked.symm)))
      · apply
          reflectedBentGuardGraftEveryPivotPinnedAtCutoff_of_pivot_not_mem
            D hcutoff hextent state rest target.2
        intro hpivotRest
        exact hpivotNotMem (List.mem_cons.mpr (Or.inr hpivotRest))

theorem reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_every_pivot_pinned
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      linkedList.Nodup →
      reflectedBentSwitchPivotLinked ∈ linkedList →
      target ∈ reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList →
      ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
        D hcutoff hextent state linkedList target
  | [], _, _, hpivot, _ => False.elim (List.not_mem_nil hpivot)
  | linked :: rest, target, hnodup, hpivotMem, hcylinder => by
      have hnodupParts := List.nodup_cons.mp hnodup
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · simp only [ReflectedBentGuardGraftEveryPivotPinnedAtCutoff]
        simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_true] at hcylinder
        obtain ⟨tail, _, heq⟩ := List.mem_map.mp hcylinder
        have hfirst := congrArg Prod.fst heq
        have hsecond := congrArg Prod.snd heq
        constructor
        · intro _
          exact hfirst.symm
        · have hlinked : linked = reflectedBentSwitchPivotLinked :=
            Subtype.ext hpivot
          have hpivotNotRest : reflectedBentSwitchPivotLinked ∉ rest := by
            intro hpivotRest
            exact hnodupParts.1 (hlinked.symm ▸ hpivotRest)
          have htailPinned :=
            reflectedBentGuardGraftEveryPivotPinnedAtCutoff_of_pivot_not_mem
              D hcutoff hextent state rest tail hpivotNotRest
          exact hsecond ▸ htailPinned
      · simp only [ReflectedBentGuardGraftEveryPivotPinnedAtCutoff]
        simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_false] at hcylinder
        obtain ⟨localTarget, _, hlocal⟩ := List.mem_flatMap.mp hcylinder
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hlocal
        have hfirst := congrArg Prod.fst heq
        have hsecond := congrArg Prod.snd heq
        constructor
        · intro hpivotFalse
          exact False.elim (hpivot hpivotFalse)
        · have hpivotTail : reflectedBentSwitchPivotLinked ∈ rest := by
            rcases List.mem_cons.mp hpivotMem with hhead | hrest
            · have hvalue := congrArg Subtype.val hhead
              exact False.elim (hpivot hvalue.symm)
            · exact hrest
          have htailPinned :=
            reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_every_pivot_pinned
              D hcutoff hextent state rest tail hnodupParts.2
                hpivotTail htail
          exact hsecond ▸ htailPinned

/-! ## 2. The structurally aligned projected graph -/

def reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) → List SlabProjectedFaceEdge
  | [], _ => []
  | linked :: rest, target =>
      slabProjectedFaceEdges
          (slabLinkFaceStrandEdges D.cutoff 5
            (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
            (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
              D hcutoff hextent state linked target.1)
            (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
              D hcutoff hextent state linked target.1)) ++
        reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTargetAtCutoff
          D hcutoff hextent state rest target.2

def reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked) → List SlabProjectedFaceEdge
  | [], _ => []
  | linked :: rest, target =>
      slabProjectedFaceEdges
          (slabLinkFaceStrandEdges D.cutoff 5
            (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
            (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
              D hcutoff hextent state linked target.1)
            (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
              D hcutoff hextent state linked target.1)) ++
        reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTargetAtCutoff
          D hcutoff hextent state rest target.2

def reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List SlabProjectedFaceEdge :=
  reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target ++
    reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target

/-! ## 3. Every edge in the parametric graph preserves color -/

theorem reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
          D hcutoff hextent state linkedList target →
      ∀ projected,
        projected ∈
          reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTargetAtCutoff
            D hcutoff hextent state linkedList target →
        reflectedBentGuardTargetFaceColorB projected.source =
          reflectedBentGuardTargetFaceColorB projected.target
  | [], _, _, _, hmem => False.elim (List.not_mem_nil hmem)
  | linked :: rest, target, hpinned, projected, hprojected => by
      rcases List.mem_append.mp hprojected with hlocal | htail
      · unfold slabProjectedFaceEdges at hlocal
        obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
        unfold slabLinkFaceStrandEdges at hedge
        obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
        simpa only [slabLinkFaceStrandEdgeOfTerminal,
          slabLinkPhysicalTerminalFaceStrandCopy,
          slabLinkFaceStrandOccurrenceToCopy] using
            reflectedBentGuardGraftRealizedLeftTerminalForTarget_color_eq_at_cutoff
              D hcutoff hextent state linked target.1 hpinned.1 terminal
      · exact
          reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTarget_color_eq
            D hcutoff hextent state rest target.2 hpinned.2 projected htail

theorem reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked))
      (projected : SlabProjectedFaceEdge),
      projected ∈
          reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTargetAtCutoff
            D hcutoff hextent state linkedList target →
        reflectedBentGuardTargetFaceColorB projected.source =
          reflectedBentGuardTargetFaceColorB projected.target
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | linked :: rest, target, projected, hprojected => by
      rcases List.mem_append.mp hprojected with hlocal | htail
      · unfold slabProjectedFaceEdges at hlocal
        obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
        unfold slabLinkFaceStrandEdges at hedge
        obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
        simpa only [slabLinkFaceStrandEdgeOfTerminal,
          slabLinkPhysicalTerminalFaceStrandCopy,
          slabLinkFaceStrandOccurrenceToCopy] using
            reflectedBentGuardGraftRealizedRightTerminalForTarget_color_eq_at_cutoff
              D hcutoff hextent state linked target.1 terminal
      · exact
          reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTarget_color_eq
            D hcutoff hextent state rest target.2 projected htail

theorem reflectedBentGuardGraftPivotCylinderProjectedFaceEdgeFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (hcylinder : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  have hpinned :=
    reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_every_pivot_pinned
      D hcutoff hextent state linkedList target hnodup hpivot hcylinder
  rcases List.mem_append.mp hprojected with hleft | hright
  · exact
      reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTarget_color_eq
        D hcutoff hextent state linkedList target hpinned projected hleft
  · exact
      reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTarget_color_eq
        D hcutoff hextent state linkedList target projected hright

#print axioms ReflectedBentGuardGraftEveryPivotPinnedAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_every_pivot_pinned
#print axioms reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesFromTarget_color_eq
#print axioms reflectedBentGuardGraftRealizedRightProjectedFaceEdgesFromTarget_color_eq
#print axioms reflectedBentGuardGraftPivotCylinderProjectedFaceEdgeFromTarget_color_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderAbstractGraph
