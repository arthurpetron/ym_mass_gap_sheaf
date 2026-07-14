/-
# Routed exceptional sources normalized into occurrence-tree carriers

This module instantiates the two terminating tree normalizers on an
exceptional source entry.  Cross-conflicting unsafe-left/right residual pairs
are absorbed first.  A second phase then absorbs any formerly path-safe left
background occurrence made unsafe by the new tree.
-/

import YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
import YMGap.Continuum.XiExceptionalPathSafeExactWeight

namespace YMGap.Continuum.XiExceptionalSourceTreeCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathBitWeight
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
open YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
open YMGap.Continuum.XiPathSafeFactsClosure

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem CWalk.end_mem_vertices
    {a : Type} {edge : a -> a -> Bool} :
    forall {x y : a} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

/-! ## Residual and routed-mask pointwise facts -/

private theorem residualBits_avoids_vertices
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (bits : OccBitVec Gamma.length) (i : Nat) (hi : i < Gamma.length)
    (hres : (residualBits (pathOccurrenceBits Gamma.length vertices) bits).at i =
      true) : i ∉ vertices := by
  intro hiMem
  rw [residualBits_at _ _ i hi] at hres
  have hpath : (pathOccurrenceBits Gamma.length vertices).at i = true := by
    rw [pathOccurrenceBits_at Gamma.length vertices i hi]
    exact decide_eq_true hiMem
  rw [hpath] at hres
  cases hres

private theorem unsafeLeft_parts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hunsafe : (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true) :
    exceptionalPathSafe Gamma qP b1 b2 entry i = false ∧
      (routedLeftResidual Gamma qP b1 b2 entry).at i = true := by
  rw [entryUnsafeLeftBits,
    unsafeLeftBits_at (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry) i hi] at hunsafe
  have hp := (Bool.and_eq_true _ _).mp hunsafe
  have hs : exceptionalPathSafe Gamma qP b1 b2 entry i = false := by
    cases h : exceptionalPathSafe Gamma qP b1 b2 entry i
    · rfl
    · simp only [h, Bool.not_true] at hp
      cases hp.1
  exact ⟨hs, hp.2⟩

/-! ## The first, cross-pair state -/

def entryCrossTreeState
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    CrossTreeState Gamma (exceptionalMarkedIndex Gamma b1 b2 entry.1) := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  let tree := OTree.ofWalk walk
  have hvertices : tree.vertices = path.indexWalk.vertices := by
    rw [OTree.ofWalk_vertices]
    exact conflictWalkOfDisagreement_vertices Gamma
      (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hseed := (forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    path.seed_true).1
  have hbound : forall i, i ∈ tree.vertices -> i < Gamma.length := by
    intro i hi
    rw [hvertices] at hi
    exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) path.indexWalk hseed i hi
  refine
    { tree := tree
      left := entryUnsafeLeftBits Gamma qP b1 b2 entry
      right := routedRightResidual Gamma qP b1 b2 entry
      valid := OTree.ofWalk_valid walk
      nodup := ?_
      vertices_bound := hbound
      left_compatible := entryUnsafeLeftBits_compatible Gamma qP b1 b2 entry
      right_compatible :=
        (routedResiduals_compatible Gamma qP b1 b2 entry).2
      disjoint := ?_
      left_unsafe := ?_
      left_fresh := ?_
      right_fresh := ?_ }
  · rw [hvertices]
    exact path.index_nodup
  · intro i hleft
    by_cases hi : i < Gamma.length
    · have hp := unsafeLeft_parts Gamma qP b1 b2 entry i hi hleft
      cases hright : (routedRightResidual Gamma qP b1 b2 entry).at i
      · rfl
      · exact False.elim (exceptional_unsafe_cross_side_impossible
          Gamma qP b1 b2 entry entry rfl i hi
          (by simpa [exceptionalPathSafe] using hp.1) hp.2 hright)
    · have hge : Gamma.length <= i := by omega
      rw [bitVec_at_false_of_ge
        (entryUnsafeLeftBits Gamma qP b1 b2 entry) i hge] at hleft
      cases hleft
  · intro i hi hleft
    have hp := unsafeLeft_parts Gamma qP b1 b2 entry i hi hleft
    rw [hvertices]
    simpa [exceptionalPathSafe] using hp.1
  · intro i hi hleft
    have hp := unsafeLeft_parts Gamma qP b1 b2 entry i hi hleft
    rw [hvertices]
    unfold routedLeftResidual at hp
    dsimp only at hp
    exact residualBits_avoids_vertices Gamma path.indexWalk.vertices
      (switchedBranchCode Gamma b2 pair).1 i hi hp.2
  · intro i hi hright
    rw [hvertices]
    unfold routedRightResidual at hright
    dsimp only at hright
    exact residualBits_avoids_vertices Gamma path.indexWalk.vertices
      (switchedBranchCode Gamma b2 pair).2 i hi hright

def entryCrossExhaust
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :=
  (entryCrossTreeState Gamma qP b1 b2 entry).exhaust

/-! ## Freshness of the routed background after cross normalization -/

def entryTreeBackground
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedLeftResidual Gamma qP b1 b2 entry)

private theorem entryTreeBackground_parts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbg : (entryTreeBackground Gamma qP b1 b2 entry).at i = true) :
    exceptionalPathSafe Gamma qP b1 b2 entry i = true ∧
      (routedLeftResidual Gamma qP b1 b2 entry).at i = true := by
  unfold entryTreeBackground at hbg
  rw [routedBackground_at _ _ i hi] at hbg
  exact (Bool.and_eq_true _ _).mp hbg

private theorem entryTreeBackground_false_of_unsafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hunsafe : (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true) :
    (entryTreeBackground Gamma qP b1 b2 entry).at i = false := by
  have hu := unsafeLeft_parts Gamma qP b1 b2 entry i hi hunsafe
  cases hbg : (entryTreeBackground Gamma qP b1 b2 entry).at i
  · rfl
  · have hb := entryTreeBackground_parts Gamma qP b1 b2 entry i hi hbg
    rw [hb.1] at hu
    cases hu.1

private theorem entryTreeBackground_false_of_cross_right
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (u v : Nat) (hu : u < Gamma.length) (hv : v < Gamma.length)
    (huUnsafe : (entryUnsafeLeftBits Gamma qP b1 b2 entry).at u = true)
    (hconflict : compatibleB (polyAt Gamma u) (polyAt Gamma v) = false) :
    (entryTreeBackground Gamma qP b1 b2 entry).at v = false := by
  cases hbg : (entryTreeBackground Gamma qP b1 b2 entry).at v
  · rfl
  · have huParts := unsafeLeft_parts Gamma qP b1 b2 entry u hu huUnsafe
    have hvParts := entryTreeBackground_parts Gamma qP b1 b2 entry v hv hbg
    have huv : u ≠ v := by
      intro hEq
      subst v
      have hfalse : false = true := huParts.1.symm.trans hvParts.1
      cases hfalse
    have hcompatible := selectByBits_pairwise_compatible Gamma
      (routedLeftResidual Gamma qP b1 b2 entry) u v hu hv huv
      huParts.2 hvParts.2
      (routedResiduals_compatible Gamma qP b1 b2 entry).1
    rw [hconflict] at hcompatible
    cases hcompatible

private theorem entryCrossExhaust_background_fresh_aux
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (state : CrossTreeState Gamma
      (exceptionalMarkedIndex Gamma b1 b2 entry.1))
    (htree : forall i, i < Gamma.length ->
      (entryTreeBackground Gamma qP b1 b2 entry).at i = true ->
        i ∉ state.tree.vertices)
    (hleft : forall i, state.left.at i = true ->
      (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true) :
    forall i, i < Gamma.length ->
      (entryTreeBackground Gamma qP b1 b2 entry).at i = true ->
        i ∉ state.exhaust.tree.vertices := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    let pair := state.selection hcross
    have huInitial := hleft pair.leftIndex pair.left_mem
    have hbgU := entryTreeBackground_false_of_unsafe Gamma qP b1 b2 entry
      pair.leftIndex pair.left_lt huInitial
    have hbgV := entryTreeBackground_false_of_cross_right
      Gamma qP b1 b2 entry pair.leftIndex pair.rightIndex
      pair.left_lt pair.right_lt huInitial pair.cross_conflict
    apply entryCrossExhaust_background_fresh_aux Gamma qP b1 b2 entry
      (state.step hcross)
    · intro i hi hbg
      change i ∉ pair.rightIndex :: pair.leftIndex :: state.tree.vertices
      intro hmem
      rcases List.mem_cons.mp hmem with hiV | hmem
      · subst i
        rw [hbgV] at hbg
        cases hbg
      · rcases List.mem_cons.mp hmem with hiU | hmem
        · subst i
          rw [hbgU] at hbg
          cases hbg
        · exact htree i hi hbg hmem
    · intro i hiState
      exact hleft i (clearResidualAt_submask state.left
        pair.leftIndex i hiState)
  next _ => exact htree
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem entryCrossExhaust_background_fresh
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    forall i, i < Gamma.length ->
      (entryTreeBackground Gamma qP b1 b2 entry).at i = true ->
        i ∉ (entryCrossExhaust Gamma qP b1 b2 entry).tree.vertices := by
  apply entryCrossExhaust_background_fresh_aux Gamma qP b1 b2 entry
    (entryCrossTreeState Gamma qP b1 b2 entry)
  · intro i hi hbg
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    have hb := entryTreeBackground_parts Gamma qP b1 b2 entry i hi hbg
    have havoid : i ∉ path.indexWalk.vertices := by
      unfold routedLeftResidual at hb
      dsimp only at hb
      exact residualBits_avoids_vertices Gamma path.indexWalk.vertices
        (switchedBranchCode Gamma b2 pair).1 i hi hb.2
    rw [entryCrossTreeState, OTree.ofWalk_vertices,
      conflictWalkOfDisagreement_vertices]
    exact havoid
  · intro i hiState
    exact hiState

/-! ## The second, background phase -/

def entryTreeBackgroundState
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    TreeBackgroundState Gamma
      (exceptionalMarkedIndex Gamma b1 b2 entry.1) :=
  let cross := entryCrossExhaust Gamma qP b1 b2 entry
  { tree := cross.tree
    background := entryTreeBackground Gamma qP b1 b2 entry
    external := unionBits cross.left cross.right
    valid := cross.valid
    nodup := cross.nodup
    vertices_bound := cross.vertices_bound
    background_compatible :=
      pathSafe_backgroundCompatible Gamma qP b1 b2 entry
    external_compatible :=
      (entryCrossTreeState Gamma qP b1 b2 entry).exhaust_external_compatible
    background_fresh := entryCrossExhaust_background_fresh
      Gamma qP b1 b2 entry }

def entryTreeExhaust
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :=
  (entryTreeBackgroundState Gamma qP b1 b2 entry).exhaust

/-! ## Admissibility transported through both phases -/

private theorem entryRoutedExternal_q_at
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hext : (entryRoutedExternal Gamma qP b1 b2 entry).at i = true) :
    qP (polyAt Gamma i) = true := by
  exact all_selectByBits_pointwise Gamma
    (entryRoutedExternal Gamma qP b1 b2 entry) qP
    (pathSafe_externalQ Gamma qP b1 b2 entry) i hi hext

theorem entryCrossTreeState_all_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryCrossTreeState Gamma qP b1 b2 entry).AllGood
      (fun i => qP (polyAt Gamma i) = true) := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  refine
    { tree := ?_
      left := ?_
      right := ?_ }
  · intro i hiTree
    have hiPath : i ∈ path.indexWalk.vertices := by
      rw [entryCrossTreeState, OTree.ofWalk_vertices,
        conflictWalkOfDisagreement_vertices] at hiTree
      exact hiTree
    apply path.q_true (polyAt Gamma i)
    rw [path.polymer_vertices]
    exact List.mem_map.mpr ⟨i, hiPath, rfl⟩
  · intro i hi hleft
    change (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true at hleft
    apply entryRoutedExternal_q_at Gamma qP b1 b2 entry i hi
    rw [entryRoutedExternal_eq_union, unionBits_at]
    rw [hleft]
    rfl
  · intro i hi hright
    change (routedRightResidual Gamma qP b1 b2 entry).at i = true at hright
    apply entryRoutedExternal_q_at Gamma qP b1 b2 entry i hi
    rw [entryRoutedExternal_eq_union, unionBits_at]
    rw [hright]
    cases (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i <;> rfl

theorem entryCrossExhaust_all_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryCrossExhaust Gamma qP b1 b2 entry).AllGood
      (fun i => qP (polyAt Gamma i) = true) :=
  (entryCrossTreeState_all_q Gamma qP b1 b2 entry).exhaust

theorem entryTreeBackgroundState_all_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryTreeBackgroundState Gamma qP b1 b2 entry).AllGood
      (fun i => qP (polyAt Gamma i) = true) := by
  have hcross := entryCrossExhaust_all_q Gamma qP b1 b2 entry
  refine
    { tree := hcross.tree
      background := ?_
      external := ?_ }
  · intro i hi hbg
    exact all_selectByBits_pointwise Gamma
      (entryTreeBackground Gamma qP b1 b2 entry) qP
      (pathSafe_backgroundQ Gamma qP b1 b2 entry) i hi hbg
  · intro i hi hext
    change (unionBits
      (entryCrossExhaust Gamma qP b1 b2 entry).left
      (entryCrossExhaust Gamma qP b1 b2 entry).right).at i = true at hext
    rw [unionBits_at] at hext
    rcases (Bool.or_eq_true _ _).mp hext with hleft | hright
    · exact hcross.left i hi hleft
    · exact hcross.right i hi hright

theorem entryTreeExhaust_all_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryTreeExhaust Gamma qP b1 b2 entry).AllGood
      (fun i => qP (polyAt Gamma i) = true) :=
  (entryTreeBackgroundState_all_q Gamma qP b1 b2 entry).exhaust

/-! ## The marked endpoints survive both attachment phases -/

private theorem CrossTreeState.mem_exhaust_of_mem
    {Gamma : List (Polymer L)} {root i : Nat}
    (state : CrossTreeState Gamma root) (hi : i ∈ state.tree.vertices) :
    i ∈ state.exhaust.tree.vertices := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    apply CrossTreeState.mem_exhaust_of_mem (state.step hcross)
    change i ∈ (state.selection hcross).rightIndex ::
      (state.selection hcross).leftIndex :: state.tree.vertices
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
  next _ => exact hi
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

private theorem TreeBackgroundState.mem_exhaust_of_mem
    {Gamma : List (Polymer L)} {root i : Nat}
    (state : TreeBackgroundState Gamma root) (hi : i ∈ state.tree.vertices) :
    i ∈ state.exhaust.tree.vertices := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    apply TreeBackgroundState.mem_exhaust_of_mem (state.step hcheck)
    exact List.mem_cons_of_mem _ hi
  next _ => exact hi
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem entryTreeExhaust_seed_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    path.seed ∈ (entryTreeExhaust Gamma qP b1 b2 entry).tree.vertices := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hbase : path.seed ∈
      (entryCrossTreeState Gamma qP b1 b2 entry).tree.vertices := by
    rw [entryCrossTreeState, OTree.ofWalk_vertices,
      conflictWalkOfDisagreement_vertices]
    exact CWalk.end_mem_vertices path.indexWalk
  have hcross := CrossTreeState.mem_exhaust_of_mem
    (entryCrossTreeState Gamma qP b1 b2 entry) hbase
  exact TreeBackgroundState.mem_exhaust_of_mem
    (entryTreeBackgroundState Gamma qP b1 b2 entry) hcross

/-! ## The finite carrier assignment and all terminal gates -/

def entryOccurrenceTreeCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccTreeCarrierCode Gamma.length :=
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  ⟨OTree.toCode (N := Gamma.length) final.tree,
    final.background, final.external⟩

theorem entryOccurrenceTreeCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceTreeCarrierCodes Gamma := by
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  let code := OTree.toCode (N := Gamma.length) final.tree
  have hcodeBound := OTree.toCode_indicesBound final.tree
    final.valid final.vertices_bound
  have hheight : code.height <= Gamma.length := by
    rw [OTree.toCode_height]
    exact OTree.vertices_length_le_ambient Gamma final.tree final.nodup
      final.vertices_bound
  have htree : code ∈ occurrenceTreeCodesUpTo Gamma.length Gamma.length :=
    OccTreeCode.mem_occurrenceTreeCodesUpTo_of_bound code hcodeBound hheight
  exact OccTreeCarrierCode.mem_of_parts Gamma code final.background
    final.external htree

theorem entryTreeExhaust_background_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (selectByBits Gamma
      (entryTreeExhaust Gamma qP b1 b2 entry).background).all qP = true := by
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_all_of_pointwise
  intro i hi hbg
  exact (entryTreeExhaust_all_q Gamma qP b1 b2 entry).background i hi hbg

theorem entryTreeExhaust_external_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (selectByBits Gamma
      (entryTreeExhaust Gamma qP b1 b2 entry).external).all qP = true := by
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_all_of_pointwise
  intro i hi hext
  exact (entryTreeExhaust_all_q Gamma qP b1 b2 entry).external i hi hext

theorem residualActivity_eqv_familyActivity
    (w : Q') (label : L.Plaquette -> Rep) :
    forall (Gamma : List (Polymer L))
      (bits : OccBitVec Gamma.length),
      residualActivity w label Gamma bits ≈
        familyActivity w (selectByBits Gamma bits) label
  | [], .nil => Q'.eqv_refl _
  | X :: Gamma, .cons head tail => by
      have ih := residualActivity_eqv_familyActivity w label Gamma tail
      cases head
      · change 1 * residualActivity w label Gamma tail ≈
          familyActivity w (selectByBits Gamma tail) label
        exact Q'.eqv_trans _ _ _
          (Q'.one_mul_eqv _) ih
      · change activity w X label * residualActivity w label Gamma tail ≈
          activity w X label *
            familyActivity w (selectByBits Gamma tail) label
        exact Q'.mul_eqv_congr_left _ _ _ ih

theorem residualActivity_unionBits_eqv
    (w : Q') (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (label : L.Plaquette -> Rep) (hdisjoint : DisjointBits left right) :
    residualActivity w label Gamma (unionBits left right) ≈
      residualActivity w label Gamma left *
        residualActivity w label Gamma right := by
  refine Q'.eqv_trans _ _ _
    (residualActivity_eqv_familyActivity w label Gamma
      (unionBits left right)) ?_
  refine Q'.eqv_trans _ _ _
    (familyActivity_unionBits_eqv w Gamma left right label hdisjoint) ?_
  exact mul_eqv_congr_both
    (Q'.eqv_symm (residualActivity_eqv_familyActivity w label Gamma left))
    (Q'.eqv_symm (residualActivity_eqv_familyActivity w label Gamma right))

private theorem OTree.ofWalk_index_activity_eqv
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette -> Rep) :
    forall {x y : Nat} (walk : CWalk (incAtDistinct Gamma) x y),
      (OTree.ofWalk walk).activity
          (fun i => activity w (polyAt Gamma i) label) ≈
        familyActivity w (walk.vertices.map (polyAt Gamma)) label
  | _, _, .single _ => Q'.eqv_symm (Q'.mul_one_eqv _)
  | _, _, .cons _ rest => by
      simp only [OTree.ofWalk, OTree.activity, CWalk.vertices,
        List.map_cons, familyActivity_cons]
      exact Q'.mul_eqv_congr_left _ _ _
        (OTree.ofWalk_index_activity_eqv w Gamma label rest)

private theorem switchedTreeCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L -> Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switchedTreeCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L -> Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem residualTreeMaskWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette -> Rep)
    (path bits : OccBitVec Gamma.length) :
    maskWeight w Gamma label (bitMask (residualBits path bits)) =
      maskWeight w Gamma label
        (residualMask (bitMask path) (bitMask bits)) := by
  apply maskWeight_congr_on
  intro i hi
  change (residualBits path bits).at i =
    residualMask (bitMask path) (bitMask bits) i
  rw [residualBits_at path bits i hi]
  rfl

theorem occurrencePairWeight_eqv_path_routed_factors
    (w : Q') (qP b1 b2 : Polymer L -> Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette -> Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrencePairWeight w qP b1 b2 Gamma label pair ≈
      (path.polymerWalk.activityWeight w label *
        familyActivity w
          (selectByBits Gamma
            (entryTreeBackground Gamma qP b1 b2 entry)) label) *
        familyActivity w
          (selectByBits Gamma
            (entryRoutedExternal Gamma qP b1 b2 entry)) label := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  let background := routedBackground safe leftResidual
  let external := routedExternal safe leftResidual rightResidual
  have hsourceEq := occurrencePairWeight_eq_source_activity_of_mem
    w qP b1 b2 Gamma label pair entry.2
  have hleftOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.1)
  have hrightOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.2)
  rw [maskFamily_toMask_eq_selectByBits] at hleftOriginal hrightOriginal
  have hsourceToOriginal :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hsourceEq)
      (mul_eqv_congr_both (Q'.eqv_symm hleftOriginal)
        (Q'.eqv_symm hrightOriginal))
  have hswitchedLeft :
      maskWeight w Gamma label (bitMask switched.1) =
        maskWeight w Gamma label
          (switchedLeft Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedTreeCode_at_left Gamma b2 pair i hi
  have hswitchedRight :
      maskWeight w Gamma label (bitMask switched.2) =
        maskWeight w Gamma label
          (switchedRight Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedTreeCode_at_right Gamma b2 pair i hi
  have hswitch :
      maskWeight w Gamma label (bitMask switched.1) *
          maskWeight w Gamma label (bitMask switched.2) ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) := by
    rw [hswitchedLeft, hswitchedRight]
    exact maskWeight_swap_preserved w Gamma label
      (forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      (bitMask pair.1) (bitMask pair.2)
  have hpartition := maskWeight_path_partition w Gamma label
    (bitMask pathBits) (bitMask switched.1) (bitMask switched.2)
    (exceptional_pathBits_switched_exclusive Gamma qP b1 b2 entry)
  have hleftResidualEq := residualTreeMaskWeight_eq w Gamma label
    pathBits switched.1
  have hrightResidualEq := residualTreeMaskWeight_eq w Gamma label
    pathBits switched.2
  rw [← hleftResidualEq, ← hrightResidualEq] at hpartition
  have hpath := pathOccurrenceMaskWeight_eqv_walk w Gamma label path
  have hleftResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask leftResidual)
  have hrightResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask rightResidual)
  rw [maskFamily_toMask_eq_selectByBits] at hleftResidual hrightResidual
  have hunsafeExclusive : forall i, i < Gamma.length -> safe i = false ->
      leftResidual.at i = true -> rightResidual.at i = false := by
    intro i hi hunsafe hleft
    cases hright : rightResidual.at i
    · rfl
    · exact False.elim (exceptional_unsafe_cross_side_impossible
        Gamma qP b1 b2 entry entry rfl i hi
        (by simpa [safe, exceptionalPathSafe] using hunsafe)
        hleft hright)
  have hrouted := routedFamilyActivity_preserved_of_unsafe_exclusive
    w Gamma label safe leftResidual rightResidual hunsafeExclusive
  change occurrencePairWeight w qP b1 b2 Gamma label pair ≈
    (path.polymerWalk.activityWeight w label *
      familyActivity w (selectByBits Gamma background) label) *
        familyActivity w (selectByBits Gamma external) label
  refine Q'.eqv_trans _ _ _ hsourceToOriginal ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hswitch) ?_
  refine Q'.eqv_trans _ _ _ hpartition ?_
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr_both hpath
      (mul_eqv_congr_both hleftResidual hrightResidual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrouted)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem entryInitialTree_activity_eqv_path
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (entryCrossTreeState Gamma qP b1 b2 entry).tree.activity
        (fun i => activity w (polyAt Gamma i) label) ≈
      path.polymerWalk.activityWeight w label := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have htree := OTree.ofWalk_index_activity_eqv w Gamma label walk
  have hvertices : walk.vertices.map (polyAt Gamma) =
      path.polymerWalk.vertices := by
    rw [conflictWalkOfDisagreement_vertices]
    exact path.polymer_vertices.symm
  change (OTree.ofWalk walk).activity
      (fun i => activity w (polyAt Gamma i) label) ≈
    path.polymerWalk.activityWeight w label
  refine Q'.eqv_trans _ _ _ htree ?_
  rw [hvertices]
  exact Q'.eqv_symm
    (CWalk.activityWeight_eq_familyActivity_vertices
      w label path.polymerWalk)

theorem entryTreeExhaust_totalActivity_eqv_routed_factors
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (entryTreeExhaust Gamma qP b1 b2 entry).totalActivity w label ≈
      (path.polymerWalk.activityWeight w label *
        familyActivity w
          (selectByBits Gamma
            (entryTreeBackground Gamma qP b1 b2 entry)) label) *
        familyActivity w
          (selectByBits Gamma
            (entryRoutedExternal Gamma qP b1 b2 entry)) label := by
  dsimp only
  let cross0 := entryCrossTreeState Gamma qP b1 b2 entry
  let crossF := cross0.exhaust
  let background := entryTreeBackground Gamma qP b1 b2 entry
  let external := entryRoutedExternal Gamma qP b1 b2 entry
  let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
  have hbgNorm := bg0.exhaust_totalActivity_eqv w label
  have hcrossNorm := cross0.exhaust_totalActivity_eqv w label
  have hfinalUnion := residualActivity_unionBits_eqv w Gamma
    crossF.left crossF.right label crossF.disjoint
  have hinitialUnion := residualActivity_unionBits_eqv w Gamma
    cross0.left cross0.right label cross0.disjoint
  have hbgToCross : bg0.totalActivity w label ≈
      crossF.totalActivity w label *
        residualActivity w label Gamma background := by
    unfold TreeBackgroundState.totalActivity CrossTreeState.totalActivity
    change ((crossF.tree.activity
        (fun i => activity w (polyAt Gamma i) label) *
          residualActivity w label Gamma background) *
        residualActivity w label Gamma
          (unionBits crossF.left crossF.right)) ≈ _
    refine Q'.eqv_trans _
      ((crossF.tree.activity
          (fun i => activity w (polyAt Gamma i) label) *
        residualActivity w label Gamma background) *
          (residualActivity w label Gamma crossF.left *
            residualActivity w label Gamma crossF.right)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hfinalUnion
    · ring_qeqv
  have hcrossTimesBackground :
      crossF.totalActivity w label *
          residualActivity w label Gamma background ≈
        cross0.totalActivity w label *
          residualActivity w label Gamma background :=
    Q'.mul_eqv_congr_right _ _ _ hcrossNorm
  have hcrossInitialToRouted :
      cross0.totalActivity w label *
          residualActivity w label Gamma background ≈
        (cross0.tree.activity
            (fun i => activity w (polyAt Gamma i) label) *
          residualActivity w label Gamma background) *
            residualActivity w label Gamma external := by
    have hexternalEq : external = unionBits cross0.left cross0.right := by
      unfold external cross0
      exact entryRoutedExternal_eq_union Gamma qP b1 b2 entry
    unfold CrossTreeState.totalActivity
    rw [hexternalEq]
    change (((cross0.tree.activity
        (fun i => activity w (polyAt Gamma i) label) *
          residualActivity w label Gamma cross0.left) *
        residualActivity w label Gamma cross0.right) *
          residualActivity w label Gamma background) ≈
      (cross0.tree.activity
          (fun i => activity w (polyAt Gamma i) label) *
        residualActivity w label Gamma background) *
          residualActivity w label Gamma
            (unionBits cross0.left cross0.right)
    refine Q'.eqv_trans _
      ((cross0.tree.activity
          (fun i => activity w (polyAt Gamma i) label) *
        residualActivity w label Gamma background) *
          (residualActivity w label Gamma cross0.left *
            residualActivity w label Gamma cross0.right)) _ ?_ ?_
    · ring_qeqv
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm hinitialUnion)
  have hpath := entryInitialTree_activity_eqv_path
    w Gamma qP b1 b2 label entry
  have hbackground := residualActivity_eqv_familyActivity
    w label Gamma background
  have hexternal := residualActivity_eqv_familyActivity
    w label Gamma external
  refine Q'.eqv_trans _ _ _ hbgNorm ?_
  refine Q'.eqv_trans _ _ _ hbgToCross ?_
  refine Q'.eqv_trans _ _ _ hcrossTimesBackground ?_
  refine Q'.eqv_trans _ _ _ hcrossInitialToRouted ?_
  exact mul_eqv_congr_both
    (mul_eqv_congr_both hpath hbackground) hexternal

theorem entryOccurrenceTreeCarrierCode_weight_eqv_totalActivity
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry) ≈
      (entryTreeExhaust Gamma qP b1 b2 entry).totalActivity w label := by
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hb2 : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hcarrier := occurrenceTreeCarrierCodeWeight_of_certified
    w Gamma qP b1 b2 label final.tree final.valid final.vertices_bound
    final.nodup
    (entryTreeExhaust_all_q Gamma qP b1 b2 entry).tree
    facts.marked_b1 path.seed
    (entryTreeExhaust_seed_mem Gamma qP b1 b2 entry) hb2
    final.background final.external final.background_compatible
    (entryTreeExhaust_background_q Gamma qP b1 b2 entry)
    (entryTreeBackgroundState Gamma qP b1 b2 entry).exhaust_background_tree_compatible
    final.external_compatible
    (entryTreeExhaust_external_q Gamma qP b1 b2 entry)
  have hbg := residualActivity_eqv_familyActivity w label Gamma
    final.background
  have hext := residualActivity_eqv_familyActivity w label Gamma
    final.external
  exact Q'.eqv_trans _ _ _ hcarrier
    (mul_eqv_congr_both
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hbg))
      (Q'.eqv_symm hext))

theorem entryOccurrenceTreeCarrierCode_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  refine Q'.eqv_trans _ _ _
    (entryOccurrenceTreeCarrierCode_weight_eqv_totalActivity
      w Gamma qP b1 b2 label entry) ?_
  refine Q'.eqv_trans _ _ _
    (entryTreeExhaust_totalActivity_eqv_routed_factors
      w Gamma qP b1 b2 label entry) ?_
  exact Q'.eqv_symm
    (occurrencePairWeight_eqv_path_routed_factors
      w qP b1 b2 Gamma label entry)

#print axioms residualBits_avoids_vertices
#print axioms unsafeLeft_parts
#print axioms entryCrossTreeState
#print axioms entryCrossExhaust
#print axioms entryCrossExhaust_background_fresh
#print axioms entryTreeBackgroundState
#print axioms entryTreeExhaust
#print axioms entryCrossTreeState_all_q
#print axioms entryCrossExhaust_all_q
#print axioms entryTreeBackgroundState_all_q
#print axioms entryTreeExhaust_all_q
#print axioms entryTreeExhaust_seed_mem
#print axioms entryOccurrenceTreeCarrierCode_mem
#print axioms entryTreeExhaust_background_q
#print axioms entryTreeExhaust_external_q
#print axioms residualActivity_eqv_familyActivity
#print axioms residualActivity_unionBits_eqv
#print axioms occurrencePairWeight_eqv_path_routed_factors
#print axioms entryInitialTree_activity_eqv_path
#print axioms entryTreeExhaust_totalActivity_eqv_routed_factors
#print axioms entryOccurrenceTreeCarrierCode_weight_eqv_totalActivity
#print axioms entryOccurrenceTreeCarrierCode_weight_eqv_source

end YMGap.Continuum.XiExceptionalSourceTreeCarrier
