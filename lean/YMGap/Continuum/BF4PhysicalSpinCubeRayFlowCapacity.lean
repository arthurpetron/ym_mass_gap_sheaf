/-
# Exact weighted-flow loads on the all-spin vacuum star

The explicit spin-cube spokes give a two-edge route between every pair of
non-vacuum spin cubes.  This module puts the exact stationary-product demand
on those routes and regroups it by oriented vacuum spoke.

For an admitted excited spin `s`, each oriented spoke has the exact load

  2 * pi(s) * mass(ray).

The ray mass is a literal subsum of the canonical vacuum-sector mass and is
therefore at most one.  After cancelling the positive source weight, capacity
of both spoke orientations follows from the local condition

  2 * delta <= P(s, vacuum).

Thus the growing ray has no carrier-cardinality payment: its remaining datum
is a concrete return-probability lower bound.  This module does not prove that
bound uniformly, does not route the rest of the carrier, and makes no
thermodynamic/continuum or Clay claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
import YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem zeroEdgeLabelling_mem_bounded_local (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

/-! ## 1. The excited spin-ray indices and their stationary mass -/

def centralLowerExcitedSpinCubeIndex
    (w : Q') (hw : (0 : Q') ≤ w) (K offset : Nat) : Nat :=
  centralLowerSpinCubeIndex w hw K (offset + 1)

theorem centralLowerExcitedSpinCubeIndex_injective_on
    {w : Q'} (hw : (0 : Q') < w) {K left right : Nat}
    (hleft : left < K) (hright : right < K)
    (heq : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K left =
      centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K right) :
    left = right := by
  unfold centralLowerExcitedSpinCubeIndex at heq
  have hleftBound : left + 1 ≤ K := by omega
  have hrightBound : right + 1 ≤ K := by omega
  have hstates : centralLowerSpinCubeState (left + 1) =
      centralLowerSpinCubeState (right + 1) := by
    rw [← centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hleftBound,
      ← centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hrightBound,
      heq]
  have hspins := centralLowerSpinCubeState_injective hstates
  omega

theorem centralLowerExcitedSpinCubeIndex_ne_zero
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset ≠ 0 := by
  intro hzero
  have hbound : offset + 1 ≤ K := by omega
  have hlocated :=
    centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hbound
  unfold centralLowerExcitedSpinCubeIndex at hzero
  rw [hzero,
    centralPhysicalFiniteStateAt_zero_eq_vacuum] at hlocated
  have hzeroCube : centralLowerSpinCubeState 0 = zeroEdgeLabelling := by
    funext id
    simp [centralLowerSpinCubeState, zeroEdgeLabelling]
  have hcubes : centralLowerSpinCubeState (offset + 1) =
      centralLowerSpinCubeState 0 :=
    hlocated.symm.trans hzeroCube.symm
  have hspinZero := centralLowerSpinCubeState_injective hcubes
  omega

def centralLowerExcitedSpinCubeIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (List.range K).map
    (centralLowerExcitedSpinCubeIndex w hw K)

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem centralLowerExcitedSpinCubeIndices_nodup
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (centralLowerExcitedSpinCubeIndices
      w (Q'.le_of_lt hw) K).Nodup := by
  unfold centralLowerExcitedSpinCubeIndices
  apply nodup_map_of_injOn
  · exact rangeNodupLocal _
  · intro left hleft right hright heq
    exact centralLowerExcitedSpinCubeIndex_injective_on hw
      (List.mem_range.mp hleft) (List.mem_range.mp hright) heq

theorem centralLowerExcitedSpinCubeIndices_subset_vacuumSector
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ∀ index,
      index ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K →
        index ∈ centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0 := by
  intro index hindex
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hindex
  exact centralLowerSpinCubeIndex_mem_vacuumSector hw
    (by
      have hlt := List.mem_range.mp hoffset
      omega)

def centralLowerExcitedSpinCubeRayMass
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum (centralPhysicalFiniteWeight w hw K 0)
    (centralLowerExcitedSpinCubeIndices w hw K)

theorem centralLowerExcitedSpinCubeRayMass_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') ≤ centralLowerExcitedSpinCubeRayMass
      w (Q'.le_of_lt hw) K := by
  unfold centralLowerExcitedSpinCubeRayMass
  apply listQSum_nonnegative_on
  intro index hindex
  exact Q'.le_of_lt
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerExcitedSpinCubeIndices_subset_vacuumSector
        hw K index hindex))

theorem centralLowerExcitedSpinCubeRayMass_le_sectorMass
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw) K ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K 0 := by
  unfold centralLowerExcitedSpinCubeRayMass
    centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  apply listQSum_le_of_injective
    (centralLowerExcitedSpinCubeIndices w (Q'.le_of_lt hw) K)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0)
    (fun index => index)
  · exact centralLowerExcitedSpinCubeIndices_nodup hw K
  · exact centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K
  · intro left _ right _ heq
    exact heq
  · intro index _
    exact Q'.le_refl' _
  · intro index hindex
    exact Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hindex)

theorem centralLowerExcitedSpinCubeRayMass_le_one
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw) K ≤ 1 := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeRayMass_le_sectorMass hw K)
    (centralPhysicalFiniteVacuumSectorMass_le_one
      w (Q'.le_of_lt hw) K 0)

theorem centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w hw K ≈
      listQSum
        (fun offset => centralPhysicalFiniteWeight w hw K 0
          (centralLowerExcitedSpinCubeIndex w hw K offset))
        (List.range K) := by
  unfold centralLowerExcitedSpinCubeRayMass
    centralLowerExcitedSpinCubeIndices
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 2. Literal star-flow occurrences -/

def centralLowerExcitedSpinCubePairWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (pair : Nat × Nat) : Q' :=
  centralPhysicalFiniteWeight w hw K 0
      (centralLowerExcitedSpinCubeIndex w hw K pair.1) *
    centralPhysicalFiniteWeight w hw K 0
      (centralLowerExcitedSpinCubeIndex w hw K pair.2)

def centralLowerExcitedSpinCubePairSpokeOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (pair : Nat × Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  let left := centralLowerExcitedSpinCubeIndex w hw K pair.1
  let right := centralLowerExcitedSpinCubeIndex w hw K pair.2
  let load := centralLowerExcitedSpinCubePairWeight w hw K pair * 2
  [((left, 0), load), ((0, right), load)]

def centralLowerExcitedSpinCubeEndpointPairs (K : Nat) :
    List (Nat × Nat) :=
  cartesian (List.range K) (List.range K)

def centralLowerExcitedSpinCubeRayFlowOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralLowerExcitedSpinCubeEndpointPairs K).flatMap
    (centralLowerExcitedSpinCubePairSpokeOccurrences w hw K)

def centralLowerExcitedSpinCubeRayFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeRayFlowOccurrences w hw K)
    source target

private theorem weightedDirectedEdgeLoad_flatMap_eqv_local
    {Class State : Type} [DecidableEq State]
    (classes : List Class)
    (occurrences : Class → List (WeightedDirectedEdgeOccurrence State))
    (source target : State) :
    weightedDirectedEdgeLoad
        (classes.flatMap occurrences) source target ≈
      listQSum
        (fun item => weightedDirectedEdgeLoad
          (occurrences item) source target)
        classes := by
  unfold weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

private theorem listQSum_single_indicator_eqv
    {A : Type} [DecidableEq A]
    (selected : A) (value : A → Q') :
    ∀ items : List A, items.Nodup → selected ∈ items →
      listQSum
          (fun item => if item = selected then value item else 0)
          items ≈ value selected
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : head = selected
      · subst head
        have hselectedTail : selected ∉ tail := hparts.1
        have htailZero : listQSum
            (fun item => if item = selected then value item else 0)
            tail ≈ 0 := by
          exact Q'.eqv_trans _
            (listQSum (fun _ => (0 : Q')) tail) _
            (listQSum_congr_on _ _ tail (fun item hitem => by
              rw [if_neg]
              exact Q'.eqv_refl 0
              intro heq
              exact hselectedTail (heq ▸ hitem)))
            (listQSum_zero tail)
        simp only [listQSum]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have htail : selected ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left
            (fun heq => hhead heq.symm)
        simp only [listQSum, if_neg hhead]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left 0 _ _
            (listQSum_single_indicator_eqv
              selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-! ## 3. Exact load of each oriented spoke -/

private theorem pairSpokeOccurrences_left_load_eqv
    {w : Q'} (hw : (0 : Q') < w) {K a b selected : Nat}
    (ha : a < K) (_hb : b < K) (hselected : selected < K) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubePairSpokeOccurrences
          w (Q'.le_of_lt hw) K (a, b))
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) 0 ≈
      if a = selected then
        centralLowerExcitedSpinCubePairWeight
          w (Q'.le_of_lt hw) K (a, b) * 2
      else 0 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K
  let load := centralLowerExcitedSpinCubePairWeight
    w (Q'.le_of_lt hw) K (a, b) * 2
  have hselectedZero : index selected ≠ 0 :=
    centralLowerExcitedSpinCubeIndex_ne_zero hw hselected
  have hsecond : (0, index b) ≠ (index selected, 0) := by
    intro heq
    have hfirst := congrArg Prod.fst heq
    exact hselectedZero hfirst.symm
  by_cases has : a = selected
  · subst a
    unfold centralLowerExcitedSpinCubePairSpokeOccurrences
      weightedDirectedEdgeLoad weightedDirectedEdgeIndicator listQSum
    dsimp only [index, load]
    simp only [listQSum]
    rw [if_true, if_neg hsecond]
    exact Q'.eqv_trans _ (load + 0) _
      (Q'.add_eqv_congr_left load _ _
        (Q'.eqv_of_eq (Q'.zero_add' 0)))
      (Q'.eqv_of_eq (Q'.add_zero' load))
  · have hindexNe : index a ≠ index selected := by
      intro heq
      exact has (centralLowerExcitedSpinCubeIndex_injective_on
        hw ha hselected heq)
    have hfirst : (index a, 0) ≠ (index selected, 0) := by
      intro heq
      exact hindexNe (congrArg Prod.fst heq)
    unfold centralLowerExcitedSpinCubePairSpokeOccurrences
      weightedDirectedEdgeLoad weightedDirectedEdgeIndicator listQSum
    dsimp only [index, load]
    simp only [listQSum]
    rw [if_neg hfirst, if_neg hsecond, if_neg has]
    exact Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left 0 _ _
        (Q'.eqv_of_eq (Q'.zero_add' 0)))
      (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem pairSpokeOccurrences_right_load_eqv
    {w : Q'} (hw : (0 : Q') < w) {K a b selected : Nat}
    (ha : a < K) (hb : b < K) (hselected : selected < K) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubePairSpokeOccurrences
          w (Q'.le_of_lt hw) K (a, b))
        0 (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) ≈
      if b = selected then
        centralLowerExcitedSpinCubePairWeight
          w (Q'.le_of_lt hw) K (a, b) * 2
      else 0 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K
  let load := centralLowerExcitedSpinCubePairWeight
    w (Q'.le_of_lt hw) K (a, b) * 2
  have haZero : index a ≠ 0 :=
    centralLowerExcitedSpinCubeIndex_ne_zero hw ha
  have hfirst : (index a, 0) ≠ (0, index selected) := by
    intro heq
    exact haZero (congrArg Prod.fst heq)
  by_cases hbs : b = selected
  · subst b
    unfold centralLowerExcitedSpinCubePairSpokeOccurrences
      weightedDirectedEdgeLoad weightedDirectedEdgeIndicator listQSum
    dsimp only [index, load]
    simp only [listQSum]
    rw [if_neg hfirst, if_true]
    exact Q'.eqv_trans _ (0 + load) _
      (Q'.add_eqv_congr_left 0 _ _
        (Q'.eqv_of_eq (Q'.add_zero' load)))
      (Q'.eqv_of_eq (Q'.zero_add' load))
  · have hindexNe : index b ≠ index selected := by
      intro heq
      exact hbs (centralLowerExcitedSpinCubeIndex_injective_on
        hw hb hselected heq)
    have hsecond : (0, index b) ≠ (0, index selected) := by
      intro heq
      exact hindexNe (congrArg Prod.snd heq)
    unfold centralLowerExcitedSpinCubePairSpokeOccurrences
      weightedDirectedEdgeLoad weightedDirectedEdgeIndicator listQSum
    dsimp only [index, load]
    simp only [listQSum]
    rw [if_neg hfirst, if_neg hsecond, if_neg hbs]
    exact Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left 0 _ _
        (Q'.eqv_of_eq (Q'.zero_add' 0)))
      (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem centralLowerExcitedSpinCubeRayFlowLoad_leftSpoke_eqv
    {w : Q'} (hw : (0 : Q') < w) {K selected : Nat}
    (hselected : selected < K) :
    centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) 0 ≈
      (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K selected) *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K) * 2 := by
  let weight : Nat → Q' := fun offset =>
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
  let selectedWeight : Nat → Q' := fun offset =>
    if offset = selected then weight offset * 2 else 0
  have hpaths : centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) 0 ≈
      listQSum
        (fun pair => if pair.1 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0)
        (centralLowerExcitedSpinCubeEndpointPairs K) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair => weightedDirectedEdgeLoad
          (centralLowerExcitedSpinCubePairSpokeOccurrences
            w (Q'.le_of_lt hw) K pair)
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K selected) 0)
        (centralLowerExcitedSpinCubeEndpointPairs K)) _ ?_ ?_
    · unfold centralLowerExcitedSpinCubeRayFlowLoad
        centralLowerExcitedSpinCubeRayFlowOccurrences
      exact weightedDirectedEdgeLoad_flatMap_eqv_local _ _ _ _
    · apply listQSum_congr_on
      intro pair hpair
      have hparts := (mem_cartesian_iff
        (List.range K) (List.range K) pair).mp hpair
      exact pairSpokeOccurrences_left_load_eqv hw
        (List.mem_range.mp hparts.1)
        (List.mem_range.mp hparts.2) hselected
  have hterm : ∀ pair,
      (if pair.1 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0) ≈
        selectedWeight pair.1 * weight pair.2 := by
    intro pair
    by_cases heq : pair.1 = selected
    · rw [if_pos heq]
      unfold selectedWeight centralLowerExcitedSpinCubePairWeight weight
      rw [if_pos heq]
      q_ring
    · rw [if_neg heq]
      unfold selectedWeight
      rw [if_neg heq]
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  have hfactor : listQSum
        (fun pair => if pair.1 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0)
        (centralLowerExcitedSpinCubeEndpointPairs K) ≈
      listQSum selectedWeight (List.range K) *
        listQSum weight (List.range K) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair => selectedWeight pair.1 * weight pair.2)
        (cartesian (List.range K) (List.range K))) _ ?_ ?_
    · unfold centralLowerExcitedSpinCubeEndpointPairs
      exact listQSum_congr hterm _
    · exact listQSum_cartesian_product
        selectedWeight weight (List.range K) (List.range K)
  have hselectedSum : listQSum selectedWeight (List.range K) ≈
      weight selected * 2 := by
    unfold selectedWeight
    exact listQSum_single_indicator_eqv selected
      (fun offset => weight offset * 2) (List.range K)
      (rangeNodupLocal _) (List.mem_range.mpr hselected)
  have hmass := centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
    w (Q'.le_of_lt hw) K
  refine Q'.eqv_trans _ _ _ hpaths
    (Q'.eqv_trans _ _ _ hfactor ?_)
  refine Q'.eqv_trans _
    ((weight selected * 2) *
      centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw) K) _ ?_ ?_
  · exact Q'.eqv_trans _
      ((weight selected * 2) * listQSum weight (List.range K)) _
      (Q'.mul_eqv_congr_right _ _ _ hselectedSum)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hmass))
  · unfold weight
    q_ring

theorem centralLowerExcitedSpinCubeRayFlowLoad_rightSpoke_eqv
    {w : Q'} (hw : (0 : Q') < w) {K selected : Nat}
    (hselected : selected < K) :
    centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) ≈
      (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K selected) *
        centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K) * 2 := by
  let weight : Nat → Q' := fun offset =>
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
  let selectedWeight : Nat → Q' := fun offset =>
    if offset = selected then weight offset * 2 else 0
  have hpaths : centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K selected) ≈
      listQSum
        (fun pair => if pair.2 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0)
        (centralLowerExcitedSpinCubeEndpointPairs K) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair => weightedDirectedEdgeLoad
          (centralLowerExcitedSpinCubePairSpokeOccurrences
            w (Q'.le_of_lt hw) K pair)
          0 (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K selected))
        (centralLowerExcitedSpinCubeEndpointPairs K)) _ ?_ ?_
    · unfold centralLowerExcitedSpinCubeRayFlowLoad
        centralLowerExcitedSpinCubeRayFlowOccurrences
      exact weightedDirectedEdgeLoad_flatMap_eqv_local _ _ _ _
    · apply listQSum_congr_on
      intro pair hpair
      have hparts := (mem_cartesian_iff
        (List.range K) (List.range K) pair).mp hpair
      exact pairSpokeOccurrences_right_load_eqv hw
        (List.mem_range.mp hparts.1)
        (List.mem_range.mp hparts.2) hselected
  have hterm : ∀ pair,
      (if pair.2 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0) ≈
        weight pair.1 * selectedWeight pair.2 := by
    intro pair
    by_cases heq : pair.2 = selected
    · rw [if_pos heq]
      unfold selectedWeight centralLowerExcitedSpinCubePairWeight weight
      rw [if_pos heq]
      q_ring
    · rw [if_neg heq]
      unfold selectedWeight
      rw [if_neg heq]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  have hfactor : listQSum
        (fun pair => if pair.2 = selected then
          centralLowerExcitedSpinCubePairWeight
            w (Q'.le_of_lt hw) K pair * 2 else 0)
        (centralLowerExcitedSpinCubeEndpointPairs K) ≈
      listQSum weight (List.range K) *
        listQSum selectedWeight (List.range K) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pair => weight pair.1 * selectedWeight pair.2)
        (cartesian (List.range K) (List.range K))) _ ?_ ?_
    · unfold centralLowerExcitedSpinCubeEndpointPairs
      exact listQSum_congr hterm _
    · exact listQSum_cartesian_product
        weight selectedWeight (List.range K) (List.range K)
  have hselectedSum : listQSum selectedWeight (List.range K) ≈
      weight selected * 2 := by
    unfold selectedWeight
    exact listQSum_single_indicator_eqv selected
      (fun offset => weight offset * 2) (List.range K)
      (rangeNodupLocal _) (List.mem_range.mpr hselected)
  have hmass := centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
    w (Q'.le_of_lt hw) K
  refine Q'.eqv_trans _ _ _ hpaths
    (Q'.eqv_trans _ _ _ hfactor ?_)
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw) K *
      (weight selected * 2)) _ ?_ ?_
  · exact Q'.eqv_trans _
      (centralLowerExcitedSpinCubeRayMass
          w (Q'.le_of_lt hw) K *
        listQSum selectedWeight (List.range K)) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hmass))
      (Q'.mul_eqv_congr_left _ _ _ hselectedSum)
  · unfold weight
    q_ring

/-! ## 4. Capacity is exactly reduced to vacuum return probability -/

def centralLowerExcitedSpinCubeVacuumReturnProbability
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) : Q' :=
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  Q'.divPos
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 index 0)
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index)
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))

theorem centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) *
        centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset ≈
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 := by
  unfold centralLowerExcitedSpinCubeVacuumReturnProbability
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _)
    (Q'.divPos_mul_eqv _ _ _)

private theorem twice_mul_nonnegative
    (delta : Q') (hdelta : (0 : Q') ≤ delta) :
    (0 : Q') ≤ 2 * delta :=
  Q'.mul_nonneg 2 delta (by decide) hdelta

/-- A return-probability floor pays the entire left-oriented ray-spoke load;
the finite ray mass disappears against its probability upper bound. -/
theorem delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (delta : Q')
    (hdelta : (0 : Q') ≤ delta)
    (hreturn : 2 * delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset) :
    delta * centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 ≤
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) 0 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 index
  let mass := centralLowerExcitedSpinCubeRayMass
    w (Q'.le_of_lt hw) K
  let returnProbability :=
    centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
  have hmass : mass ≤ 1 :=
    centralLowerExcitedSpinCubeRayMass_le_one hw K
  have htwiceMass : (2 * delta) * mass ≤ returnProbability := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      mass 1 (2 * delta) hmass
      (twice_mul_nonnegative delta hdelta)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_one_eqv (2 * delta))) hreturn)
  have hweight0 : (0 : Q') ≤ weight :=
    Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    ((2 * delta) * mass) returnProbability weight
    htwiceMass hweight0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _
      (delta * ((weight * mass) * 2)) _
      (Q'.mul_eqv_congr_left delta _ _
        (centralLowerExcitedSpinCubeRayFlowLoad_leftSpoke_eqv
          hw hoffset))
      (by q_ring)))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
          hw hoffset)))

/-- The same return floor pays the reverse spoke because the physical joint
kernel is symmetric and the reverse load has the same exact scalar value. -/
theorem delta_mul_rightSpokeLoad_le_kernel_of_twice_delta_le_return
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (delta : Q')
    (hdelta : (0 : Q') ≤ delta)
    (hreturn : 2 * delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset) :
    delta * centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) ≤
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 0
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset) := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  have hleft :=
    delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return
      hw hoffset delta hdelta hreturn
  have hloads : centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K 0 index ≈
      centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K index 0 :=
    Q'.eqv_trans _ _ _
      (centralLowerExcitedSpinCubeRayFlowLoad_rightSpoke_eqv
        hw hoffset)
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeRayFlowLoad_leftSpoke_eqv
          hw hoffset))
  have hkernels : centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 0 index ≈
      centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 index 0 := by
    dsimp only [index, centralLowerExcitedSpinCubeIndex]
    unfold centralPhysicalFiniteKernel
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum,
      centralPhysicalFiniteStateAt_spinCubeIndex_eq hw (by omega)]
    exact centralNormalizedPhysicalReflectedKernel_symm
      (zeroEdgeLabelling_mem_bounded_local K (centralLowerFaceIds 0))
      (centralLowerSpinCubeState_mem_centralHalfStates (by omega))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left delta _ _ hloads))
    (Q'.le_trans' _ _ _ hleft
      (Q'.le_of_eqv (Q'.eqv_symm hkernels)))

end YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCubeIndex_injective_on
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCubeIndices_nodup
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCubeRayMass_le_one
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCubeRayFlowLoad_leftSpoke_eqv
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCubeRayFlowLoad_rightSpoke_eqv
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity.delta_mul_rightSpokeLoad_le_kernel_of_twice_delta_le_return
