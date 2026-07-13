/-
# Cross-balanced two-block spine carrier

Two consecutive bounced ears share one articulation.  This file composes
their walks, proves the exact `length(first)+length(second)-1` fuel identity,
and packages the result into the finite occurrence target.  On polymer walks
it also proves the corresponding activity identity with the articulation
counted once, then derives the cross-balanced two-code weight bound.
-/

import YMGap.Continuum.XiExceptionalBlockCutCrossBalance

namespace YMGap.Continuum.XiExceptionalCrossSpineCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiSignLayer
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalBlockCutCrossBalance

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## Walk composition and exact fuel -/

theorem CWalk.append_vertices_length {alpha : Type}
    {edge : alpha → alpha → Bool} :
    ∀ {x y z : alpha} (first : CWalk edge x y) (second : CWalk edge y z),
      (first.append second).vertices.length + 1 =
        first.vertices.length + second.vertices.length
  | _, _, _, .single _, second => by
      simp only [CWalk.append, CWalk.vertices, List.length_cons,
        List.length_nil]
      omega
  | _, _, _, .cons _ rest, second => by
      simp only [CWalk.append, CWalk.vertices, List.length_cons]
      rw [CWalk.append_vertices_length rest second]
      omega

def crossBounceWalk {edge : Nat → Nat → Bool} {i j k : Nat}
    (first : PairedPath edge i j) (second : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    CWalk edge i k :=
  (first.bounceWalk hsymm).append (second.bounceWalk hsymm)

theorem crossBounceWalk_length {edge : Nat → Nat → Bool}
    {i j k : Nat} (first : PairedPath edge i j)
    (second : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    (crossBounceWalk first second hsymm).vertices.length =
      3 + 4 * (first.pairCount + second.pairCount) := by
  have happ := CWalk.append_vertices_length
    (first.bounceWalk hsymm) (second.bounceWalk hsymm)
  rw [PairedPath.bounceWalk_length hsymm first,
    PairedPath.bounceWalk_length hsymm second] at happ
  unfold crossBounceWalk
  omega

/-! ## Occurrence target packaging -/

variable {L : Lattice} [DecidableEq L.Plaquette]

def crossSpineCarrierCode (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j k : Nat}
    (first : PairedPath edge i j) (second : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := i
        chain := occurrenceChainCodeOfWalk
          (crossBounceWalk first second hsymm) background }
    external := external }

theorem crossSpineCarrierCode_mem (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j k : Nat}
    (first : PairedPath edge i j) (second : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length)
    (hi : i < Gamma.length)
    (hfuel : 3 + 4 * (first.pairCount + second.pairCount) ≤
      Gamma.length)
    (hbound : ∀ u, u ∈ (crossBounceWalk first second hsymm).vertices →
      u < Gamma.length) :
    crossSpineCarrierCode Gamma first second hsymm background external ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold crossSpineCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨external, bitVectors_complete external, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨i, occurrenceChainCodeOfWalk
    (crossBounceWalk first second hsymm) background⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨i, occurrenceIndices_complete hi, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk
    (crossBounceWalk first second hsymm) background, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background
    (crossBounceWalk first second hsymm) Gamma.length
  · rw [crossBounceWalk_length first second hsymm]
    exact hfuel
  · exact hbound

def crossSpineBlock (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j k : Nat}
    (firstA firstB : PairedPath edge i j)
    (secondA secondB : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length) :
    List (OccCarrierXiCodeAt Gamma) :=
  [crossSpineCarrierCode Gamma firstA secondB hsymm background external,
    crossSpineCarrierCode Gamma firstB secondA hsymm background external]

theorem crossSpineBlock_length (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j k : Nat}
    (firstA firstB : PairedPath edge i j)
    (secondA secondB : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length) :
    (crossSpineBlock Gamma firstA firstB secondA secondB hsymm
      background external).length = 2 := rfl

theorem crossSpineBlock_nodup (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j k : Nat}
    (firstA firstB : PairedPath edge i j)
    (secondA secondB : PairedPath edge j k)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length)
    (hne : crossSpineCarrierCode Gamma firstA secondB hsymm
        background external ≠
      crossSpineCarrierCode Gamma firstB secondA hsymm background external) :
    (crossSpineBlock Gamma firstA firstB secondA secondB hsymm
      background external).Nodup := by
  simp [crossSpineBlock, hne]

/-! ## Activity normalization across the shared articulation -/

def prefixActivityWeight (w : Q') (label : L.Plaquette → Rep) :
    {X Y : Polymer L} →
      CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y → Q'
  | _, _, .single _ => 1
  | X, _, .cons _ rest =>
      activity w X label * prefixActivityWeight w label rest

private theorem polymerIncompatSymm (X Y : Polymer L)
    (h : (!(compatibleB X Y)) = true) : (!(compatibleB Y X)) = true := by
  rw [compatibleB_symm Y X]
  exact h

theorem CWalk.append_activityWeight_eqv (w : Q')
    (label : L.Plaquette → Rep) :
    ∀ {X Y Z : Polymer L}
      (first : CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y)
      (second : CWalk (fun A B : Polymer L => !(compatibleB A B)) Y Z),
      (first.append second).activityWeight w label ≈
        prefixActivityWeight w label first * second.activityWeight w label
  | _, _, _, .single _, second => by
      simp only [CWalk.append, prefixActivityWeight]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | _, _, _, .cons _ rest, second => by
      simp only [CWalk.append, CWalk.activityWeight,
        prefixActivityWeight]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (CWalk.append_activityWeight_eqv w label rest second)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem PairedPath.bounceWalk_prefixActivity_eqv
    (w : Q') (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (path : PairedPath
        (fun A B : Polymer L => !(compatibleB A B)) X Y),
      prefixActivityWeight w label (path.bounceWalk polymerIncompatSymm) ≈
        activity w X label *
          (path.interiorActivity w label * path.interiorActivity w label)
  | _, _, .last _ => by
      simp only [PairedPath.bounceWalk, prefixActivityWeight,
        PairedPath.interiorActivity]
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.one_mul_eqv 1))
  | _, _, @PairedPath.pair _ _ X A B Y hXA hAB rest => by
      simp only [PairedPath.bounceWalk, prefixActivityWeight,
        PairedPath.interiorActivity]
      refine Q'.eqv_trans _
        (activity w X label * (activity w A label *
          (activity w B label * (activity w A label *
            (activity w B label *
              (rest.interiorActivity w label *
                rest.interiorActivity w label)))))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _
                (PairedPath.bounceWalk_prefixActivity_eqv w label rest))))
      · ring_qeqv

def polymerCrossBounceWalk
    {X J Y : Polymer L}
    (first : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) X J)
    (second : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) J Y) :=
  (first.bounceWalk polymerIncompatSymm).append
    (second.bounceWalk polymerIncompatSymm)

theorem polymerCrossBounceWalk_activity_eqv (w : Q')
    (label : L.Plaquette → Rep)
    {X J Y : Polymer L}
    (first : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) X J)
    (second : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) J Y) :
    (polymerCrossBounceWalk first second).activityWeight w label ≈
      activity w X label *
        (first.interiorActivity w label * first.interiorActivity w label *
          (activity w J label *
            (second.interiorActivity w label *
              second.interiorActivity w label * activity w Y label))) := by
  unfold polymerCrossBounceWalk
  refine Q'.eqv_trans _ _ _
    (CWalk.append_activityWeight_eqv w label _ _) ?_
  refine Q'.eqv_trans _
    ((activity w X label *
        (first.interiorActivity w label * first.interiorActivity w label)) *
      (activity w J label *
        (second.interiorActivity w label * second.interiorActivity w label *
          activity w Y label))) _ ?_ ?_
  · exact YMGap.Continuum.XiPairSwitching.mul_eqv_congr_both
      (PairedPath.bounceWalk_prefixActivity_eqv w label first)
      (PairedPath.bounceWalk_activity_eqv second w label)
  · ring_qeqv

/-- The two cross-spine target weights dominate the product of all four arm
interior weights, with the three spine vertices counted exactly once. -/
theorem crossSpine_two_code_weight_bound {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep)
    {X J Y : Polymer L}
    (firstA firstB : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) X J)
    (secondA secondB : PairedPath
      (fun A B : Polymer L => !(compatibleB A B)) J Y) :
    (activity w X label * activity w J label * activity w Y label) *
        ((firstA.interiorActivity w label *
            firstB.interiorActivity w label) *
          (secondA.interiorActivity w label *
            secondB.interiorActivity w label)) ≤
      (polymerCrossBounceWalk firstA secondB).activityWeight w label +
        (polymerCrossBounceWalk firstB secondA).activityWeight w label := by
  let C := activity w X label * activity w J label * activity w Y label
  let A₁ := firstA.interiorActivity w label
  let B₁ := firstB.interiorActivity w label
  let A₂ := secondA.interiorActivity w label
  let B₂ := secondB.interiorActivity w label
  have hC : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (activity_nonneg hw X label)
      (activity_nonneg hw J label))
    (activity_nonneg hw Y label)
  have hA₁ := PairedPath.interiorActivity_nonnegative hw label firstA
  have hB₁ := PairedPath.interiorActivity_nonnegative hw label firstB
  have hA₂ := PairedPath.interiorActivity_nonnegative hw label secondA
  have hB₂ := PairedPath.interiorActivity_nonnegative hw label secondB
  have hcross := cross_balanced_pair_weight_bound hA₁ hB₁ hA₂ hB₂
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C hcross hC
  have htargets :
      (polymerCrossBounceWalk firstA secondB).activityWeight w label +
          (polymerCrossBounceWalk firstB secondA).activityWeight w label ≈
        C * ((A₁ * B₂) * (A₁ * B₂) +
          (B₁ * A₂) * (B₁ * A₂)) := by
    refine Q'.eqv_trans _ _ _
      (YMGap.Continuum.AbstractPolymerXi.add_eqv_congr_both
        _ _ _ _
        (polymerCrossBounceWalk_activity_eqv w label firstA secondB)
        (polymerCrossBounceWalk_activity_eqv w label firstB secondA)) ?_
    unfold C A₁ B₁ A₂ B₂
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv htargets)

#print axioms CWalk.append_vertices_length
#print axioms crossBounceWalk_length
#print axioms crossSpineCarrierCode_mem
#print axioms crossSpineBlock_length
#print axioms crossSpineBlock_nodup
#print axioms CWalk.append_activityWeight_eqv
#print axioms PairedPath.bounceWalk_prefixActivity_eqv
#print axioms polymerCrossBounceWalk_activity_eqv
#print axioms crossSpine_two_code_weight_bound

end YMGap.Continuum.XiExceptionalCrossSpineCarrier
