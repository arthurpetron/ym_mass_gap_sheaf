/-
# Residual zero fence for the mark-pruned branch packing

Clearing the marked self-bit removes the first normalization failure, but a
terminal background is tested against every earlier path vertex.  This file
proves the exact remaining obstruction: any retained switched-left branch
incompatible with a path vertex still forces the packed carrier term to zero.
-/

import YMGap.Continuum.XiExceptionalMarkedPrunedPacking

namespace YMGap.Continuum.XiExceptionalMarkedPrunedFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalMarkedPrunedPacking

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A path/background incompatibility forces zero -/

theorem occurrenceWalkWeight_eqv_zero_of_path_background_failure
    (w : Q') (qP b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec Gamma.length)
    (bg : Polymer L → Bool) (T : Polymer L)
    (hT : T ∈ selectByBits Gamma background)
    (hfailure : bg T = false ∨
      ∃ k, k ∈ walk.vertices ∧ compatibleB (polyAt Gamma k) T = false) :
    chainCodeWeight w qP b2 Gamma label (polyAt Gamma i) bg
        (eraseOccChainCode Gamma
          (occurrenceChainCodeOfWalk walk background)) ≈ 0 := by
  induction walk generalizing bg with
  | single i =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      cases hgate : qP (polyAt Gamma i) && b2 (polyAt Gamma i) with
      | false => exact Q'.eqv_refl 0
      | true =>
          simp only [hgate, if_true]
          have hfail : bg T = false ∨ compatibleB (polyAt Gamma i) T = false := by
            rcases hfailure with hbg | ⟨k, hk, hcompat⟩
            · exact Or.inl hbg
            · rw [List.mem_singleton.mp hk] at hcompat
              exact Or.inr hcompat
          have hall : (selectByBits Gamma background).all
              (fun U => (qP U && bg U) &&
                compatibleB (polyAt Gamma i) U) = false := by
            cases h : (selectByBits Gamma background).all
                (fun U => (qP U && bg U) &&
                  compatibleB (polyAt Gamma i) U) with
            | false => rfl
            | true =>
                have hbad := List.all_eq_true.mp h T hT
                rcases hfail with hbg | hcompat <;> simp_all
          unfold admissibleFamilyWeight
          rw [hall]
          exact Q'.mul_zero_eqv _
  | @cons i k j hedge rest ih =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      rw [CWalk.start_eq]
      cases hgate : qP (polyAt Gamma k) &&
          !(compatibleB (polyAt Gamma i) (polyAt Gamma k)) with
      | false =>
          simp only [hgate, Bool.false_eq_true, if_false]
          exact Q'.mul_zero_eqv _
      | true =>
          simp only [hgate, if_true]
          let nextBg := fun U => bg U && compatibleB (polyAt Gamma i) U
          have hfailureRest : nextBg T = false ∨
              ∃ m, m ∈ rest.vertices ∧
                compatibleB (polyAt Gamma m) T = false := by
            rcases hfailure with hbg | ⟨m, hm, hcompat⟩
            · left
              simp [nextBg, hbg]
            · rcases List.mem_cons.mp hm with hmi | hmrest
              · subst m
                left
                simp [nextBg, hcompat]
              · right
                exact ⟨m, hmrest, hcompat⟩
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (ih nextBg hfailureRest)) ?_
          exact Q'.mul_zero_eqv _

/-! ## 2. Specialization to the mark-pruned packing -/

theorem exceptionalMarkedPrunedCarrierCode_weight_eqv_zero_of_witness
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (T : Polymer L)
    (hT : T ∈ selectByBits Gamma
      (clearOccurrenceBit (switchedBranchCode Gamma b2 entry.1).1
        (exceptionalMarkedIndex Gamma b1 b2 entry.1)))
    (hbad : ∃ k,
      k ∈ (sourceExceptionalPath Gamma qP b1 b2 entry.1
        (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1
          entry.2)).indexWalk.vertices ∧
      compatibleB (polyAt Gamma k) T = false) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalMarkedPrunedCarrierCode Gamma qP b1 b2 entry) ≈ 0 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let marked := exceptionalMarkedIndex Gamma b1 b2 pair
  let background := clearOccurrenceBit switched.1 marked
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hq : qP (polyAt Gamma marked) = true :=
    facts.right_q marked facts.marked_lt facts.marked_right_true
  have hhead : (qP (polyAt Gamma marked) && b1 (polyAt Gamma marked)) = true :=
    (Bool.and_eq_true _ _).mpr ⟨hq, facts.marked_b1⟩
  have hchain := occurrenceWalkWeight_eqv_zero_of_path_background_failure
    w qP b2 Gamma label path.indexWalk background (fun _ => true) T hT
      (Or.inr hbad)
  change carrierXiCodeWeight w qP b1 b2 Gamma label
    ((polyAt Gamma marked,
        eraseOccChainCode Gamma
          (occurrenceChainCodeOfWalk path.indexWalk background)),
      selectByBits Gamma switched.2) ≈ 0
  unfold carrierXiCodeWeight carrierCodeWeight
  simp only [Prod.fst, Prod.snd]
  rw [if_pos hhead]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hchain) ?_
  exact Q'.zero_mul_eqv _

/-! ## 3. The three-polymer branch witness still vanishes -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def C : Polymer TL := [p1]
private def Gamma3 : List (Polymer TL) := [A, B, C]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)
private def label0 : TL.Plaquette → Rep := fun _ => 0
private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))
private def pairBranch : MaskPair Gamma3.length :=
  (bits3 false true false, bits3 true false true)

theorem pairBranch_mem :
    pairBranch ∈ exceptionalSourceCodes Gamma3 qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBranch, ?_⟩
  rfl

private def entryBranch : ExceptionalSourceEntry Gamma3 qAll markA badB :=
  ⟨pairBranch, pairBranch_mem⟩

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma3.length)
    (hbad : badB (polyAt Gamma3 i) = true) : i = 1 := by
  have hi3 : i < 3 := by simpa [Gamma3] using hi
  have hne0 : i ≠ 0 := by
    intro h
    subst i
    cases hbad
  have hne2 : i ≠ 2 := by
    intro h
    subst i
    cases hbad
  omega

theorem marked_pruned_branch_background_contains_C :
    C ∈ selectByBits Gamma3
      (clearOccurrenceBit (switchedBranchCode Gamma3 badB pairBranch).1
        (exceptionalMarkedIndex Gamma3 markA badB pairBranch)) := by
  apply selectByBits_mem_of_at_true Gamma3 _ 2
  · simp [Gamma3]
  · rfl

theorem marked_pruned_branch_has_path_conflict :
    ∃ k,
      k ∈ (sourceExceptionalPath Gamma3 qAll markA badB pairBranch
        (exceptionalSourceFactsOfMem Gamma3 qAll markA badB pairBranch
          pairBranch_mem)).indexWalk.vertices ∧
      compatibleB (polyAt Gamma3 k) C = false := by
  let facts := exceptionalSourceFactsOfMem Gamma3 qAll markA badB
    pairBranch pairBranch_mem
  let path := sourceExceptionalPath Gamma3 qAll markA badB pairBranch facts
  have hp := forwardSeed_parts Gamma3.length
    (bitMask pairBranch.1) (bitMask pairBranch.2)
    (predAt Gamma3 badB) path.seed_true
  have hseed : path.seed = 1 := badB_polyAt_index hp.1 hp.2.2.2
  refine ⟨path.seed, CWalk.end_mem_vertices path.indexWalk, ?_⟩
  rw [hseed]
  rfl

theorem marked_pruned_branch_carrier_weight_eqv_zero :
    occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma3 label0
        (exceptionalMarkedPrunedCarrierCode Gamma3 qAll markA badB
          entryBranch) ≈ 0 :=
  exceptionalMarkedPrunedCarrierCode_weight_eqv_zero_of_witness
    1 qAll markA badB Gamma3 label0 entryBranch C
      marked_pruned_branch_background_contains_C
      marked_pruned_branch_has_path_conflict

#print axioms occurrenceWalkWeight_eqv_zero_of_path_background_failure
#print axioms exceptionalMarkedPrunedCarrierCode_weight_eqv_zero_of_witness
#print axioms pairBranch_mem
#print axioms marked_pruned_branch_background_contains_C
#print axioms marked_pruned_branch_has_path_conflict
#print axioms marked_pruned_branch_carrier_weight_eqv_zero

end YMGap.Continuum.XiExceptionalMarkedPrunedFence
