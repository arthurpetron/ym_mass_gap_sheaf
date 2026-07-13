/-
# Inductive pair-bounced block-cut spines

A `PairedSpine` is a nonempty sequence of open ears whose consecutive
endpoints are shared articulations.  Bouncing every selected ear and
concatenating the walks gives an actual carrier walk.  Structural induction
proves its exact fuel and activity formulas: base edges add by block, paired
interiors add with multiplicity four, and each articulation is counted once.
-/

import YMGap.Continuum.XiExceptionalCrossSpineCarrier

namespace YMGap.Continuum.XiExceptionalPairedSpine

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalCrossSpineCarrier

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- A nonempty endpoint-matched sequence of paired open ears. -/
inductive PairedSpine {alpha : Type} (edge : alpha → alpha → Bool) :
    alpha → alpha → Type
  | one {x y : alpha} (path : PairedPath edge x y) : PairedSpine edge x y
  | cons {x y z : alpha} (path : PairedPath edge x y)
      (rest : PairedSpine edge y z) : PairedSpine edge x z

namespace PairedSpine

variable {alpha : Type} {edge : alpha → alpha → Bool}

def blockCount : {x y : alpha} → PairedSpine edge x y → Nat
  | _, _, .one _ => 1
  | _, _, .cons _ rest => rest.blockCount + 1

def pairCount : {x y : alpha} → PairedSpine edge x y → Nat
  | _, _, .one path => path.pairCount
  | _, _, .cons path rest => path.pairCount + rest.pairCount

def bounceWalk
    (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    {x y : alpha} → PairedSpine edge x y → CWalk edge x y
  | _, _, .one path => path.bounceWalk hsymm
  | _, _, .cons path rest =>
      (path.bounceWalk hsymm).append (rest.bounceWalk hsymm)

/-- Exact additive repeated-ear fuel for an arbitrary consecutive spine. -/
theorem bounceWalk_length
    (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    ∀ {x y : alpha} (spine : PairedSpine edge x y),
      (spine.bounceWalk hsymm).vertices.length =
        spine.blockCount + 1 + 4 * spine.pairCount
  | _, _, .one path => by
      simp only [bounceWalk, blockCount, pairCount]
      rw [PairedPath.bounceWalk_length hsymm path]
  | _, _, .cons path rest => by
      simp only [bounceWalk, blockCount, pairCount]
      have happ := CWalk.append_vertices_length
        (path.bounceWalk hsymm) (rest.bounceWalk hsymm)
      rw [PairedPath.bounceWalk_length hsymm path,
        bounceWalk_length hsymm rest] at happ
      omega

/-! ## Occurrence target packaging -/

variable {L : Lattice} [DecidableEq L.Plaquette]

def occurrenceCarrierCode (Gamma : List (Polymer L))
    {edgeN : Nat → Nat → Bool} {i j : Nat}
    (spine : PairedSpine edgeN i j)
    (hsymm : ∀ x y, edgeN x y = true → edgeN y x = true)
    (background external : OccBitVec Gamma.length) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := i
        chain := occurrenceChainCodeOfWalk (spine.bounceWalk hsymm) background }
    external := external }

theorem occurrenceCarrierCode_mem (Gamma : List (Polymer L))
    {edgeN : Nat → Nat → Bool} {i j : Nat}
    (spine : PairedSpine edgeN i j)
    (hsymm : ∀ x y, edgeN x y = true → edgeN y x = true)
    (background external : OccBitVec Gamma.length)
    (hi : i < Gamma.length)
    (hfuel : spine.blockCount + 1 + 4 * spine.pairCount ≤ Gamma.length)
    (hbound : ∀ k, k ∈ (spine.bounceWalk hsymm).vertices →
      k < Gamma.length) :
    occurrenceCarrierCode Gamma spine hsymm background external ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold occurrenceCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨external, bitVectors_complete external, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨i, occurrenceChainCodeOfWalk (spine.bounceWalk hsymm) background⟩,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨i, occurrenceIndices_complete hi, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk (spine.bounceWalk hsymm) background,
    ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background
    (spine.bounceWalk hsymm) Gamma.length
  · rw [bounceWalk_length hsymm spine]
    exact hfuel
  · exact hbound

/-! ## Exact articulation-normalized activity -/

private theorem polymerIncompatSymm (X Y : Polymer L)
    (h : (!(compatibleB X Y)) = true) : (!(compatibleB Y X)) = true := by
  rw [compatibleB_symm Y X]
  exact h

def activityFormula (w : Q') (label : L.Plaquette → Rep) :
    {X Y : Polymer L} →
      PairedSpine (fun A B : Polymer L => !(compatibleB A B)) X Y → Q'
  | X, Y, .one path =>
      activity w X label *
        (path.interiorActivity w label * path.interiorActivity w label *
          activity w Y label)
  | X, _, .cons path rest =>
      activity w X label *
        (path.interiorActivity w label * path.interiorActivity w label *
          activityFormula w label rest)

/-- Exact activity of an arbitrary bounced spine, with each shared
articulation present only in the recursively following block. -/
theorem bounceWalk_activity_eqv (w : Q') (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (spine : PairedSpine
        (fun A B : Polymer L => !(compatibleB A B)) X Y),
      (spine.bounceWalk polymerIncompatSymm).activityWeight w label ≈
        spine.activityFormula w label
  | _, _, .one path => by
      simp only [bounceWalk, activityFormula]
      exact PairedPath.bounceWalk_activity_eqv path w label
  | _, _, @PairedSpine.cons _ _ X J Y path rest => by
      simp only [bounceWalk, activityFormula]
      refine Q'.eqv_trans _ _ _
        (CWalk.append_activityWeight_eqv w label _ _) ?_
      refine Q'.eqv_trans _
        ((activity w X label *
          (path.interiorActivity w label * path.interiorActivity w label)) *
            activityFormula w label rest) _ ?_ ?_
      · exact YMGap.Continuum.XiPairSwitching.mul_eqv_congr_both
          (PairedPath.bounceWalk_prefixActivity_eqv w label path)
          (bounceWalk_activity_eqv w label rest)
      · ring_qeqv

theorem activityFormula_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (spine : PairedSpine
        (fun A B : Polymer L => !(compatibleB A B)) X Y),
      (0 : Q') ≤ spine.activityFormula w label
  | _, _, .one path => by
      simp only [activityFormula]
      exact Q'.mul_nonneg _ _ (activity_nonneg hw _ label)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (PairedPath.interiorActivity_nonnegative hw label path)
            (PairedPath.interiorActivity_nonnegative hw label path))
          (activity_nonneg hw _ label))
  | _, _, .cons path rest => by
      simp only [activityFormula]
      exact Q'.mul_nonneg _ _ (activity_nonneg hw _ label)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (PairedPath.interiorActivity_nonnegative hw label path)
            (PairedPath.interiorActivity_nonnegative hw label path))
          (activityFormula_nonnegative hw label rest))

#print axioms bounceWalk_length
#print axioms occurrenceCarrierCode_mem
#print axioms bounceWalk_activity_eqv
#print axioms activityFormula_nonnegative

end PairedSpine

end YMGap.Continuum.XiExceptionalPairedSpine
