/-
# Exact merged-external carrier for compatible residual unions

The two path-cleared source residuals need not occupy the two carrier mask
slots separately.  When their occurrence masks are disjoint and their union
is an admissible compatible family, both can be moved into the external slot
and the terminal background can be empty.  The canonical path is unchanged,
so this ordinary carrier has exactly the exceptional source weight even when
both residuals are individually unsafe for the path.

This closes a genuine subregion of the both-sides-unsafe source.  It does not
claim global injectivity: the merged mask forgets the left/right colouring,
so the remaining global step is a fibre allocation keyed by the already
injective trace-plus-right datum.
-/

import YMGap.Continuum.XiExceptionalTraceRightInvariant

namespace YMGap.Continuum.XiExceptionalMergedResidualCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit
open YMGap.Continuum.XiExceptionalTraceRightInvariant

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Disjoint occurrence union and its exact activity -/

def unionBits : {n : Nat} → OccBitVec n → OccBitVec n → OccBitVec n
  | 0, .nil, .nil => .nil
  | _ + 1, .cons a as, .cons b bs => .cons (a || b) (unionBits as bs)

theorem unionBits_at : ∀ {n : Nat} (left right : OccBitVec n) (i : Nat),
    (unionBits left right).at i = (left.at i || right.at i)
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons _ _, .cons _ _, 0 => rfl
  | _ + 1, .cons _ left, .cons _ right, i + 1 =>
      unionBits_at left right i

def DisjointBits {n : Nat} (left right : OccBitVec n) : Prop :=
  ∀ i, left.at i = true → right.at i = false

theorem disjointBits_tail {n : Nat} {a b : Bool}
    {left right : OccBitVec n}
    (h : DisjointBits (.cons a left) (.cons b right)) :
    DisjointBits left right := by
  intro i hi
  exact h (i + 1) hi

theorem disjointBits_heads_not_both {n : Nat} {a b : Bool}
    {left right : OccBitVec n}
    (h : DisjointBits (.cons a left) (.cons b right))
    (ha : a = true) : b = false := by
  exact h 0 ha

/-- With no duplicated selected occurrence, merging the two occurrence masks
multiplies their family activities exactly. -/
theorem familyActivity_unionBits_eqv :
    ∀ (w : Q') (Gamma : List (Polymer L))
      (left right : OccBitVec Gamma.length)
      (label : L.Plaquette → Rep),
      DisjointBits left right →
      familyActivity w (selectByBits Gamma (unionBits left right)) label ≈
        familyActivity w (selectByBits Gamma left) label *
          familyActivity w (selectByBits Gamma right) label
  | _, [], .nil, .nil, _, _ =>
      Q'.eqv_symm (Q'.one_mul_eqv 1)
  | w, X :: Gamma, .cons false left, .cons false right, label, h =>
      familyActivity_unionBits_eqv w Gamma left right label
        (disjointBits_tail h)
  | w, X :: Gamma, .cons false left, .cons true right, label, h => by
      have ih := familyActivity_unionBits_eqv w Gamma left right label
        (disjointBits_tail h)
      simp only [unionBits, Bool.false_or, selectByBits_cons_true,
        selectByBits_cons_false, familyActivity_cons]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (activity w X label) _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv
          (activity w X label)
          (familyActivity w (selectByBits Gamma left) label)
          (familyActivity w (selectByBits Gamma right) label))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (activity w X label)
            (familyActivity w (selectByBits Gamma left) label))) ?_
      exact Q'.mul_assoc_eqv
        (familyActivity w (selectByBits Gamma left) label)
        (activity w X label)
        (familyActivity w (selectByBits Gamma right) label)
  | w, X :: Gamma, .cons true left, .cons false right, label, h => by
      have ih := familyActivity_unionBits_eqv w Gamma left right label
        (disjointBits_tail h)
      simp only [unionBits, Bool.true_or, selectByBits_cons_true,
        selectByBits_cons_false, familyActivity_cons]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (activity w X label) _ _ ih)
        (Q'.eqv_symm (Q'.mul_assoc_eqv
          (activity w X label)
          (familyActivity w (selectByBits Gamma left) label)
          (familyActivity w (selectByBits Gamma right) label)))
  | w, X :: Gamma, .cons true left, .cons true right, label, h => by
      have hfalse : true = false := disjointBits_heads_not_both h rfl
      cases hfalse

/-! ## The merged ordinary carrier -/

def mergedResidualBits
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  unionBits (leftPathResidual Gamma qP b1 b2 entry)
    (rightPathResidual Gamma qP b1 b2 entry)

def mergedResidualCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (emptyOccurrenceBits Gamma)
    (mergedResidualBits Gamma qP b1 b2 entry)

theorem mergedResidualCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    mergedResidualCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry _ _

/-- Local exact payment for the compatible, occurrence-disjoint merged
residual region.  Neither residual is required to be path-safe. -/
theorem mergedResidualCarrierCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hdisjoint : DisjointBits
      (leftPathResidual Gamma qP b1 b2 entry)
      (rightPathResidual Gamma qP b1 b2 entry))
    (hcompatible : familyCompatibleB
      (selectByBits Gamma (mergedResidualBits Gamma qP b1 b2 entry)) = true)
    (hq : (selectByBits Gamma
      (mergedResidualBits Gamma qP b1 b2 entry)).all qP = true) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (mergedResidualCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let left := leftPathResidual Gamma qP b1 b2 entry
  let right := rightPathResidual Gamma qP b1 b2 entry
  let merged := mergedResidualBits Gamma qP b1 b2 entry
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hcarrier := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry (emptyOccurrenceBits Gamma) merged
    (by rw [select_emptyOccurrenceBits]; rfl)
    (by rw [select_emptyOccurrenceBits]; rfl)
    (by
      dsimp only
      intro X hX T hT
      rw [select_emptyOccurrenceBits] at hT
      cases hT)
    (by simpa [merged] using hcompatible)
    (by simpa [merged] using hq)
  have hunion : familyActivity w (selectByBits Gamma merged) label ≈
      familyActivity w (selectByBits Gamma left) label *
        familyActivity w (selectByBits Gamma right) label := by
    exact familyActivity_unionBits_eqv w Gamma left right label (by
      simpa [left, right] using hdisjoint)
  have hsource := occurrencePairWeight_eqv_original_path_residuals
    w qP b1 b2 Gamma label entry
  dsimp only at hcarrier hsource
  rw [select_emptyOccurrenceBits] at hcarrier
  simp only [familyActivity_nil] at hcarrier
  have hcarrierReduced :
      occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
          (mergedResidualCarrierCode Gamma qP b1 b2 entry) ≈
        path.polymerWalk.activityWeight w label *
          familyActivity w (selectByBits Gamma merged) label := by
    exact Q'.eqv_trans _ _ _ hcarrier
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_one_eqv
          (path.polymerWalk.activityWeight w label)))
  exact Q'.eqv_trans _ _ _ hcarrierReduced
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (path.polymerWalk.activityWeight w label) _ _ hunion)
      (Q'.eqv_symm hsource))

/-! ## A genuine both-sides-unsafe member of the merged region -/

namespace BothUnsafeWitness

abbrev TL := toyLattice

instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def x : TL.Plaquette := (0, 0)
def a : TL.Plaquette := (1, 0)
def b : TL.Plaquette := (2, 0)
def A : Polymer TL := [x, a]
def B : Polymer TL := [x, b]
def C : Polymer TL := [a]
def D : Polymer TL := [b]
def Gamma : List (Polymer TL) := [A, B, C, D]
def qAll : Polymer TL → Bool := fun _ => true
def markA : Polymer TL → Bool := fun X => decide (X = A)
def badB : Polymer TL → Bool := fun X => decide (X = B)
def labelOne : TL.Plaquette → Rep := fun _ => 1
def half : Q' := Q'.mkPos 1 2 (by decide)
def oneOver4096 : Q' := Q'.mkPos 1 4096 (by decide)

def bits4 (x0 x1 x2 x3 : Bool) : OccBitVec 4 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 .nil)))

def pair : MaskPair Gamma.length :=
  (bits4 false true true false, bits4 true false false true)

theorem pair_mem : pair ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markA badB := ⟨pair, pair_mem⟩

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {u v : alpha} (walk : CWalk edge u v), v ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badB (polyAt Gamma i) = true) : i = 1 := by
  have hi4 : i < 4 := by simpa [Gamma] using hi
  have hne0 : i ≠ 0 := by intro h; subst i; cases hbad
  have hne2 : i ≠ 2 := by intro h; subst i; cases hbad
  have hne3 : i ≠ 3 := by intro h; subst i; cases hbad
  omega

private theorem branched_direct_walk_vertices
    {edge : Nat → Nat → Bool} {start finish : Nat}
    (walk : CWalk edge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup)
    (hfirst : ∀ j, edge 0 j = true → j = 1 ∨ j = 2)
    (hsecond : ∀ j, edge 2 j = true → j = 0) :
    walk.vertices = [0, 1] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      rcases hfirst next hedge with rfl | rfl
      · cases rest with
        | single _ => rfl
        | @cons _ next2 _ hedge2 tail =>
            have hpNodup := List.nodup_cons.mp hnodup
            have htailNodup := List.nodup_cons.mp hpNodup.2
            exact absurd (CWalk.end_mem_vertices tail) htailNodup.1
      · cases rest with
        | @cons _ next2 _ hedge2 tail =>
            have hnext2 := hsecond next2 hedge2
            subst next2
            have hpNodup := List.nodup_cons.mp hnodup
            exact absurd
              (List.mem_cons_of_mem 2 (CWalk.start_mem_vertices tail))
              hpNodup.1

private theorem path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
  let path := sourceExceptionalPath Gamma qAll markA badB pair facts
  have hstart : exceptionalMarkedIndex Gamma markA badB pair = 0 := by rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma badB) path.seed_true
  have hfinish : path.seed = 1 := badB_polyAt_index hp.1 hp.2.2.2
  apply branched_direct_walk_vertices path.indexWalk hstart hfinish
    path.index_nodup
  · intro j hedge
    have hj := (disagreementEdge_bounds Gamma.length
      (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2) hedge).2
    have hj4 : j < 4 := by simpa [Gamma] using hj
    have hj0 : j ≠ 0 := by intro h; subst j; cases hedge
    have hj3 : j ≠ 3 := by intro h; subst j; cases hedge
    omega
  · intro j hedge
    have hj := (disagreementEdge_bounds Gamma.length
      (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2) hedge).2
    have hj4 : j < 4 := by simpa [Gamma] using hj
    have hj1 : j ≠ 1 := by intro h; subst j; cases hedge
    have hj2 : j ≠ 2 := by intro h; subst j; cases hedge
    have hj3 : j ≠ 3 := by intro h; subst j; cases hedge
    omega

private theorem entry_path_vertices :
    (sourceExceptionalPath Gamma qAll markA badB entry.1
      (exceptionalSourceFactsOfMem Gamma qAll markA badB entry.1
        entry.2)).indexWalk.vertices = [0, 1] := by
  simpa [entry] using path_vertices

theorem left_residual :
    leftPathResidual Gamma qAll markA badB entry =
      bits4 false false true false := by
  unfold leftPathResidual entry
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pair
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pair
          pair_mem)).indexWalk.vertices)
    pair.1 = bits4 false false true false
  rw [path_vertices]
  rfl

theorem right_residual :
    rightPathResidual Gamma qAll markA badB entry =
      bits4 false false false true := by
  unfold rightPathResidual entry
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pair
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pair
          pair_mem)).indexWalk.vertices)
    pair.2 = bits4 false false false true
  rw [path_vertices]
  rfl

theorem entry_both_sides_unsafe :
    entry ∈ bothSidesPathUnsafeSource Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  constructor
  · exact List.mem_attach _ entry
  · unfold twoSidedCoveredB leftResidualPathSafeB rightResidualPathSafeB
    dsimp only
    rw [left_residual, right_residual, entry_path_vertices]
    rfl

theorem merged_disjoint : DisjointBits
    (leftPathResidual Gamma qAll markA badB entry)
    (rightPathResidual Gamma qAll markA badB entry) := by
  intro i hi
  have hi4 : i < 4 := by
    by_cases hlt : i < 4
    · exact hlt
    · have hge : 4 ≤ i := by omega
      have hout := bitVec_at_false_of_ge
        (leftPathResidual Gamma qAll markA badB entry) i hge
      rw [hi] at hout
      cases hout
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rw [left_residual] at hi
  rw [right_residual]
  rcases hiCases with rfl | rfl | rfl | rfl
  · cases hi
  · cases hi
  · rfl
  · cases hi

theorem merged_compatible : familyCompatibleB
    (selectByBits Gamma
      (mergedResidualBits Gamma qAll markA badB entry)) = true := by
  rw [mergedResidualBits, left_residual, right_residual]
  rfl

theorem merged_q : (selectByBits Gamma
    (mergedResidualBits Gamma qAll markA badB entry)).all qAll = true := by
  rw [mergedResidualBits, left_residual, right_residual]
  rfl

theorem source_weight_exact :
    occurrencePairWeight half qAll markA badB Gamma labelOne pair ≈
      oneOver4096 := by
  decide

theorem merged_carrier_weight_exact :
    occurrenceCarrierXiCodeWeight half qAll markA badB Gamma labelOne
        (mergedResidualCarrierCode Gamma qAll markA badB entry) ≈
      oneOver4096 := by
  exact Q'.eqv_trans _ _ _
    (mergedResidualCarrierCode_weight_eqv_source half qAll markA badB
      Gamma labelOne entry merged_disjoint merged_compatible merged_q)
    source_weight_exact

end BothUnsafeWitness

#print axioms unionBits_at
#print axioms familyActivity_unionBits_eqv
#print axioms mergedResidualCarrierCode_mem
#print axioms mergedResidualCarrierCode_weight_eqv_source
#print axioms BothUnsafeWitness.pair_mem
#print axioms BothUnsafeWitness.entry_both_sides_unsafe
#print axioms BothUnsafeWitness.merged_carrier_weight_exact

end YMGap.Continuum.XiExceptionalMergedResidualCarrier
