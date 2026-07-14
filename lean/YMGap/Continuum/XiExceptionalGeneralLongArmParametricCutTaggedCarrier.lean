/-
# Parametric cut-tagged carriers for a broken long arm

A non-full Boolean path has a canonical first missing position.  The data
below keeps that cut as an explicit owner tag, writes the selected prefix
and the remaining suffix as two components, and colors those components
with opposite alternating phases.  The terminal and external masks recover
the source exactly and never overlap.

Unlike the fixed C12 truth table, every construction in this file is
parametric in the cut and suffix length.  The final section proves the exact
activity factorization for an arbitrary `Nat -> Q'` assignment.  Thus the
singleton cut-tagged block pays its source algebraically; a geometric use of
the substrate only has to realize these two masks as an admissible occurrence
carrier.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveBreakNecessity

namespace YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalWeightedInjection

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## A canonical first-cut source key -/

/-- A broken path consists of a full selected prefix, its first missing
vertex, and the unrestricted suffix after that cut. -/
structure CutPattern where
  cut : Nat
  suffix : List Bool
deriving DecidableEq

def CutPattern.leftBits (p : CutPattern) : List Bool :=
  List.replicate p.cut true

def CutPattern.sourceBits (p : CutPattern) : List Bool :=
  p.leftBits ++ false :: p.suffix

def CutPattern.pathLength (p : CutPattern) : Nat :=
  p.cut + 1 + p.suffix.length

theorem CutPattern.leftBits_length (p : CutPattern) :
    p.leftBits.length = p.cut := by
  simp [CutPattern.leftBits]

theorem CutPattern.sourceBits_length (p : CutPattern) :
    p.sourceBits.length = p.pathLength := by
  simp [CutPattern.sourceBits, CutPattern.pathLength,
    CutPattern.leftBits]
  omega

theorem CutPattern.cut_lt_pathLength (p : CutPattern) :
    p.cut < p.pathLength := by
  unfold CutPattern.pathLength
  omega

/-- Constructively find the first missing path occurrence. -/
def firstCut : List Bool → Option CutPattern
  | [] => none
  | false :: suffix => some ⟨0, suffix⟩
  | true :: bits =>
      match firstCut bits with
      | none => none
      | some p => some ⟨p.cut + 1, p.suffix⟩

theorem firstCut_source (cut : Nat) (suffix : List Bool) :
    firstCut (List.replicate cut true ++ false :: suffix) =
      some ⟨cut, suffix⟩ := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, firstCut, ih]

theorem firstCut_sourceBits (p : CutPattern) :
    firstCut p.sourceBits = some p := by
  cases p with
  | mk cut suffix => exact firstCut_source cut suffix

theorem firstCut_some_reconstruct : ∀ {bits : List Bool} {p : CutPattern},
    firstCut bits = some p → p.sourceBits = bits
  | [], _, h => by cases h
  | false :: bits, p, h => by
      simp only [firstCut, Option.some.injEq] at h
      subst p
      rfl
  | true :: bits, p, h => by
      cases hcut : firstCut bits with
      | none => simp [firstCut, hcut] at h
      | some q =>
          simp only [firstCut, hcut, Option.some.injEq] at h
          subst p
          have ih := firstCut_some_reconstruct hcut
          simp only [CutPattern.sourceBits, CutPattern.leftBits,
            List.replicate_succ, List.cons_append]
          rw [← ih]
          rfl

theorem firstCut_none_all_true : ∀ {bits : List Bool},
    firstCut bits = none → bits = List.replicate bits.length true
  | [], _ => rfl
  | false :: _, h => by cases h
  | true :: bits, h => by
      cases hcut : firstCut bits with
      | none =>
          have ih := firstCut_none_all_true hcut
          simp only [List.length_cons, List.replicate_succ]
          exact congrArg (List.cons true) ih
      | some _ => simp [firstCut, hcut] at h

/-- Every non-full finite path has a canonical cut pattern, independently of
its length. -/
theorem firstCut_complete (bits : List Bool)
    (hnfull : bits ≠ List.replicate bits.length true) :
    ∃ p, firstCut bits = some p ∧ p.sourceBits = bits := by
  cases hcut : firstCut bits with
  | none => exact False.elim (hnfull (firstCut_none_all_true hcut))
  | some p => exact ⟨p, rfl, firstCut_some_reconstruct hcut⟩

/-! ## Reset-alternating component masks -/

/-- Split a selected mask into terminal and external layers, toggling the
terminal phase once at each path position. -/
def alternatingMasks : Bool → List Bool → List Bool × List Bool
  | _, [] => ([], [])
  | terminalPhase, b :: bs =>
      let tail := alternatingMasks (!terminalPhase) bs
      ((b && terminalPhase) :: tail.1,
        (b && !terminalPhase) :: tail.2)

/-- Pointwise union, truncated only when one input ends.  All uses below
have equal-length masks. -/
def mergeMasks : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a || b) :: mergeMasks as bs
  | _, _ => []

/-- Pointwise overlap, with the same equal-length convention. -/
def overlapMasks : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a && b) :: overlapMasks as bs
  | _, _ => []

theorem alternatingMasks_fst_length (phase : Bool) : ∀ bits,
    (alternatingMasks phase bits).1.length = bits.length
  | [] => rfl
  | _ :: bits => by
      simp [alternatingMasks, alternatingMasks_fst_length (!phase) bits]

theorem alternatingMasks_snd_length (phase : Bool) : ∀ bits,
    (alternatingMasks phase bits).2.length = bits.length
  | [] => rfl
  | _ :: bits => by
      simp [alternatingMasks, alternatingMasks_snd_length (!phase) bits]

theorem alternatingMasks_reconstruct (phase : Bool) : ∀ bits,
    mergeMasks (alternatingMasks phase bits).1
      (alternatingMasks phase bits).2 = bits
  | [] => rfl
  | b :: bits => by
      cases b <;> cases phase <;>
        simp [alternatingMasks, mergeMasks,
          alternatingMasks_reconstruct]

theorem alternatingMasks_disjoint (phase : Bool) : ∀ bits,
    overlapMasks (alternatingMasks phase bits).1
      (alternatingMasks phase bits).2 =
        List.replicate bits.length false
  | [] => rfl
  | b :: bits => by
      cases b <;> cases phase <;>
        simp only [alternatingMasks, overlapMasks, Bool.false_and,
          Bool.true_and, Bool.not_false, Bool.not_true,
          alternatingMasks_disjoint, List.length_cons]
      all_goals
        rw [show bits.length + 1 = Nat.succ bits.length by omega,
          List.replicate_succ]

/-- The ordinary left component begins external at the left boundary. -/
def CutPattern.leftMasks (p : CutPattern) : List Bool × List Bool :=
  alternatingMasks false p.leftBits

/-- The reset flips the phase that ordinary path alternation would have at
the first suffix position. -/
def resetSuffixPhase (cut : Nat) : Bool :=
  !(YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.flipN
      (cut + 1) false)

def CutPattern.rightMasks (p : CutPattern) : List Bool × List Bool :=
  alternatingMasks (resetSuffixPhase p.cut) p.suffix

def CutPattern.terminalMask (p : CutPattern) : List Bool :=
  p.leftMasks.1 ++ false :: p.rightMasks.1

def CutPattern.externalMask (p : CutPattern) : List Bool :=
  p.leftMasks.2 ++ false :: p.rightMasks.2

private theorem mergeMasks_append_of_lengths :
    ∀ (a b c d : List Bool), a.length = b.length →
      mergeMasks (a ++ c) (b ++ d) =
        mergeMasks a b ++ mergeMasks c d
  | [], [], c, d, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | a :: as, b :: bs, c, d, h => by
      simp only [List.cons_append, mergeMasks]
      congr 1
      exact mergeMasks_append_of_lengths as bs c d (Nat.succ.inj h)

private theorem overlapMasks_append_of_lengths :
    ∀ (a b c d : List Bool), a.length = b.length →
      overlapMasks (a ++ c) (b ++ d) =
        overlapMasks a b ++ overlapMasks c d
  | [], [], c, d, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | a :: as, b :: bs, c, d, h => by
      simp only [List.cons_append, overlapMasks]
      congr 1
      exact overlapMasks_append_of_lengths as bs c d (Nat.succ.inj h)

private theorem replicate_false_cut : ∀ a b : Nat,
    List.replicate a false ++ false :: List.replicate b false =
      List.replicate (a + 1 + b) false
  | 0, b => by
      change false :: List.replicate b false =
        List.replicate (1 + b) false
      rw [show 1 + b = Nat.succ b by omega, List.replicate_succ]
  | a + 1, b => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [replicate_false_cut a b]
      rw [show a + 1 + 1 + b = Nat.succ (a + 1 + b) by omega,
        List.replicate_succ]

theorem CutPattern.terminalMask_length (p : CutPattern) :
    p.terminalMask.length = p.pathLength := by
  simp [CutPattern.terminalMask, CutPattern.leftMasks,
    CutPattern.rightMasks, CutPattern.pathLength,
    alternatingMasks_fst_length, CutPattern.leftBits_length]
  omega

theorem CutPattern.externalMask_length (p : CutPattern) :
    p.externalMask.length = p.pathLength := by
  simp [CutPattern.externalMask, CutPattern.leftMasks,
    CutPattern.rightMasks, CutPattern.pathLength,
    alternatingMasks_snd_length, CutPattern.leftBits_length]
  omega

/-- Terminal plus external recovers every selected source occurrence. -/
theorem CutPattern.masks_reconstruct (p : CutPattern) :
    mergeMasks p.terminalMask p.externalMask = p.sourceBits := by
  unfold CutPattern.terminalMask CutPattern.externalMask
  rw [mergeMasks_append_of_lengths p.leftMasks.1 p.leftMasks.2
    (false :: p.rightMasks.1) (false :: p.rightMasks.2)]
  · simp only [mergeMasks, Bool.false_or]
    simp only [CutPattern.leftMasks, CutPattern.rightMasks,
      CutPattern.sourceBits]
    rw [alternatingMasks_reconstruct, alternatingMasks_reconstruct]
  · unfold CutPattern.leftMasks
    rw [alternatingMasks_fst_length, alternatingMasks_snd_length]

/-- No selected occurrence is charged to both layers. -/
theorem CutPattern.masks_disjoint (p : CutPattern) :
    overlapMasks p.terminalMask p.externalMask =
      List.replicate p.pathLength false := by
  unfold CutPattern.terminalMask CutPattern.externalMask
  rw [overlapMasks_append_of_lengths p.leftMasks.1 p.leftMasks.2
    (false :: p.rightMasks.1) (false :: p.rightMasks.2)]
  · simp only [overlapMasks, Bool.false_and]
    simp only [CutPattern.leftMasks, CutPattern.rightMasks]
    rw [alternatingMasks_disjoint, alternatingMasks_disjoint]
    rw [CutPattern.leftBits_length]
    exact replicate_false_cut p.cut p.suffix.length
  · unfold CutPattern.leftMasks
    rw [alternatingMasks_fst_length, alternatingMasks_snd_length]

/-! ## Explicit owner tags and disjoint singleton blocks -/

/-- The carrier substrate stores the cut separately from the two masks. -/
structure CutTaggedCarrier where
  cut : Nat
  terminal : List Bool
  external : List Bool
deriving DecidableEq

def encodeCutPattern (p : CutPattern) : CutTaggedCarrier where
  cut := p.cut
  terminal := p.terminalMask
  external := p.externalMask

def CutTaggedCarrier.recoveredSource (c : CutTaggedCarrier) : List Bool :=
  mergeMasks c.terminal c.external

def CutTaggedCarrier.ownerKey (c : CutTaggedCarrier) : Nat × List Bool :=
  (c.cut, c.recoveredSource)

def CutPattern.ownerKey (p : CutPattern) : Nat × List Bool :=
  (p.cut, p.sourceBits)

theorem ownerKey_encode (p : CutPattern) :
    (encodeCutPattern p).ownerKey = p.ownerKey := by
  simp [CutTaggedCarrier.ownerKey, CutTaggedCarrier.recoveredSource,
    CutPattern.ownerKey, encodeCutPattern, CutPattern.masks_reconstruct]

theorem encodeCutPattern_injective {p q : CutPattern}
    (h : encodeCutPattern p = encodeCutPattern q) : p = q := by
  have hkey : p.ownerKey = q.ownerKey := by
    rw [← ownerKey_encode p, ← ownerKey_encode q, h]
  have hcut : p.cut = q.cut := congrArg Prod.fst hkey
  have hsource : p.sourceBits = q.sourceBits := congrArg Prod.snd hkey
  cases p with
  | mk pc ps =>
      cases q with
      | mk qc qs =>
          simp only [CutPattern.sourceBits,
            CutPattern.leftBits] at hcut hsource
          subst qc
          have hsuffix : ps = qs := by simpa using hsource
          subst qs
          rfl

def cutTaggedBlock (p : CutPattern) : List CutTaggedCarrier :=
  [encodeCutPattern p]

theorem cutTaggedBlock_nodup (p : CutPattern) :
    (cutTaggedBlock p).Nodup := by
  simp [cutTaggedBlock]

/-- The explicit cut and reconstructed source give deterministic ownership,
so distinct source keys have disjoint singleton blocks. -/
theorem cutTaggedBlocks_disjoint {p q : CutPattern} (hpq : p ≠ q) :
    ∀ code, code ∈ cutTaggedBlock p → code ∉ cutTaggedBlock q := by
  intro code hp hq
  simp only [cutTaggedBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hp hq
  subst code
  exact hpq (encodeCutPattern_injective hq)

/-! ## Exact activity factorization and payment -/

/-- Product of the activities selected by a Boolean mask. -/
def maskedProduct : (Nat → Q') → List Bool → Q'
  | _, [] => 1
  | activity, b :: bs =>
      (if b then activity 0 else 1) *
        maskedProduct (fun i => activity (i + 1)) bs

private theorem maskedProduct_zero_head
    (x y z : Q') (h : x * y ≈ z) :
    (1 * x) * (1 * y) ≈ 1 * z := by
  refine Q'.eqv_trans _ (1 * (x * y)) _ (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left 1 _ _ h

private theorem maskedProduct_only_right
    (a x y z : Q') (h : x * y ≈ z) :
    (1 * x) * (a * y) ≈ a * z := by
  refine Q'.eqv_trans _ (a * (x * y)) _ (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left a _ _ h

private theorem maskedProduct_only_left
    (a x y z : Q') (h : x * y ≈ z) :
    (a * x) * (1 * y) ≈ a * z := by
  refine Q'.eqv_trans _ (a * (x * y)) _ (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left a _ _ h

private theorem maskedProduct_partition
    (activity : Nat → Q') (terminal external source : List Bool)
    (ht : terminal.length = source.length)
    (he : external.length = source.length)
    (hm : mergeMasks terminal external = source)
    (hd : overlapMasks terminal external =
      List.replicate source.length false) :
    maskedProduct activity terminal * maskedProduct activity external ≈
      maskedProduct activity source := by
  induction source generalizing activity terminal external with
  | nil =>
      cases terminal with
      | nil =>
          cases external with
          | nil =>
              exact Q'.mul_one_eqv _
          | cons _ _ => cases he
      | cons _ _ => cases ht
  | cons s ss ih =>
      cases terminal with
      | nil => cases ht
      | cons t ts =>
          cases external with
          | nil => cases he
          | cons e es =>
              change (t || e) :: mergeMasks ts es = s :: ss at hm
              change (t && e) :: overlapMasks ts es =
                false :: List.replicate ss.length false at hd
              injection hm with hhead hmerge
              injection hd with hdisjoint hdisjointTail
              have ihTail := ih (fun i => activity (i + 1)) ts es
                (Nat.succ.inj ht) (Nat.succ.inj he)
                hmerge hdisjointTail
              cases t <;> cases e <;> cases s
              · exact maskedProduct_zero_head _ _ _ ihTail
              · cases hhead
              · cases hhead
              · exact maskedProduct_only_right (activity 0) _ _ _ ihTail
              · cases hhead
              · exact maskedProduct_only_left (activity 0) _ _ _ ihTail
              · cases hhead
              · cases hdisjoint

def cutTaggedSourceWeight (activity : Nat → Q') (p : CutPattern) : Q' :=
  maskedProduct activity p.sourceBits

def cutTaggedCarrierWeight (activity : Nat → Q')
    (carrier : CutTaggedCarrier) : Q' :=
  maskedProduct activity carrier.terminal *
    maskedProduct activity carrier.external

/-- The two reset-colored layers factor the full source activity exactly. -/
theorem cutTaggedCarrierWeight_eqv_source
    (activity : Nat → Q') (p : CutPattern) :
    cutTaggedCarrierWeight activity (encodeCutPattern p) ≈
      cutTaggedSourceWeight activity p := by
  apply maskedProduct_partition
  · exact p.terminalMask_length.trans p.sourceBits_length.symm
  · exact p.externalMask_length.trans p.sourceBits_length.symm
  · exact p.masks_reconstruct
  · rw [p.sourceBits_length]
    exact p.masks_disjoint

/-- Consequently the source is paid by the singleton cut-tagged block. -/
theorem cutTaggedSource_le_block
    (activity : Nat → Q') (p : CutPattern) :
    cutTaggedSourceWeight activity p ≤
      qListSum (cutTaggedCarrierWeight activity) (cutTaggedBlock p) := by
  simp only [cutTaggedBlock, qListSum_cons, qListSum_nil, Q'.add_zero']
  exact Q'.ge_of_eqv (cutTaggedCarrierWeight_eqv_source activity p)

end YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.CutPattern.masks_reconstruct
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.CutPattern.masks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.firstCut_complete
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.ownerKey_encode
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.encodeCutPattern_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.cutTaggedBlocks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.cutTaggedCarrierWeight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier.cutTaggedSource_le_block
