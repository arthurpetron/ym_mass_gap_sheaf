/-
# Degree-bounded selected quaternion translation chains

The BF4 cutoff-one slab has degree at most six in every link block.  This
module turns that structural bound into the executable left/right translation
certificates used by the selected-pair Haar chain.  It also proves that a
translation can increase degree only in its multiplier block.  Consequently
a chain whose selected blocks are chords and whose multipliers are tree links
preserves a common chord-degree bound throughout.

## Axiom gate

Finite polynomial recursion, exact monomial degrees, and decidable moment
tables only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive

/-! ## 1. At-most block degree -/

def QuaternionBlockDegreeAtMost
    (block maxDegree : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    quaternionBlockDegree term.1 block ≤ maxDegree

theorem quaternionBlockDegreeAtMost_zero
    (block maxDegree : Nat) :
    QuaternionBlockDegreeAtMost block maxDegree polyZero := by
  intro term hterm
  simp [polyZero] at hterm

theorem QuaternionBlockDegreeAtMost.add
    {block maxDegree : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockDegreeAtMost block maxDegree left)
    (hright : QuaternionBlockDegreeAtMost block maxDegree right) :
    QuaternionBlockDegreeAtMost block maxDegree (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

theorem QuaternionBlockDegreeAtMost.neg
    {block maxDegree : Nat} {polynomial : RatPoly}
    (h : QuaternionBlockDegreeAtMost block maxDegree polynomial) :
    QuaternionBlockDegreeAtMost block maxDegree (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact h source hsource

theorem QuaternionBlockDegreeAtMost.smul
    {block maxDegree : Nat} {polynomial : RatPoly}
    (h : QuaternionBlockDegreeAtMost block maxDegree polynomial)
    (scale : Q') :
    QuaternionBlockDegreeAtMost block maxDegree
      (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact h source hsource

theorem QuaternionBlockDegreeAtMost.mono
    {block first second : Nat} {polynomial : RatPoly}
    (h : QuaternionBlockDegreeAtMost block first polynomial)
    (hle : first ≤ second) :
    QuaternionBlockDegreeAtMost block second polynomial := by
  intro term hterm
  exact Nat.le_trans (h term hterm) hle

theorem quaternionBlockDegreeAtMost_one
    (block maxDegree : Nat) :
    QuaternionBlockDegreeAtMost block maxDegree polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [quaternionBlockDegree, exponentAt]

private theorem quaternionBlockDegree_monoMul
    (left right : List Nat) (block : Nat) :
    quaternionBlockDegree (monoMul left right) block =
      quaternionBlockDegree left block +
        quaternionBlockDegree right block := by
  unfold quaternionBlockDegree
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul]
  omega

theorem QuaternionBlockDegreeAtMost.mul
    {block leftMax rightMax : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockDegreeAtMost block leftMax left)
    (hright : QuaternionBlockDegreeAtMost block rightMax right) :
    QuaternionBlockDegreeAtMost block (leftMax + rightMax)
      (polyMul left right) := by
  intro term hterm
  obtain ⟨source, hsource, hrow⟩ := List.mem_flatMap.mp hterm
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hrow
  rw [quaternionBlockDegree_monoMul]
  exact Nat.add_le_add (hleft source hsource) (hright target htarget)

theorem hasDegree_to_degreeAtMost
    {block degree maxDegree : Nat} {polynomial : RatPoly}
    (hdegree : HasQuaternionBlockDegree block degree polynomial)
    (hle : degree ≤ maxDegree) :
    QuaternionBlockDegreeAtMost block maxDegree polynomial := by
  intro term hterm
  rw [hdegree term hterm]
  exact hle

private theorem quaternionBlockDegree_reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat) {block : Nat} (hblock : block < blocks) :
    quaternionBlockDegree
        (reindexQuaternionExponents permutation monomial) block =
      quaternionBlockDegree monomial (permutation.map block) := by
  unfold quaternionBlockDegree
  rw [exponentAt_reindexQuaternionExponents permutation monomial (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial (by omega)]
  have h0 : (4 * block) / 4 = block := by omega
  have h1 : (4 * block + 1) / 4 = block := by omega
  have h2 : (4 * block + 2) / 4 = block := by omega
  have h3 : (4 * block + 3) / 4 = block := by omega
  have m0 : (4 * block) % 4 = 0 := by omega
  have m1 : (4 * block + 1) % 4 = 1 := by omega
  have m2 : (4 * block + 2) % 4 = 2 := by omega
  have m3 : (4 * block + 3) % 4 = 3 := by omega
  rw [h0, h1, h2, h3, m0, m1, m2, m3]
  simp only [Nat.add_zero]

theorem QuaternionBlockDegreeAtMost.reindex
    {blocks block maxDegree : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) {polynomial : RatPoly}
    (h : QuaternionBlockDegreeAtMost
      (permutation.map block) maxDegree polynomial) :
    QuaternionBlockDegreeAtMost block maxDegree
      (reindexQuaternionPolynomial permutation polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  rw [quaternionBlockDegree_reindex permutation source.1 hblock]
  exact h source hsource

theorem QuaternionBlockDegreeAtMost.signSelected
    {block maxDegree coordinates : Nat}
    (selected : Nat → Bool) {polynomial : RatPoly}
    (h : QuaternionBlockDegreeAtMost block maxDegree polynomial) :
    QuaternionBlockDegreeAtMost block maxDegree
      (signSelectedPolynomial coordinates selected polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact h source hsource

/-! ## 2. Degree six supplies every cutoff-one moment check -/

theorem translationPolynomialCheck_of_degreeAtMost
    {check : Nat → Nat → Nat → Nat → Bool}
    {maxDegree : Nat} {polynomial : RatPoly}
    (hchecks : translationMomentChecksThrough check maxDegree = true)
    (hdegree : QuaternionBlockDegreeAtMost 0 maxDegree polynomial) :
    translationPolynomialCheck check polynomial = true := by
  apply List.all_eq_true.mpr
  intro term hterm
  apply translationMomentChecksThrough_apply hchecks
  simpa [quaternionBlockDegree] using hdegree term hterm

/-! ## 3. Translated-head substitution preserves every non-multiplier block -/

private theorem ratPolyPow_blockDegree
    {block degree : Nat} {polynomial : RatPoly}
    (hdegree : HasQuaternionBlockDegree block degree polynomial) :
    ∀ exponent,
      HasQuaternionBlockDegree block (exponent * degree)
        (ratPolyPow polynomial exponent)
  | 0 => by
      simpa using hasQuaternionBlockDegree_one block
  | exponent + 1 => by
      exact HasQuaternionBlockDegree.relabel
        (by rw [Nat.succ_mul] :
          exponent * degree + degree = (exponent + 1) * degree)
        ((ratPolyPow_blockDegree hdegree exponent).mul hdegree)

private theorem translatedHeadQuaternion_blockDegree
    (translated : PolyQuaternion)
    (htranslated : translated = leftTranslatedHeadQuaternion ∨
      translated = rightTranslatedHeadQuaternion)
    (block : Nat) :
    HasPolyQuaternionBlockDegree block
      (if block = 0 ∨ block = 1 then 1 else 0) translated := by
  rcases htranslated with rfl | rfl
  · unfold leftTranslatedHeadQuaternion
    by_cases h0 : block = 0
    · subst block
      simpa using
        (hasPolyQuaternionBlockDegree_coordinateVariable 1 0).mul
          (hasPolyQuaternionBlockDegree_coordinateVariable 0 0)
    · by_cases h1 : block = 1
      · subst block
        simpa using
          (hasPolyQuaternionBlockDegree_coordinateVariable 1 1).mul
            (hasPolyQuaternionBlockDegree_coordinateVariable 0 1)
      · simpa [h0, h1] using
          (hasPolyQuaternionBlockDegree_coordinateVariable 1 block).mul
            (hasPolyQuaternionBlockDegree_coordinateVariable 0 block)
  · unfold rightTranslatedHeadQuaternion
    by_cases h0 : block = 0
    · subst block
      simpa using
        (hasPolyQuaternionBlockDegree_coordinateVariable 0 0).mul
          (hasPolyQuaternionBlockDegree_coordinateVariable 1 0)
    · by_cases h1 : block = 1
      · subst block
        simpa using
          (hasPolyQuaternionBlockDegree_coordinateVariable 0 1).mul
            (hasPolyQuaternionBlockDegree_coordinateVariable 1 1)
      · simpa [h0, h1] using
          (hasPolyQuaternionBlockDegree_coordinateVariable 0 block).mul
            (hasPolyQuaternionBlockDegree_coordinateVariable 1 block)

private theorem translatedHeadMonomial_blockDegree
    (translated : PolyQuaternion)
    (htranslated : translated = leftTranslatedHeadQuaternion ∨
      translated = rightTranslatedHeadQuaternion)
    (block e0 e1 e2 e3 : Nat) :
    HasQuaternionBlockDegree block
      (if block = 0 ∨ block = 1 then e0 + e1 + e2 + e3 else 0)
      (translatedHeadMonomial translated e0 e1 e2 e3) := by
  have hq := translatedHeadQuaternion_blockDegree
    translated htranslated block
  unfold translatedHeadMonomial
  by_cases hb : block = 0 ∨ block = 1
  · rw [if_pos hb] at hq ⊢
    exact HasQuaternionBlockDegree.relabel
      (by omega :
        e0 * 1 + (e1 * 1 + (e2 * 1 + e3 * 1)) =
          e0 + e1 + e2 + e3)
      ((ratPolyPow_blockDegree hq.scalar e0).mul
      ((ratPolyPow_blockDegree hq.iPart e1).mul
        ((ratPolyPow_blockDegree hq.jPart e2).mul
          (ratPolyPow_blockDegree hq.kPart e3))))
  · rw [if_neg hb] at hq ⊢
    exact HasQuaternionBlockDegree.relabel
      (by omega :
        e0 * 0 + (e1 * 0 + (e2 * 0 + e3 * 0)) = 0)
      ((ratPolyPow_blockDegree hq.scalar e0).mul
      ((ratPolyPow_blockDegree hq.iPart e1).mul
        ((ratPolyPow_blockDegree hq.jPart e2).mul
          (ratPolyPow_blockDegree hq.kPart e3))))

private theorem exponentAt_headTailLift
    (term : RatTerm) (coordinate : Nat) (hcoordinate : 4 ≤ coordinate) :
    exponentAt ([0, 0, 0, 0] ++ term.1.drop 4) coordinate =
      exponentAt term.1 coordinate := by
  have hsplit : coordinate = 4 + (coordinate - 4) := by omega
  rw [hsplit]
  simp only [List.cons_append, List.nil_append]
  have hprefix :
      exponentAt (0 :: 0 :: 0 :: 0 :: term.1.drop 4)
          (4 + (coordinate - 4)) =
        exponentAt (term.1.drop 4) (coordinate - 4) := by
    unfold exponentAt
    rw [Nat.add_comm 4 (coordinate - 4)]
    rfl
  rw [hprefix]
  exact exponentAt_drop term.1 4 (coordinate - 4)

private theorem headTailLiftTerm_blockDegree
    (term : RatTerm) (block : Nat) :
    HasQuaternionBlockDegree block
      (if block = 0 then 0 else quaternionBlockDegree term.1 block)
      (headTailLiftTerm term) := by
  intro source hsource
  simp only [headTailLiftTerm, List.mem_cons, List.not_mem_nil,
    or_false] at hsource
  subst source
  by_cases hblock : block = 0
  · subst block
    simp [quaternionBlockDegree, exponentAt]
  · have hpos : 0 < block := Nat.pos_of_ne_zero hblock
    unfold quaternionBlockDegree
    simp only [if_neg hblock]
    have h4b : 4 ≤ 4 * block := by omega
    have h4b1 : 4 ≤ 4 * block + 1 := by omega
    have h4b2 : 4 ≤ 4 * block + 2 := by omega
    have h4b3 : 4 ≤ 4 * block + 3 := by omega
    rw [exponentAt_headTailLift term (4 * block) h4b,
      exponentAt_headTailLift term (4 * block + 1) h4b1,
      exponentAt_headTailLift term (4 * block + 2) h4b2,
      exponentAt_headTailLift term (4 * block + 3) h4b3]

private theorem translatedHeadTerm_degreeAtMost
    (translated : PolyQuaternion)
    (htranslated : translated = leftTranslatedHeadQuaternion ∨
      translated = rightTranslatedHeadQuaternion)
    {block maxDegree : Nat} (hnotMultiplier : block ≠ 1)
    (term : RatTerm)
    (hdegree : quaternionBlockDegree term.1 block ≤ maxDegree) :
    QuaternionBlockDegreeAtMost block maxDegree
      (translatedHeadTerm translated term) := by
  intro output houtput
  have htranslatedDegree := translatedHeadMonomial_blockDegree
    translated htranslated block
    (exponentAt term.1 0) (exponentAt term.1 1)
    (exponentAt term.1 2) (exponentAt term.1 3)
  have htailDegree := headTailLiftTerm_blockDegree term block
  have houtputDegree := htranslatedDegree.mul htailDegree
  unfold translatedHeadTerm at houtput
  rw [houtputDegree output houtput]
  by_cases hzero : block = 0
  · subst block
    simpa [quaternionBlockDegree] using hdegree
  · have hother : ¬ (block = 0 ∨ block = 1) := by
      intro h
      exact h.elim hzero hnotMultiplier
    simpa [hzero, hnotMultiplier] using hdegree

theorem translatedHeadPolynomial_degreeAtMost_nonMultiplier
    (translated : PolyQuaternion)
    (htranslated : translated = leftTranslatedHeadQuaternion ∨
      translated = rightTranslatedHeadQuaternion)
    {block maxDegree : Nat} (hnotMultiplier : block ≠ 1) :
    ∀ polynomial : RatPoly,
      QuaternionBlockDegreeAtMost block maxDegree polynomial →
      QuaternionBlockDegreeAtMost block maxDegree
        (translatedHeadPolynomial translated polynomial)
  | [], _ => quaternionBlockDegreeAtMost_zero block maxDegree
  | term :: rest, hdegree => by
      apply QuaternionBlockDegreeAtMost.add
      · exact translatedHeadTerm_degreeAtMost translated htranslated
          hnotMultiplier term (hdegree term List.mem_cons_self)
      · exact translatedHeadPolynomial_degreeAtMost_nonMultiplier
          translated htranslated hnotMultiplier rest
          (fun source hsource =>
            hdegree source (List.mem_cons_of_mem term hsource))

/-! ## 4. Selected-pair translations preserve all non-multiplier blocks -/

private theorem exposeTranslationPair_degreeAtMost
    (blocks selected multiplier maxDegree : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (hdistinct : selected ≠ multiplier)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost selected maxDegree polynomial) :
    QuaternionBlockDegreeAtMost 0 maxDegree
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier polynomial) := by
  unfold exposeTranslationPairPolynomial
  apply QuaternionBlockDegreeAtMost.reindex _ (by omega)
  rw [translationPairTailPermutation_map_zero blocks selected multiplier
    hblocks hselected hmultiplier hdistinct]
  apply QuaternionBlockDegreeAtMost.reindex _ (by omega)
  rw [translationPairHeadPermutation,
    headSwapBlockInvolution_map_zero]
  exact hdegree

private theorem selectedTranslatedPolynomial_degreeAtMost_nonMultiplier
    (translated : PolyQuaternion)
    (htranslated : translated = leftTranslatedHeadQuaternion ∨
      translated = rightTranslatedHeadQuaternion)
    (tailBlocks selected multiplier monitored maxDegree : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (_hdistinct : selected ≠ multiplier)
    (hmonitored : monitored < tailBlocks + 1)
    (hnotMultiplier : monitored ≠ multiplier)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost monitored maxDegree polynomial) :
    QuaternionBlockDegreeAtMost monitored maxDegree
      (restoreTranslationPairPolynomial (tailBlocks + 1)
        selected multiplier (by omega) hselected hmultiplier
        (translatedHeadPolynomial translated
          (exposeTranslationPairPolynomial (tailBlocks + 1)
            selected multiplier (by omega) hselected hmultiplier
            polynomial))) := by
  let head := translationPairHeadPermutation
    (tailBlocks + 1) selected hselected
  let tail := translationPairTailPermutation
    (tailBlocks + 1) selected multiplier (by omega) hselected hmultiplier
  let exposedBlock := tail.map (head.map monitored)
  have hheadMonitored : head.map monitored < tailBlocks + 1 :=
    head.map_lt monitored hmonitored
  have hexposedLt : exposedBlock < tailBlocks + 1 :=
    tail.map_lt (head.map monitored) hheadMonitored
  have hexposedSource :
      head.map (tail.map exposedBlock) = monitored := by
    dsimp only [exposedBlock]
    rw [tail.involutive (head.map monitored) hheadMonitored,
      head.involutive monitored hmonitored]
  have hexposedDegree : QuaternionBlockDegreeAtMost exposedBlock maxDegree
      (exposeTranslationPairPolynomial (tailBlocks + 1)
        selected multiplier (by omega) hselected hmultiplier polynomial) := by
    unfold exposeTranslationPairPolynomial
    apply QuaternionBlockDegreeAtMost.reindex tail hexposedLt
    apply QuaternionBlockDegreeAtMost.reindex head
      (tail.map_lt exposedBlock hexposedLt)
    rw [hexposedSource]
    exact hdegree
  have hexposedNeOne : exposedBlock ≠ 1 := by
    intro heq
    have hsourceOne : head.map (tail.map 1) = multiplier := by
      simpa [head, tail] using exposedTranslationPair_source_one
        (tailBlocks + 1) selected multiplier (by omega)
        hselected hmultiplier
    have hexposedToMultiplier :
        head.map (tail.map exposedBlock) = multiplier := by
      rw [heq]
      exact hsourceOne
    exact hnotMultiplier
      (hexposedSource.symm.trans hexposedToMultiplier)
  have htranslatedDegree :=
    translatedHeadPolynomial_degreeAtMost_nonMultiplier
      translated htranslated hexposedNeOne _ hexposedDegree
  unfold restoreTranslationPairPolynomial
  apply QuaternionBlockDegreeAtMost.reindex head hmonitored
  apply QuaternionBlockDegreeAtMost.reindex tail hheadMonitored
  simpa [exposedBlock] using htranslatedDegree

theorem applySelectedTranslationStep_degreeAtMost_nonMultiplier
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    {monitored maxDegree : Nat}
    (hmonitored : monitored < tailBlocks + 1)
    (hnotMultiplier : monitored ≠ step.multiplier)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost monitored maxDegree polynomial) :
    QuaternionBlockDegreeAtMost monitored maxDegree
      (applySelectedTranslationStep hblocks step polynomial) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation,
            selectedLeftTranslatedPolynomial] using
            selectedTranslatedPolynomial_degreeAtMost_nonMultiplier
              leftTranslatedHeadQuaternion (Or.inl rfl)
              tailBlocks step.selected step.multiplier monitored maxDegree
              hblocks step.selected_lt step.multiplier_lt step.distinct
              hmonitored hnotMultiplier polynomial hdegree
      | inverse =>
          unfold applySelectedTranslationStep
          rw [hside, horientation]
          unfold selectedLeftInverseTranslatedPolynomial
          apply QuaternionBlockDegreeAtMost.signSelected
          simpa [selectedLeftTranslatedPolynomial] using
            selectedTranslatedPolynomial_degreeAtMost_nonMultiplier
              leftTranslatedHeadQuaternion (Or.inl rfl)
              tailBlocks step.selected step.multiplier monitored maxDegree
              hblocks step.selected_lt step.multiplier_lt step.distinct
              hmonitored hnotMultiplier _
              (QuaternionBlockDegreeAtMost.signSelected _ hdegree)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation,
            selectedRightTranslatedPolynomial] using
            selectedTranslatedPolynomial_degreeAtMost_nonMultiplier
              rightTranslatedHeadQuaternion (Or.inr rfl)
              tailBlocks step.selected step.multiplier monitored maxDegree
              hblocks step.selected_lt step.multiplier_lt step.distinct
              hmonitored hnotMultiplier polynomial hdegree
      | inverse =>
          unfold applySelectedTranslationStep
          rw [hside, horientation]
          unfold selectedRightInverseTranslatedPolynomial
          apply QuaternionBlockDegreeAtMost.signSelected
          simpa [selectedRightTranslatedPolynomial] using
            selectedTranslatedPolynomial_degreeAtMost_nonMultiplier
              rightTranslatedHeadQuaternion (Or.inr rfl)
              tailBlocks step.selected step.multiplier monitored maxDegree
              hblocks step.selected_lt step.multiplier_lt step.distinct
              hmonitored hnotMultiplier _
              (QuaternionBlockDegreeAtMost.signSelected _ hdegree)

theorem selectedTranslationStepCheck_of_selected_degree_five
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlockDegreeAtMost step.selected 5 polynomial) :
    selectedTranslationStepCheck hblocks step polynomial = true := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          unfold selectedTranslationStepCheck
          rw [hside, horientation]
          apply translationPolynomialCheck_of_degreeAtMost
            leftTranslationMomentChecksThrough_five
          exact exposeTranslationPair_degreeAtMost
            (tailBlocks + 1) step.selected step.multiplier 5 (by omega)
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hdegree
      | inverse =>
          unfold selectedTranslationStepCheck
          rw [hside, horientation]
          unfold selectedLeftInverseTranslationCheck
          apply translationPolynomialCheck_of_degreeAtMost
            leftTranslationMomentChecksThrough_five
          exact exposeTranslationPair_degreeAtMost
            (tailBlocks + 1) step.selected step.multiplier 5 (by omega)
            step.selected_lt step.multiplier_lt step.distinct _
            (QuaternionBlockDegreeAtMost.signSelected _ hdegree)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          unfold selectedTranslationStepCheck
          rw [hside, horientation]
          apply translationPolynomialCheck_of_degreeAtMost
            rightTranslationMomentChecksThrough_five
          exact exposeTranslationPair_degreeAtMost
            (tailBlocks + 1) step.selected step.multiplier 5 (by omega)
            step.selected_lt step.multiplier_lt step.distinct polynomial
            hdegree
      | inverse =>
          unfold selectedTranslationStepCheck
          rw [hside, horientation]
          unfold selectedRightInverseTranslationCheck
          apply translationPolynomialCheck_of_degreeAtMost
            rightTranslationMomentChecksThrough_five
          exact exposeTranslationPair_degreeAtMost
            (tailBlocks + 1) step.selected step.multiplier 5 (by omega)
            step.selected_lt step.multiplier_lt step.distinct _
            (QuaternionBlockDegreeAtMost.signSelected _ hdegree)

/-! ## 5. Degree-five certification of a whole selected-pair chain -/

def QuaternionBlocksDegreeAtMost
    (blocks : List Nat) (maxDegree : Nat) (polynomial : RatPoly) : Prop :=
  ∀ block, block ∈ blocks →
    QuaternionBlockDegreeAtMost block maxDegree polynomial

theorem applySelectedTranslationStep_blocksDegreeAtMost_nonMultipliers
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (monitored : List Nat) {maxDegree : Nat}
    (hmonitoredLt : ∀ block, block ∈ monitored →
      block < tailBlocks + 1)
    (hnotMultipliers : ∀ block, block ∈ monitored →
      block ≠ step.multiplier)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlocksDegreeAtMost
      monitored maxDegree polynomial) :
    QuaternionBlocksDegreeAtMost monitored maxDegree
      (applySelectedTranslationStep hblocks step polynomial) := by
  intro block hblock
  exact applySelectedTranslationStep_degreeAtMost_nonMultiplier
    hblocks step (hmonitoredLt block hblock)
    (hnotMultipliers block hblock) polynomial
    (hdegree block hblock)

theorem selectedTranslationStepsCheck_of_monitored_degree_five
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (monitored : List Nat)
    (hmonitoredLt : ∀ block, block ∈ monitored →
      block < tailBlocks + 1) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (polynomial : RatPoly),
      (∀ step, step ∈ steps →
        step.selected ∈ monitored ∧
          ∀ block, block ∈ monitored →
            block ≠ step.multiplier) →
      QuaternionBlocksDegreeAtMost monitored 5 polynomial →
      selectedTranslationStepsCheck hblocks steps polynomial = true
  | [], _, _, _ => rfl
  | step :: rest, polynomial, hsteps, hdegree => by
      have hstep := hsteps step List.mem_cons_self
      have hrestSteps :
          ∀ other, other ∈ rest →
            other.selected ∈ monitored ∧
              ∀ block, block ∈ monitored →
                block ≠ other.multiplier := by
        intro other hother
        exact hsteps other (List.mem_cons_of_mem step hother)
      have hnextDegree : QuaternionBlocksDegreeAtMost monitored 5
          (applySelectedTranslationStep hblocks step polynomial) :=
        applySelectedTranslationStep_blocksDegreeAtMost_nonMultipliers
          hblocks step monitored hmonitoredLt hstep.2 polynomial hdegree
      simp only [selectedTranslationStepsCheck, Bool.and_eq_true]
      exact ⟨selectedTranslationStepCheck_of_selected_degree_five
          hblocks step polynomial (hdegree step.selected hstep.1),
        selectedTranslationStepsCheck_of_monitored_degree_five
          hblocks monitored hmonitoredLt rest
          (applySelectedTranslationStep hblocks step polynomial)
          hrestSteps hnextDegree⟩

def selectedTranslationStepDegreeCompatible
    {tailBlocks : Nat} (monitored : List Nat)
    (step : SelectedTranslationStep tailBlocks) : Bool :=
  decide (step.selected ∈ monitored) &&
    monitored.all fun block => decide (block ≠ step.multiplier)

def selectedTranslationStepsDegreeCompatible
    {tailBlocks : Nat} (monitored : List Nat)
    (steps : List (SelectedTranslationStep tailBlocks)) : Bool :=
  steps.all (selectedTranslationStepDegreeCompatible monitored)

theorem selectedTranslationStepsCheck_of_degreeCompatible_five
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (monitored : List Nat)
    (hmonitoredLt : ∀ block, block ∈ monitored →
      block < tailBlocks + 1)
    (steps : List (SelectedTranslationStep tailBlocks))
    (hcompatible :
      selectedTranslationStepsDegreeCompatible monitored steps = true)
    (polynomial : RatPoly)
    (hdegree : QuaternionBlocksDegreeAtMost monitored 5 polynomial) :
    selectedTranslationStepsCheck hblocks steps polynomial = true := by
  apply selectedTranslationStepsCheck_of_monitored_degree_five
    hblocks monitored hmonitoredLt steps polynomial
  · intro step hstep
    have hrow := List.all_eq_true.mp hcompatible step hstep
    have hsplit :
        decide (step.selected ∈ monitored) = true ∧
          monitored.all (fun block => decide (block ≠ step.multiplier)) =
            true := by
      simpa [selectedTranslationStepDegreeCompatible] using hrow
    exact ⟨of_decide_eq_true hsplit.1,
      fun block hblock =>
        of_decide_eq_true
          (List.all_eq_true.mp hsplit.2 block hblock)⟩
  · exact hdegree

end YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree.applySelectedTranslationStep_degreeAtMost_nonMultiplier
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree.selectedTranslationStepCheck_of_selected_degree_five
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree.selectedTranslationStepsCheck_of_monitored_degree_five
#print axioms YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree.selectedTranslationStepsCheck_of_degreeCompatible_five
