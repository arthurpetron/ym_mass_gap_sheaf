/-
# From the finite BF4 step certificate to proof-carrying ledger steps

This file identifies the decoded, proof-free certificate entry with the
corresponding certified translation step used by the geometric ledgers.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCertificate

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.RingNormaliser
open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

private theorem quaternionPrefixPolynomialEqv_symm
    {blocks : Nat} {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks right left := by
  induction heqv with
  | nil => exact .nil
  | cons hterm _ induction =>
      exact .cons
        ⟨Q'.eqv_symm hterm.coefficient,
          fun coordinate hcoordinate =>
            (hterm.exponent coordinate hcoordinate).symm⟩
        induction

private theorem ratPolyCoeffEqv_singleton_of_prefix
    {blocks : Nat} {left right : RatTerm}
    (heqv : QuaternionPrefixPolynomialEqv blocks [left] [right])
    (hleftLength : left.1.length = 4 * blocks)
    (hrightLength : right.1.length = 4 * blocks) :
    RatPolyCoeffEqv [left] [right] := by
  cases heqv with
  | cons hterm hrest =>
      cases hrest
      have hmonomial : left.1 = right.1 := by
        apply natList_eq_of_length_getD
        · exact hleftLength.trans hrightLength.symm
        · intro coordinate hcoordinate
          exact hterm.exponent coordinate (by omega)
      intro weight
      change left.2 * weight left.1 + 0 ≈
        right.2 * weight right.1 + 0
      rw [hmonomial]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hterm.coefficient)
        (Q'.eqv_refl 0)

private theorem ratPolyCoeffEqv_of_prefix_exact_lengths
    {blocks : Nat} {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right)
    (hleft : ∀ term, term ∈ left → term.1.length = 4 * blocks)
    (hright : ∀ term, term ∈ right → term.1.length = 4 * blocks) :
    RatPolyCoeffEqv left right := by
  induction heqv with
  | nil => exact RatPolyCoeffEqv.refl []
  | @cons leftTerm rightTerm leftRest rightRest hterm hrest induction =>
      have hmonomial : leftTerm.1 = rightTerm.1 := by
        apply natList_eq_of_length_getD
        · exact (hleft leftTerm List.mem_cons_self).trans
            (hright rightTerm List.mem_cons_self).symm
        · intro coordinate hcoordinate
          exact hterm.exponent coordinate (by
            rw [hleft leftTerm List.mem_cons_self] at hcoordinate
            exact hcoordinate)
      intro weight
      change leftTerm.2 * weight leftTerm.1 +
          ratWeightedSum weight leftRest ≈
        rightTerm.2 * weight rightTerm.1 +
          ratWeightedSum weight rightRest
      rw [hmonomial]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hterm.coefficient)
        (induction
          (fun term hmem => hleft term
            (List.mem_cons_of_mem leftTerm hmem))
          (fun term hmem => hright term
            (List.mem_cons_of_mem rightTerm hmem)) weight)

private theorem reindexQuaternionPolynomial_term_length
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (polynomial : RatPoly) (term : RatTerm)
    (hterm : term ∈ reindexQuaternionPolynomial permutation polynomial) :
    term.1.length = 4 * blocks := by
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨source, _, hsource⟩ := List.mem_map.mp hterm
  rw [← hsource]
  exact reindexQuaternionExponents_length permutation source.1

private theorem exposeTranslationPairPolynomial_prefix_coeffEqv
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    RatPolyCoeffEqv
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier left)
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier right) := by
  let head := translationPairHeadPermutation blocks selected hselected
  let tail := translationPairTailPermutation blocks selected multiplier
    hblocks hselected hmultiplier
  have hprefix := QuaternionPrefixPolynomialEqv.reindex tail
    (QuaternionPrefixPolynomialEqv.reindex head heqv)
  apply ratPolyCoeffEqv_of_prefix_exact_lengths hprefix
  · intro term hterm
    exact reindexQuaternionPolynomial_term_length tail _ term hterm
  · intro term hterm
    exact reindexQuaternionPolynomial_term_length tail _ term hterm

private theorem selectedExponentParity_prefix_congr_local
    {blocks : Nat} (selected : Nat → Bool)
    {left right : RatTerm}
    (heqv : QuaternionPrefixTermEqv blocks left right) :
    selectedExponentParity (4 * blocks) selected left.1 =
      selectedExponentParity (4 * blocks) selected right.1 := by
  unfold selectedExponentParity
  have hfold : ∀ (entries : List Nat) (parity : Bool),
      (∀ coordinate, coordinate ∈ entries → coordinate < 4 * blocks) →
      entries.foldl
          (fun current coordinate =>
            if selected coordinate then
              xor current
                (decide (exponentAt left.1 coordinate % 2 = 1))
            else current)
          parity =
        entries.foldl
          (fun current coordinate =>
            if selected coordinate then
              xor current
                (decide (exponentAt right.1 coordinate % 2 = 1))
            else current)
          parity := by
    intro entries parity hentries
    induction entries generalizing parity with
    | nil => rfl
    | cons coordinate rest induction =>
        simp only [List.foldl_cons]
        by_cases hselected : selected coordinate = true
        · rw [if_pos hselected, if_pos hselected,
            heqv.exponent coordinate
              (hentries coordinate List.mem_cons_self)]
          exact induction _ (fun entry hentry =>
            hentries entry (List.mem_cons_of_mem coordinate hentry))
        · rw [if_neg hselected, if_neg hselected]
          exact induction _ (fun entry hentry =>
            hentries entry (List.mem_cons_of_mem coordinate hentry))
  exact hfold (List.range (4 * blocks)) false
    (fun coordinate hcoordinate => List.mem_range.mp hcoordinate)

private theorem signSelectedPolynomial_prefix
    {blocks : Nat} (selected : Nat → Bool)
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected left)
      (signSelectedPolynomial (4 * blocks) selected right) := by
  induction heqv with
  | nil => exact .nil
  | @cons leftTerm rightTerm leftRest rightRest hterm hrest induction =>
      have hparity := selectedExponentParity_prefix_congr_local
        selected hterm
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · generalize hleftParity :
            selectedExponentParity (4 * blocks) selected leftTerm.1 = parity
          have hrightParity :
              selectedExponentParity (4 * blocks) selected rightTerm.1 =
                parity := hparity.symm.trans hleftParity
          cases parity
          · simpa [signSelectedTerm, hleftParity, hrightParity] using
              hterm.coefficient
          · simpa [signSelectedTerm, hleftParity, hrightParity] using
              (Q'.neg_eqv_congr _ _ hterm.coefficient)
        · intro coordinate hcoordinate
          simpa [signSelectedTerm] using
            hterm.exponent coordinate hcoordinate
      · exact induction

private theorem conjugateQuaternionBlockPolynomial_prefix
    (blocks block : Nat) {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (conjugateQuaternionBlockPolynomial blocks block left)
      (conjugateQuaternionBlockPolynomial blocks block right) := by
  exact signSelectedPolynomial_prefix
    (quaternionConjugateCoordinateSelector block) heqv

private theorem translatedRestored_exposed_prefix_coeffEqv
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (translated : PolyQuaternion) {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    RatPolyCoeffEqv
      (restoreTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier
        (translatedHeadPolynomial translated
          (exposeTranslationPairPolynomial blocks selected multiplier
            hblocks hselected hmultiplier left)))
      (restoreTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier
        (translatedHeadPolynomial translated
          (exposeTranslationPairPolynomial blocks selected multiplier
            hblocks hselected hmultiplier right))) := by
  have hexposed := exposeTranslationPairPolynomial_prefix_coeffEqv
    blocks selected multiplier hblocks hselected hmultiplier heqv
  have htranslated := translatedHeadPolynomial_coeffEqv translated hexposed
  unfold restoreTranslationPairPolynomial
  exact RatPolyCoeffEqv.reindex
    (translationPairHeadPermutation blocks selected hselected)
    (RatPolyCoeffEqv.reindex
      (translationPairTailPermutation blocks selected multiplier
        hblocks hselected hmultiplier) htranslated)

private theorem applySelectedTranslationStep_identityReindex_coeffEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution (tailBlocks + 1)) polynomial))
      (applySelectedTranslationStep hblocks step polynomial) := by
  have hidentity := identityReindexQuaternionPolynomial_prefix
    (tailBlocks + 1) polynomial
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation,
            selectedLeftTranslatedPolynomial] using
            (translatedRestored_exposed_prefix_coeffEqv
              (tailBlocks + 1) step.selected step.multiplier (by omega)
              step.selected_lt step.multiplier_lt leftTranslatedHeadQuaternion
              hidentity)
      | inverse =>
          have hconjugatedPrefix := conjugateQuaternionBlockPolynomial_prefix
            (tailBlocks + 1) step.multiplier hidentity
          have htranslated := translatedRestored_exposed_prefix_coeffEqv
            (tailBlocks + 1) step.selected step.multiplier (by omega)
            step.selected_lt step.multiplier_lt leftTranslatedHeadQuaternion
            hconjugatedPrefix
          exact (by
            simpa [applySelectedTranslationStep, hside, horientation,
              selectedLeftInverseTranslatedPolynomial,
              selectedLeftTranslatedPolynomial] using
              (conjugateQuaternionBlockPolynomial_coeffEqv
                (tailBlocks + 1) step.multiplier htranslated))
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation,
            selectedRightTranslatedPolynomial] using
            (translatedRestored_exposed_prefix_coeffEqv
              (tailBlocks + 1) step.selected step.multiplier (by omega)
              step.selected_lt step.multiplier_lt rightTranslatedHeadQuaternion
              hidentity)
      | inverse =>
          have hconjugatedPrefix := conjugateQuaternionBlockPolynomial_prefix
            (tailBlocks + 1) step.multiplier hidentity
          have htranslated := translatedRestored_exposed_prefix_coeffEqv
            (tailBlocks + 1) step.selected step.multiplier (by omega)
            step.selected_lt step.multiplier_lt rightTranslatedHeadQuaternion
            hconjugatedPrefix
          exact (by
            simpa [applySelectedTranslationStep, hside, horientation,
              selectedRightInverseTranslatedPolynomial,
              selectedRightTranslatedPolynomial] using
              (conjugateQuaternionBlockPolynomial_coeffEqv
                (tailBlocks + 1) step.multiplier htranslated))

private theorem applySelectedTranslationStepQuaternion_identityReindex_coeffEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (quaternion : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks [step]
        (reindexPolyQuaternion
          (identityQuaternionBlockInvolution (tailBlocks + 1)) quaternion))
      (applySelectedTranslationStepsQuaternion hblocks [step] quaternion) :=
  ⟨applySelectedTranslationStep_identityReindex_coeffEqv
      hblocks step quaternion.scalar,
    applySelectedTranslationStep_identityReindex_coeffEqv
      hblocks step quaternion.iPart,
    applySelectedTranslationStep_identityReindex_coeffEqv
      hblocks step quaternion.jPart,
    applySelectedTranslationStep_identityReindex_coeffEqv
      hblocks step quaternion.kPart⟩

private theorem reindexTwice_polyVar_coeffEqv_identity
    {blocks target source component : Nat}
    (first second : QuaternionBlockInvolution blocks)
    (htarget : target < blocks) (hcomponent : component < 4)
    (hmap : first.map (second.map target) = source) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first
          (polyVar (4 * source + component))))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution blocks)
        (polyVar (4 * target + component))) := by
  have hleft := reindexTwice_polyVar_prefix first second
    htarget hcomponent hmap
  have hright := identityReindexQuaternionPolynomial_prefix blocks
    (polyVar (4 * target + component))
  have hprefix := QuaternionPrefixPolynomialEqv.trans hleft
    (quaternionPrefixPolynomialEqv_symm hright)
  change QuaternionPrefixPolynomialEqv blocks
    [(reindexQuaternionExponents second
      (reindexQuaternionExponents first
        (varMono (4 * source + component))), 1)]
    [(reindexQuaternionExponents
      (identityQuaternionBlockInvolution blocks)
        (varMono (4 * target + component)), 1)] at hprefix
  exact ratPolyCoeffEqv_singleton_of_prefix hprefix
    (reindexQuaternionExponents_length second _)
    (reindexQuaternionExponents_length
      (identityQuaternionBlockInvolution blocks) _)

private theorem reindexTwice_identityReindexedPolyVar_coeffEqv_identity
    {blocks target source component : Nat}
    (first second : QuaternionBlockInvolution blocks)
    (htarget : target < blocks) (hcomponent : component < 4)
    (hmap : first.map (second.map target) = source) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first
          (reindexQuaternionPolynomial
            (identityQuaternionBlockInvolution blocks)
            (polyVar (4 * source + component)))))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution blocks)
        (polyVar (4 * target + component))) := by
  have hid := identityReindexQuaternionPolynomial_prefix blocks
    (polyVar (4 * source + component))
  have hidReindexed := QuaternionPrefixPolynomialEqv.reindex second
    (QuaternionPrefixPolynomialEqv.reindex first hid)
  have htransport := reindexTwice_polyVar_prefix first second
    htarget hcomponent hmap
  have htargetIdentity := identityReindexQuaternionPolynomial_prefix blocks
    (polyVar (4 * target + component))
  have hprefix := QuaternionPrefixPolynomialEqv.trans hidReindexed
    (QuaternionPrefixPolynomialEqv.trans htransport
      (quaternionPrefixPolynomialEqv_symm htargetIdentity))
  change QuaternionPrefixPolynomialEqv blocks
    [(reindexQuaternionExponents second
      (reindexQuaternionExponents first
        (reindexQuaternionExponents
          (identityQuaternionBlockInvolution blocks)
          (varMono (4 * source + component)))), 1)]
    [(reindexQuaternionExponents
      (identityQuaternionBlockInvolution blocks)
      (varMono (4 * target + component)), 1)] at hprefix
  exact ratPolyCoeffEqv_singleton_of_prefix hprefix
    (reindexQuaternionExponents_length second _)
    (reindexQuaternionExponents_length
      (identityQuaternionBlockInvolution blocks) _)

private theorem zeroFour_append_drop_eq
    (monomial : List Nat) (hlength : 4 ≤ monomial.length)
    (h0 : exponentAt monomial 0 = 0)
    (h1 : exponentAt monomial 1 = 0)
    (h2 : exponentAt monomial 2 = 0)
    (h3 : exponentAt monomial 3 = 0) :
    [0, 0, 0, 0] ++ monomial.drop 4 = monomial := by
  cases monomial with
  | nil => simp at hlength
  | cons a rest =>
      cases rest with
      | nil => simp at hlength
      | cons b rest =>
          cases rest with
          | nil => simp at hlength
          | cons c rest =>
              cases rest with
              | nil => simp at hlength
              | cons d rest =>
                  simp [exponentAt] at h0 h1 h2 h3
                  subst a
                  subst b
                  subst c
                  subst d
                  rfl

private theorem translatedHeadPolynomial_singleton_zeroHead
    (translated : PolyQuaternion) (monomial : List Nat)
    (h0 : exponentAt monomial 0 = 0)
    (h1 : exponentAt monomial 1 = 0)
    (h2 : exponentAt monomial 2 = 0)
    (h3 : exponentAt monomial 3 = 0)
    (hrebuild : [0, 0, 0, 0] ++ monomial.drop 4 = monomial) :
    translatedHeadPolynomial translated [(monomial, 1)] =
      [(monomial, 1)] := by
  simp [translatedHeadPolynomial, translatedHeadTerm,
    translatedHeadMonomial, ratPolyPow, headTailLiftTerm,
    polyAdd, polyMul, polyOne, polyZero,
    RingNormaliser.monoMul, h0, h1, h2, h3, hrebuild] <;>
    decide

private theorem identityReindexedVar_head_zero
    {blocks target component headCoordinate : Nat}
    (htarget : target < blocks) (htargetNe : target ≠ 0)
    (hcomponent : component < 4) (hhead : headCoordinate < 4) :
    exponentAt
      (reindexQuaternionExponents
        (identityQuaternionBlockInvolution blocks)
        (varMono (4 * target + component))) headCoordinate = 0 := by
  rw [exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks) _ (by omega),
    exponentAt_varMono]
  change (if 4 * (headCoordinate / 4) + headCoordinate % 4 =
      4 * target + component then 1 else 0) = 0
  rw [if_neg]
  intro heq
  have htargetZero : target = 0 := by omega
  exact htargetNe htargetZero

private theorem translatedHeadPolynomial_identityReindexPolyVar_of_ne_zero
    {blocks target component : Nat}
    (translated : PolyQuaternion)
    (htarget : target < blocks) (htargetNe : target ≠ 0)
    (hcomponent : component < 4) :
    translatedHeadPolynomial translated
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution blocks)
          (polyVar (4 * target + component))) =
      reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution blocks)
        (polyVar (4 * target + component)) := by
  let monomial := reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks)
    (varMono (4 * target + component))
  have h0 : exponentAt monomial 0 = 0 :=
    identityReindexedVar_head_zero htarget htargetNe hcomponent (by omega)
  have h1 : exponentAt monomial 1 = 0 :=
    identityReindexedVar_head_zero htarget htargetNe hcomponent (by omega)
  have h2 : exponentAt monomial 2 = 0 :=
    identityReindexedVar_head_zero htarget htargetNe hcomponent (by omega)
  have h3 : exponentAt monomial 3 = 0 :=
    identityReindexedVar_head_zero htarget htargetNe hcomponent (by omega)
  have hlength : 4 ≤ monomial.length := by
    rw [reindexQuaternionExponents_length]
    omega
  have hrebuild := zeroFour_append_drop_eq monomial hlength
    h0 h1 h2 h3
  change translatedHeadPolynomial translated [(monomial, 1)] =
    [(monomial, 1)]
  exact translatedHeadPolynomial_singleton_zeroHead translated monomial
    h0 h1 h2 h3 hrebuild

private theorem restoredTranslatedExposed_polyVar_of_ne_selected
    (tailBlocks selected multiplier block component : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (hblock : block < tailBlocks + 1) (hblockNe : block ≠ selected)
    (hcomponent : component < 4)
    (translated : PolyQuaternion) :
    RatPolyCoeffEqv
      (restoreTranslationPairPolynomial (tailBlocks + 1)
        selected multiplier (by omega) hselected hmultiplier
        (translatedHeadPolynomial translated
          (exposeTranslationPairPolynomial (tailBlocks + 1)
            selected multiplier (by omega) hselected hmultiplier
            (polyVar (4 * block + component)))))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (polyVar (4 * block + component))) := by
  let head := translationPairHeadPermutation
    (tailBlocks + 1) selected hselected
  let tail := translationPairTailPermutation
    (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier
  let target := tail.map (head.map block)
  have htarget : target < tailBlocks + 1 :=
    tail.map_lt _ (head.map_lt block hblock)
  have hmapForward : head.map (tail.map target) = block := by
    dsimp [target]
    rw [tail.involutive (head.map block) (head.map_lt block hblock),
      head.involutive block hblock]
  have htargetNe : target ≠ 0 := by
    intro hzero
    have hsourceZero := exposedTranslationPair_source_zero
      (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier hdistinct
    change head.map (tail.map 0) = selected at hsourceZero
    have hforwardZero : head.map (tail.map 0) = block := by
      rw [← hzero]
      exact hmapForward
    exact hblockNe (hforwardZero.symm.trans hsourceZero)
  have hexposed := reindexTwice_polyVar_coeffEqv_identity
    (component := component) head tail htarget hcomponent hmapForward
  have htranslatedCongr := translatedHeadPolynomial_coeffEqv
    translated hexposed
  have htargetFixed :=
    translatedHeadPolynomial_identityReindexPolyVar_of_ne_zero
      translated htarget htargetNe hcomponent
  have htranslated : RatPolyCoeffEqv
      (translatedHeadPolynomial translated
        (exposeTranslationPairPolynomial (tailBlocks + 1)
          selected multiplier (by omega) hselected hmultiplier
          (polyVar (4 * block + component))))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (polyVar (4 * target + component))) := by
    exact RatPolyCoeffEqv.trans htranslatedCongr (by
      rw [htargetFixed]
      exact RatPolyCoeffEqv.refl _)
  have hrestored := RatPolyCoeffEqv.reindex head
    (RatPolyCoeffEqv.reindex tail htranslated)
  have hmapBack : tail.map (head.map block) = target := rfl
  have hback := reindexTwice_identityReindexedPolyVar_coeffEqv_identity
    (component := component) tail head hblock hcomponent hmapBack
  exact RatPolyCoeffEqv.trans hrestored hback

private theorem applySelectedTranslationStep_direct_coordinate_of_ne_selected
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (block : Nat) (hblock : block < tailBlocks + 1)
    (hblockNe : block ≠ step.selected)
    (horientation : step.multiplierOrientation =
      SelectedMultiplierOrientation.direct) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks [step]
        (PolyQuaternion.coordinateVariable block))
      (reindexPolyQuaternion
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (PolyQuaternion.coordinateVariable block)) := by
  have hcomponent : ∀ component, component < 4 →
      RatPolyCoeffEqv
        (applySelectedTranslationStep hblocks step
          (polyVar (4 * block + component)))
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution (tailBlocks + 1))
          (polyVar (4 * block + component))) := by
    intro component hcomponent
    cases hside : step.side with
    | left =>
        simpa [applySelectedTranslationStep, hside, horientation,
          selectedLeftTranslatedPolynomial] using
          (restoredTranslatedExposed_polyVar_of_ne_selected
            tailBlocks step.selected step.multiplier block component
            hblocks step.selected_lt step.multiplier_lt step.distinct
            hblock hblockNe hcomponent leftTranslatedHeadQuaternion)
    | right =>
        simpa [applySelectedTranslationStep, hside, horientation,
          selectedRightTranslatedPolynomial] using
          (restoredTranslatedExposed_polyVar_of_ne_selected
            tailBlocks step.selected step.multiplier block component
            hblocks step.selected_lt step.multiplier_lt step.distinct
            hblock hblockNe hcomponent rightTranslatedHeadQuaternion)
  exact ⟨
    by simpa [applySelectedTranslationStepsQuaternion,
      applySelectedTranslationSteps, PolyQuaternion.coordinateVariable,
      reindexPolyQuaternion] using hcomponent 0 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      applySelectedTranslationSteps, PolyQuaternion.coordinateVariable,
      reindexPolyQuaternion] using hcomponent 1 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      applySelectedTranslationSteps, PolyQuaternion.coordinateVariable,
      reindexPolyQuaternion] using hcomponent 2 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      applySelectedTranslationSteps, PolyQuaternion.coordinateVariable,
      reindexPolyQuaternion] using hcomponent 3 (by omega)⟩

private theorem signSelectedPolynomial_involutive
    (coordinates : Nat) (selected : Nat → Bool) : ∀ polynomial,
    RatPolyCoeffEqv
      (signSelectedPolynomial coordinates selected
        (signSelectedPolynomial coordinates selected polynomial))
      polynomial
  | [] => RatPolyCoeffEqv.refl []
  | term :: rest => by
      intro weight
      simp only [signSelectedPolynomial, List.map_cons]
      simp only [signSelectedTerm, ratWeightedSum]
      generalize hparity :
        selectedExponentParity coordinates selected term.1 = parity
      cases parity
      · simp only [hparity, Bool.false_eq_true, if_false]
        exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (signSelectedPolynomial_involutive coordinates selected rest weight)
      · simp only [hparity, if_true]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_neg_eqv term.2))
          (signSelectedPolynomial_involutive coordinates selected rest weight)

private theorem conjugateQuaternionBlockPolynomial_involutive
    (blocks block : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (conjugateQuaternionBlockPolynomial blocks block
        (conjugateQuaternionBlockPolynomial blocks block polynomial))
      polynomial := by
  exact signSelectedPolynomial_involutive (4 * blocks)
    (quaternionConjugateCoordinateSelector block) polynomial

private theorem identityReindex_polyVar_selectedExponentParity
    (blocks coordinate : Nat) (selected : Nat → Bool) :
    selectedExponentParity (4 * blocks) selected
        (reindexQuaternionExponents
          (identityQuaternionBlockInvolution blocks)
          (varMono coordinate)) =
      selectedExponentParity (4 * blocks) selected
        (varMono coordinate) := by
  have hprefix := identityReindexQuaternionPolynomial_prefix blocks
    (polyVar coordinate)
  change QuaternionPrefixPolynomialEqv blocks
    [(reindexQuaternionExponents
      (identityQuaternionBlockInvolution blocks)
      (varMono coordinate), 1)] [(varMono coordinate, 1)] at hprefix
  cases hprefix with
  | cons hterm hrest =>
      exact selectedExponentParity_prefix_congr_local selected hterm

private theorem inverseConjugatedDirectPolyVar_of_base
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (directStep : SelectedTranslationStep tailBlocks)
    (multiplier block component : Nat)
    (hbase : RatPolyCoeffEqv
      (applySelectedTranslationSteps hblocks [directStep]
        (polyVar (4 * block + component)))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (polyVar (4 * block + component)))) :
    RatPolyCoeffEqv
      (conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
        (applySelectedTranslationSteps hblocks [directStep]
          (conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
            (polyVar (4 * block + component)))))
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (polyVar (4 * block + component))) := by
  let selector := quaternionConjugateCoordinateSelector multiplier
  let sourceMonomial := varMono (4 * block + component)
  let targetMonomial := reindexQuaternionExponents
    (identityQuaternionBlockInvolution (tailBlocks + 1)) sourceMonomial
  have hparity : selectedExponentParity (4 * (tailBlocks + 1)) selector
      targetMonomial =
      selectedExponentParity (4 * (tailBlocks + 1)) selector
        sourceMonomial := by
    exact identityReindex_polyVar_selectedExponentParity
      (tailBlocks + 1) (4 * block + component) selector
  generalize hsourceParity :
    selectedExponentParity (4 * (tailBlocks + 1)) selector
      sourceMonomial = parity
  have htargetParity :
      selectedExponentParity (4 * (tailBlocks + 1)) selector
        targetMonomial = parity := hparity.trans hsourceParity
  have hinner : RatPolyCoeffEqv
      (applySelectedTranslationSteps hblocks [directStep]
        (conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
          (polyVar (4 * block + component))))
      (conjugateQuaternionBlockPolynomial (tailBlocks + 1) multiplier
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution (tailBlocks + 1))
          (polyVar (4 * block + component)))) := by
    cases parity
    · simpa [conjugateQuaternionBlockPolynomial,
        signSelectedPolynomial, signSelectedTerm,
        reindexQuaternionPolynomial, polyVar,
        selector, sourceMonomial, targetMonomial,
        hsourceParity, htargetParity] using hbase
    · have hnegative := RatPolyCoeffEqv.trans
          (applySelectedTranslationSteps_neg hblocks [directStep]
            (polyVar (4 * block + component)))
          (RatPolyCoeffEqv.neg hbase)
      simpa [conjugateQuaternionBlockPolynomial,
        signSelectedPolynomial, signSelectedTerm,
        reindexQuaternionPolynomial, polyVar,
        polyNeg, selector, sourceMonomial, targetMonomial,
        hsourceParity, htargetParity] using hnegative
  exact RatPolyCoeffEqv.trans
    (conjugateQuaternionBlockPolynomial_coeffEqv
      (tailBlocks + 1) multiplier hinner)
    (conjugateQuaternionBlockPolynomial_involutive
      (tailBlocks + 1) multiplier
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (polyVar (4 * block + component))))

private theorem applySelectedTranslationStep_inverse_coordinate_of_ne_selected
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (block : Nat) (hblock : block < tailBlocks + 1)
    (hblockNe : block ≠ step.selected)
    (horientation : step.multiplierOrientation =
      SelectedMultiplierOrientation.inverse) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks [step]
        (PolyQuaternion.coordinateVariable block))
      (reindexPolyQuaternion
        (identityQuaternionBlockInvolution (tailBlocks + 1))
        (PolyQuaternion.coordinateVariable block)) := by
  let directStep : SelectedTranslationStep tailBlocks :=
    { selected := step.selected
      multiplier := step.multiplier
      selected_lt := step.selected_lt
      multiplier_lt := step.multiplier_lt
      distinct := step.distinct
      side := step.side
      multiplierOrientation := SelectedMultiplierOrientation.direct }
  have hdirect :=
    applySelectedTranslationStep_direct_coordinate_of_ne_selected
      hblocks directStep block hblock hblockNe rfl
  have hinverseComponent : ∀ component, component < 4 →
      RatPolyCoeffEqv
        (applySelectedTranslationSteps hblocks [step]
          (polyVar (4 * block + component)))
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution (tailBlocks + 1))
          (polyVar (4 * block + component))) := by
    intro component hcomponent
    have hbase : RatPolyCoeffEqv
        (applySelectedTranslationSteps hblocks [directStep]
          (polyVar (4 * block + component)))
        (reindexQuaternionPolynomial
          (identityQuaternionBlockInvolution (tailBlocks + 1))
          (polyVar (4 * block + component))) := by
      have hcases : component = 0 ∨ component = 1 ∨
          component = 2 ∨ component = 3 := by omega
      rcases hcases with hzero | hone | htwo | hthree
      · subst component
        simpa only [applySelectedTranslationStepsQuaternion,
          PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
            hdirect.scalar
      · subst component
        simpa only [applySelectedTranslationStepsQuaternion,
          PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
            hdirect.iPart
      · subst component
        simpa only [applySelectedTranslationStepsQuaternion,
          PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
            hdirect.jPart
      · subst component
        simpa only [applySelectedTranslationStepsQuaternion,
          PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
            hdirect.kPart
    have hconjugated := inverseConjugatedDirectPolyVar_of_base
      hblocks directStep step.multiplier block component hbase
    cases hside : step.side with
    | left =>
        simpa [applySelectedTranslationSteps, applySelectedTranslationStep,
          hside, horientation, directStep,
          selectedLeftInverseTranslatedPolynomial] using hconjugated
    | right =>
        simpa [applySelectedTranslationSteps, applySelectedTranslationStep,
          hside, horientation, directStep,
          selectedRightInverseTranslatedPolynomial] using hconjugated
  exact ⟨
    by simpa [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
        hinverseComponent 0 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
        hinverseComponent 1 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
        hinverseComponent 2 (by omega),
    by simpa [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.coordinateVariable, reindexPolyQuaternion] using
        hinverseComponent 3 (by omega)⟩

private theorem translatedHeadPolynomial_polyVar_of_four_le
    (translated : PolyQuaternion) (coordinate : Nat)
    (hcoordinate : 4 ≤ coordinate) :
    translatedHeadPolynomial translated (polyVar coordinate) =
      polyVar coordinate := by
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_add_of_le hcoordinate
  rw [Nat.add_comm 4 tail]
  simp [translatedHeadPolynomial, translatedHeadTerm,
    translatedHeadMonomial, ratPolyPow, headTailLiftTerm,
    polyVar, polyAdd, polyMul, polyOne, polyZero, exponentAt,
    YMGap.Continuum.RingNormaliser.varMono,
    YMGap.Continuum.RingNormaliser.monoMul, List.drop_append,
    List.replicate] <;> decide

def selectedTranslationStepRaw
    (step : SelectedTranslationStep 31) : RawSelectedTranslationStep where
  selected := step.selected
  multiplier := step.multiplier
  side := step.side
  multiplierOrientation := step.multiplierOrientation

private theorem rawSelectedTranslationStep_ext
    {left right : RawSelectedTranslationStep}
    (hselected : left.selected = right.selected)
    (hmultiplier : left.multiplier = right.multiplier)
    (hside : left.side = right.side)
    (horientation : left.multiplierOrientation =
      right.multiplierOrientation) :
    left = right := by
  cases left with
  | mk leftSelected leftMultiplier leftSide leftOrientation =>
      cases right with
      | mk rightSelected rightMultiplier rightSide rightOrientation =>
          cases hselected
          cases hmultiplier
          cases hside
          cases horientation
          rfl

private theorem selectedTranslationStep_ext
    {left right : SelectedTranslationStep 31}
    (hselected : left.selected = right.selected)
    (hmultiplier : left.multiplier = right.multiplier)
    (hside : left.side = right.side)
    (horientation : left.multiplierOrientation =
      right.multiplierOrientation) :
    left = right := by
  cases left with
  | mk leftSelected leftMultiplier leftSelectedLt leftMultiplierLt
      leftDistinct leftSide leftOrientation =>
      cases right with
      | mk rightSelected rightMultiplier rightSelectedLt rightMultiplierLt
          rightDistinct rightSide rightOrientation =>
          cases hselected
          cases hmultiplier
          cases hside
          cases horientation
          rfl

theorem selectedTranslationStepRaw_valid
    (step : SelectedTranslationStep 31) :
    rawSelectedTranslationStepValid 31
      (selectedTranslationStepRaw step) = true := by
  apply decide_eq_true
  exact ⟨step.selected_lt, step.multiplier_lt, step.distinct⟩

theorem selectedTranslationStepRaw_certify
    (step : SelectedTranslationStep 31)
    (hvalid : rawSelectedTranslationStepValid 31
      (selectedTranslationStepRaw step) = true) :
    (selectedTranslationStepRaw step).certify hvalid = step := by
  cases step
  rfl

private theorem encodedSelectedTranslationSideBit
    (selected multiplier side orientation : Nat)
    (hlow : selected + 32 * multiplier < 1024) :
    (selected + 32 * (multiplier + 32 * (side + 2 * orientation))) /
        1024 % 2 = side % 2 := by
  have hcode :
      selected + 32 * (multiplier + 32 * (side + 2 * orientation)) =
        (selected + 32 * multiplier) +
          1024 * (side + 2 * orientation) := by
    omega
  rw [hcode]
  have hdiv :
      ((selected + 32 * multiplier) +
          1024 * (side + 2 * orientation)) / 1024 =
        side + 2 * orientation := by
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hlow]
  rw [hdiv, Nat.add_mul_mod_self_left]

private theorem encodedSelectedMultiplierOrientationBit
    (selected multiplier side orientation : Nat)
    (hlow : selected + 32 * multiplier < 1024)
    (hside : side < 2) (horientation : orientation < 2) :
    (selected + 32 * (multiplier + 32 * (side + 2 * orientation))) /
        2048 % 2 = orientation := by
  have hlow' :
      selected + 32 * multiplier + 1024 * side < 2048 := by
    omega
  have hcode :
      selected + 32 * (multiplier + 32 * (side + 2 * orientation)) =
        (selected + 32 * multiplier + 1024 * side) +
          2048 * orientation := by
    omega
  rw [hcode]
  have hdiv :
      ((selected + 32 * multiplier + 1024 * side) +
          2048 * orientation) / 2048 = orientation := by
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hlow']
  rw [hdiv, Nat.mod_eq_of_lt horientation]

theorem decodeRawSelectedTranslationStep_selectedTranslationStepCode
    (step : SelectedTranslationStep 31) :
    decodeRawSelectedTranslationStep (selectedTranslationStepCode step) =
      selectedTranslationStepRaw step := by
  cases step with
  | mk selected multiplier selected_lt multiplier_lt distinct side orientation =>
      have hlow : selected + 32 * multiplier < 1024 := by
        omega
      apply rawSelectedTranslationStep_ext
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt selected_lt]
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hdiv :
            (selected + 32 * (multiplier + 32 *
              (selectedTranslationSideCode side +
                2 * selectedMultiplierOrientationCode orientation))) / 32 =
              multiplier + 32 * (selectedTranslationSideCode side +
                2 * selectedMultiplierOrientationCode orientation) := by
          simpa [Nat.add_mul_div_left,
            Nat.div_eq_of_lt selected_lt]
        rw [hdiv, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt multiplier_lt]
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hbit := encodedSelectedTranslationSideBit
          selected multiplier (selectedTranslationSideCode side)
            (selectedMultiplierOrientationCode orientation) hlow
        simp only [hbit]
        cases side <;> rfl
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hside : selectedTranslationSideCode side < 2 := by
          cases side <;> decide
        have horientation :
            selectedMultiplierOrientationCode orientation < 2 := by
          cases orientation <;> decide
        have hbit := encodedSelectedMultiplierOrientationBit
          selected multiplier (selectedTranslationSideCode side)
            (selectedMultiplierOrientationCode orientation)
              hlow hside horientation
        simp only [hbit]
        cases orientation <;> rfl

theorem decodeRawSelectedTranslationStep_certify_stepCode
    (step : SelectedTranslationStep 31)
    (hvalid : rawSelectedTranslationStepValid 31
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)) = true) :
    (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).certify hvalid = step := by
  have hdecode :=
    decodeRawSelectedTranslationStep_selectedTranslationStepCode step
  apply selectedTranslationStep_ext
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).selected = step.selected
    exact congrArg RawSelectedTranslationStep.selected hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).multiplier = step.multiplier
    exact congrArg RawSelectedTranslationStep.multiplier hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).side = step.side
    exact congrArg RawSelectedTranslationStep.side hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).multiplierOrientation =
        step.multiplierOrientation
    exact congrArg RawSelectedTranslationStep.multiplierOrientation hdecode

theorem decodedSelectedTranslationStepCoordinateCheck_stepCode
    (step : SelectedTranslationStep 31) :
    decodedSelectedTranslationStepCoordinateCheck
        (selectedTranslationStepCode step) =
      selectedTranslationStepCoordinateCheck
        (by decide : 0 < 31) step step.selected := by
  have hdecode :=
    decodeRawSelectedTranslationStep_selectedTranslationStepCode step
  have hvalid : rawSelectedTranslationStepValid 31
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)) = true := by
    rw [hdecode]
    exact selectedTranslationStepRaw_valid step
  unfold decodedSelectedTranslationStepCoordinateCheck
  rw [dif_pos hvalid]
  have hcertify :
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)).certify hvalid = step := by
    exact decodeRawSelectedTranslationStep_certify_stepCode step hvalid
  rw [hcertify]

theorem surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask) :
    selectedTranslationStepCoordinateCheck
      (by decide : 0 < 31) step step.selected = true := by
  have hcoverage :=
    binarySurfaceForestGaugeStepUniverseCoverageCheck_true
  unfold binarySurfaceForestGaugeStepUniverseCoverageCheck at hcoverage
  let maskEntry : { candidate // candidate ∈ binarySurfaceMasks } :=
    ⟨mask, hmask⟩
  have hmaskRow := List.all_eq_true.mp hcoverage maskEntry
    (List.mem_attach _ maskEntry)
  have hcodeDecision := List.all_eq_true.mp hmaskRow step hstep
  have hcode : selectedTranslationStepCode step ∈
      surfaceForestGaugeStepUniverseCodes :=
    of_decide_eq_true hcodeDecision
  have huniverse := surfaceForestGaugeStepUniverseCoordinateCheck_true
  unfold surfaceForestGaugeStepUniverseCoordinateCheck at huniverse
  have hdecoded := List.all_eq_true.mp huniverse
    (selectedTranslationStepCode step) hcode
  rw [decodedSelectedTranslationStepCoordinateCheck_stepCode] at hdecoded
  exact hdecoded

theorem surfaceForestGaugeLedgerStepSelectedCoordinate_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        [step] (orientedCoordinateQuaternion step.selected false))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          (selectedTranslationStepForwardWord step step.selected))) := by
  exact polyQuaternionCanonicalCoeffCheck_sound
    (surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
      mask hmask step hstep)

private theorem reindexPolyQuaternion_coeffEqv
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {left right : PolyQuaternion}
    (heqv : PolyQuaternionCoeffEqv left right) :
    PolyQuaternionCoeffEqv
      (reindexPolyQuaternion permutation left)
      (reindexPolyQuaternion permutation right) :=
  ⟨RatPolyCoeffEqv.reindex permutation heqv.scalar,
    RatPolyCoeffEqv.reindex permutation heqv.iPart,
    RatPolyCoeffEqv.reindex permutation heqv.jPart,
    RatPolyCoeffEqv.reindex permutation heqv.kPart⟩

private theorem compactOrientedQuaternionWord_singleton_forward
    (block : Nat) :
    PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord [(block, false)])
      (PolyQuaternion.coordinateVariable block) := by
  exact PolyQuaternionCoeffEqv.trans
    (compactOrientedQuaternionWord_coeffEqv_product [(block, false)])
    (by simpa [orientedSurfaceWordProduct, orientedCoordinateQuaternion] using
      (PolyQuaternionCoeffEqv.mul_one
        (PolyQuaternion.coordinateVariable block)))

private def twoQuaternionEnvironmentLocal
    (left right : PolyQuaternion) : Nat → RatPoly
  | 0 => left.scalar
  | 1 => left.iPart
  | 2 => left.jPart
  | 3 => left.kPart
  | 4 => right.scalar
  | 5 => right.iPart
  | 6 => right.jPart
  | 7 => right.kPart
  | _ => polyZero

private def exprConjMulLocal : PolyQuaternionExpr :=
  PolyQuaternionExpr.conj
    (PolyQuaternionExpr.mul
      (PolyQuaternionExpr.coordinate 0)
      (PolyQuaternionExpr.coordinate 4))

private def exprMulConjReverseLocal : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))

private theorem exprConjMulReverseLocal_normal :
    normalize exprConjMulLocal.scalar =
        normalize exprMulConjReverseLocal.scalar ∧
      normalize exprConjMulLocal.iPart =
        normalize exprMulConjReverseLocal.iPart ∧
      normalize exprConjMulLocal.jPart =
        normalize exprMulConjReverseLocal.jPart ∧
      normalize exprConjMulLocal.kPart =
        normalize exprMulConjReverseLocal.kPart := by
  decide

private theorem polyQuaternion_conj_mul_reverse_coeffEqv
    (left right : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.conj (PolyQuaternion.mul left right))
      (PolyQuaternion.mul
        (PolyQuaternion.conj right) (PolyQuaternion.conj left)) := by
  let environment := twoQuaternionEnvironmentLocal left right
  constructor
  · simpa [environment, exprConjMulLocal, exprMulConjReverseLocal,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, coeffEvalExpr,
      twoQuaternionEnvironmentLocal, PolyQuaternion.mul,
      PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulLocal.scalar exprMulConjReverseLocal.scalar
        exprConjMulReverseLocal_normal.1 environment)
  · simpa [environment, exprConjMulLocal, exprMulConjReverseLocal,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, coeffEvalExpr,
      twoQuaternionEnvironmentLocal, PolyQuaternion.mul,
      PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulLocal.iPart exprMulConjReverseLocal.iPart
        exprConjMulReverseLocal_normal.2.1 environment)
  · simpa [environment, exprConjMulLocal, exprMulConjReverseLocal,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, coeffEvalExpr,
      twoQuaternionEnvironmentLocal, PolyQuaternion.mul,
      PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulLocal.jPart exprMulConjReverseLocal.jPart
        exprConjMulReverseLocal_normal.2.2.1 environment)
  · simpa [environment, exprConjMulLocal, exprMulConjReverseLocal,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, coeffEvalExpr,
      twoQuaternionEnvironmentLocal, PolyQuaternion.mul,
      PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulLocal.kPart exprMulConjReverseLocal.kPart
        exprConjMulReverseLocal_normal.2.2.2 environment)

private def exprConjConjLocal : PolyQuaternionExpr :=
  PolyQuaternionExpr.conj
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))

private theorem exprConjConjLocal_normal :
    normalize exprConjConjLocal.scalar =
        normalize (PolyQuaternionExpr.coordinate 0).scalar ∧
      normalize exprConjConjLocal.iPart =
        normalize (PolyQuaternionExpr.coordinate 0).iPart ∧
      normalize exprConjConjLocal.jPart =
        normalize (PolyQuaternionExpr.coordinate 0).jPart ∧
      normalize exprConjConjLocal.kPart =
        normalize (PolyQuaternionExpr.coordinate 0).kPart := by
  decide

private theorem polyQuaternion_conj_conj_coeffEqv
    (quaternion : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.conj (PolyQuaternion.conj quaternion)) quaternion := by
  let environment := twoQuaternionEnvironmentLocal quaternion quaternion
  constructor
  · simpa [environment, exprConjConjLocal,
      PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, twoQuaternionEnvironmentLocal, PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjConjLocal.scalar (PolyQuaternionExpr.coordinate 0).scalar
        exprConjConjLocal_normal.1 environment)
  · simpa [environment, exprConjConjLocal,
      PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, twoQuaternionEnvironmentLocal, PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjConjLocal.iPart (PolyQuaternionExpr.coordinate 0).iPart
        exprConjConjLocal_normal.2.1 environment)
  · simpa [environment, exprConjConjLocal,
      PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, twoQuaternionEnvironmentLocal, PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjConjLocal.jPart (PolyQuaternionExpr.coordinate 0).jPart
        exprConjConjLocal_normal.2.2.1 environment)
  · simpa [environment, exprConjConjLocal,
      PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, twoQuaternionEnvironmentLocal, PolyQuaternion.conj] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjConjLocal.kPart (PolyQuaternionExpr.coordinate 0).kPart
        exprConjConjLocal_normal.2.2.2 environment)

private theorem orientedCoordinateQuaternion_not_coeffEqv
    (entry : OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (orientedCoordinateQuaternion entry.1 (!entry.2))
      (PolyQuaternion.conj
        (orientedCoordinateQuaternion entry.1 entry.2)) := by
  cases entry with
  | mk block reverse =>
      cases reverse with
      | false => exact PolyQuaternionCoeffEqv.refl _
      | true =>
          simpa [orientedCoordinateQuaternion] using
            (PolyQuaternionCoeffEqv.symm
              (polyQuaternion_conj_conj_coeffEqv
                (PolyQuaternion.coordinateVariable block)))

private theorem orientedSurfaceWordProduct_inverse_coeffEqv :
    ∀ word : List OrientedSurfaceEdge,
    PolyQuaternionCoeffEqv
      (orientedSurfaceWordProduct (inverseSurfaceWord word))
      (PolyQuaternion.conj (orientedSurfaceWordProduct word))
  | [] => by
      exact PolyQuaternionCoeffEqv.refl _
  | entry :: rest => by
      have happend := orientedSurfaceWordProduct_append
        (inverseSurfaceWord rest) [(entry.1, !entry.2)]
      have hrest := orientedSurfaceWordProduct_inverse_coeffEqv rest
      have hentry : PolyQuaternionCoeffEqv
          (orientedSurfaceWordProduct [(entry.1, !entry.2)])
          (PolyQuaternion.conj
            (orientedCoordinateQuaternion entry.1 entry.2)) := by
        exact PolyQuaternionCoeffEqv.trans
          (by simpa [orientedSurfaceWordProduct] using
            (PolyQuaternionCoeffEqv.mul_one
              (orientedCoordinateQuaternion entry.1 (!entry.2))))
          (orientedCoordinateQuaternion_not_coeffEqv entry)
      exact PolyQuaternionCoeffEqv.trans
        (by simpa [inverseSurfaceWord] using happend)
        (PolyQuaternionCoeffEqv.trans
          (PolyQuaternionCoeffEqv.mul hrest hentry)
          (PolyQuaternionCoeffEqv.symm
            (polyQuaternion_conj_mul_reverse_coeffEqv
              (orientedCoordinateQuaternion entry.1 entry.2)
              (orientedSurfaceWordProduct rest))))

private theorem compactOrientedQuaternionWord_inverse_coeffEqv
    (word : List OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord (inverseSurfaceWord word))
      (PolyQuaternion.conj (compactOrientedQuaternionWord word)) := by
  exact PolyQuaternionCoeffEqv.trans
    (compactOrientedQuaternionWord_coeffEqv_product
      (inverseSurfaceWord word))
    (PolyQuaternionCoeffEqv.trans
      (orientedSurfaceWordProduct_inverse_coeffEqv word)
      (PolyQuaternionCoeffEqv.conj
        (PolyQuaternionCoeffEqv.symm
          (compactOrientedQuaternionWord_coeffEqv_product word))))

/-- Every forward coordinate action of an actual surface-forest ledger step
has the word substitution prescribed by that step.  The selected-coordinate
case is discharged by the finite certificate; all 31 untouched coordinates
are proved structurally. -/
theorem surfaceForestGaugeLedgerStepForwardCoordinate_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask)
    (block : Nat) (hblock : block < 32) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        [step] (orientedCoordinateQuaternion block false))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          (selectedTranslationStepForwardWord step block))) := by
  by_cases hselected : block = step.selected
  · subst block
    exact surfaceForestGaugeLedgerStepSelectedCoordinate_coeffEqv
      mask hmask step hstep
  · have hcompact : PolyQuaternionCoeffEqv
        (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
          (compactOrientedQuaternionWord [(block, false)]))
        (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
          (PolyQuaternion.coordinateVariable block)) :=
      reindexPolyQuaternion_coeffEqv
        (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord_singleton_forward block)
    have hfixed : PolyQuaternionCoeffEqv
        (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
          [step] (PolyQuaternion.coordinateVariable block))
        (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
          (PolyQuaternion.coordinateVariable block)) := by
      cases horientation : step.multiplierOrientation with
      | direct =>
          exact applySelectedTranslationStep_direct_coordinate_of_ne_selected
            (by decide : 0 < 31) step block hblock hselected horientation
      | inverse =>
          exact applySelectedTranslationStep_inverse_coordinate_of_ne_selected
            (by decide : 0 < 31) step block hblock hselected horientation
    exact PolyQuaternionCoeffEqv.trans
      (by simpa [orientedCoordinateQuaternion] using hfixed)
      (by simpa [selectedTranslationStepForwardWord, hselected] using
        hcompact.symm)

/-- The oriented word produced by one selected-pair ledger step. -/
def selectedTranslationStepOrientedWord
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) (reverse : Bool) : List OrientedSurfaceEdge :=
  if reverse then
    inverseSurfaceWord (selectedTranslationStepForwardWord step block)
  else selectedTranslationStepForwardWord step block

/-- The forward-coordinate ledger theorem commutes with orientation
reversal, so one actual surface-forest step acts correctly on either edge
orientation. -/
theorem surfaceForestGaugeLedgerStepOrientedCoordinate_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask)
    (block : Nat) (hblock : block < 32) (reverse : Bool) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        [step] (orientedCoordinateQuaternion block reverse))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          (selectedTranslationStepOrientedWord step block reverse))) := by
  cases reverse with
  | false =>
      simpa [selectedTranslationStepOrientedWord] using
        (surfaceForestGaugeLedgerStepForwardCoordinate_coeffEqv
          mask hmask step hstep block hblock)
  | true =>
      let word := selectedTranslationStepForwardWord step block
      have hforward :=
        surfaceForestGaugeLedgerStepForwardCoordinate_coeffEqv
          mask hmask step hstep block hblock
      have hconj := PolyQuaternionCoeffEqv.conj hforward
      have happly := applySelectedTranslationStepsQuaternion_conj
        (by decide : 0 < 31) [step]
        (PolyQuaternion.coordinateVariable block)
      have hinverse := reindexPolyQuaternion_coeffEqv
        (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord_inverse_coeffEqv word)
      rw [reindexPolyQuaternion_conj] at hinverse
      exact PolyQuaternionCoeffEqv.trans
        (by simpa [orientedCoordinateQuaternion] using happly)
        (PolyQuaternionCoeffEqv.trans hconj
          (by simpa [selectedTranslationStepOrientedWord, word] using
            hinverse.symm))

private theorem compactOrientedQuaternionWord_singleton
    (entry : OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord [entry])
      (orientedCoordinateQuaternion entry.1 entry.2) := by
  exact PolyQuaternionCoeffEqv.trans
    (compactOrientedQuaternionWord_coeffEqv_product [entry])
    (by simpa [orientedSurfaceWordProduct] using
      (PolyQuaternionCoeffEqv.mul_one
        (orientedCoordinateQuaternion entry.1 entry.2)))

private theorem compactOrientedQuaternionWord_append_coeffEqv
    (left right : List OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord (left ++ right))
      (PolyQuaternion.mul
        (compactOrientedQuaternionWord left)
        (compactOrientedQuaternionWord right)) := by
  exact PolyQuaternionCoeffEqv.trans
    (compactOrientedQuaternionWord_coeffEqv_product (left ++ right))
    (PolyQuaternionCoeffEqv.trans
      (orientedSurfaceWordProduct_append left right)
      (PolyQuaternionCoeffEqv.mul
        (PolyQuaternionCoeffEqv.symm
          (compactOrientedQuaternionWord_coeffEqv_product left))
        (PolyQuaternionCoeffEqv.symm
          (compactOrientedQuaternionWord_coeffEqv_product right))))

/-- Substitute one selected-pair ledger step into every letter of an oriented
word. -/
def applySelectedTranslationStepWord
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (word : List OrientedSurfaceEdge) : List OrientedSurfaceEdge :=
  word.flatMap fun entry =>
    selectedTranslationStepOrientedWord step entry.1 entry.2

private theorem selectedTranslationStepOrientedWord_nonempty
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) (reverse : Bool) :
    selectedTranslationStepOrientedWord step block reverse ≠ [] := by
  cases reverse <;>
    cases hside : step.side <;>
    cases horientation : step.multiplierOrientation <;>
    by_cases hselected : block = step.selected <;>
    simp [selectedTranslationStepOrientedWord,
      selectedTranslationStepForwardWord, inverseSurfaceWord,
      hside, horientation, hselected]

private theorem selectedTranslationStepOrientedWord_block_lt
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) (hblock : block < tailBlocks + 1) (reverse : Bool) :
    ∀ entry, entry ∈ selectedTranslationStepOrientedWord step block reverse →
      entry.1 < tailBlocks + 1 := by
  intro entry hentry
  cases reverse <;>
    cases hside : step.side <;>
    cases horientation : step.multiplierOrientation <;>
    by_cases hselected : block = step.selected <;>
    simp_all [selectedTranslationStepOrientedWord,
      selectedTranslationStepForwardWord, inverseSurfaceWord]
  all_goals
    rcases hentry with hentry | hentry <;>
      subst entry <;> simp only
  all_goals first
    | exact step.multiplier_lt
    | exact step.selected_lt
    | exact hblock

private theorem applySelectedTranslationStepWord_nonempty
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    {word : List OrientedSurfaceEdge} (hword : word ≠ []) :
    applySelectedTranslationStepWord step word ≠ [] := by
  cases word with
  | nil => exact False.elim (hword rfl)
  | cons entry rest =>
      simp only [applySelectedTranslationStepWord, List.flatMap_cons]
      exact (List.append_ne_nil_of_left_ne_nil
        (selectedTranslationStepOrientedWord_nonempty
          step entry.1 entry.2)) _

private theorem applySelectedTranslationStepWord_block_lt
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (word : List OrientedSurfaceEdge)
    (hword : ∀ entry, entry ∈ word → entry.1 < tailBlocks + 1) :
    ∀ entry, entry ∈ applySelectedTranslationStepWord step word →
      entry.1 < tailBlocks + 1 := by
  intro entry hentry
  unfold applySelectedTranslationStepWord at hentry
  obtain ⟨source, hsource, hentry⟩ := List.mem_flatMap.mp hentry
  exact selectedTranslationStepOrientedWord_block_lt step source.1
    (hword source hsource) source.2 entry hentry

private theorem surfaceForestGaugeLedgerStepWord_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask) :
    ∀ word : List OrientedSurfaceEdge, word ≠ [] →
      (∀ entry, entry ∈ word → entry.1 < 32) →
      PolyQuaternionCoeffEqv
        (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
          [step] (compactOrientedQuaternionWord word))
        (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
          (compactOrientedQuaternionWord
            (applySelectedTranslationStepWord step word))) := by
  intro word hnonempty hbound
  induction word with
  | nil => exact False.elim (hnonempty rfl)
  | cons entry rest induction =>
      cases rest with
      | nil =>
          have hentryBound : entry.1 < 32 :=
            hbound entry List.mem_cons_self
          exact PolyQuaternionCoeffEqv.trans
            (applySelectedTranslationStepsQuaternion_coeffEqv
              (by decide : 0 < 31) [step]
              (compactOrientedQuaternionWord_singleton entry))
            (by simpa [applySelectedTranslationStepWord] using
              (surfaceForestGaugeLedgerStepOrientedCoordinate_coeffEqv
                mask hmask step hstep entry.1 hentryBound entry.2))
      | cons next tail =>
          let remaining : List OrientedSurfaceEdge := next :: tail
          have hentryBound : entry.1 < 32 :=
            hbound entry List.mem_cons_self
          have hremainingBound : ∀ candidate, candidate ∈ remaining →
              candidate.1 < 32 := by
            intro candidate hcandidate
            exact hbound candidate (List.mem_cons_of_mem entry hcandidate)
          have hremaining := induction (by simp [remaining]) hremainingBound
          have hsplit := compactOrientedQuaternionWord_append_coeffEqv
            [entry] remaining
          have happlySplit :=
            applySelectedTranslationStepsQuaternion_coeffEqv
              (by decide : 0 < 31) [step] hsplit
          have hmul := applySelectedTranslationStepsQuaternion_mul
            (by decide : 0 < 31) [step]
            (compactOrientedQuaternionWord [entry])
            (compactOrientedQuaternionWord remaining)
          have hentryAction := PolyQuaternionCoeffEqv.trans
            (applySelectedTranslationStepsQuaternion_coeffEqv
              (by decide : 0 < 31) [step]
              (compactOrientedQuaternionWord_singleton entry))
            (surfaceForestGaugeLedgerStepOrientedCoordinate_coeffEqv
              mask hmask step hstep entry.1 hentryBound entry.2)
          have hparts := PolyQuaternionCoeffEqv.mul hentryAction hremaining
          have htargetSplit := compactOrientedQuaternionWord_append_coeffEqv
            (selectedTranslationStepOrientedWord step entry.1 entry.2)
            (applySelectedTranslationStepWord step remaining)
          have hreindexedTarget := reindexPolyQuaternion_coeffEqv
            (identityQuaternionBlockInvolution 32) htargetSplit
          rw [reindexPolyQuaternion_mul] at hreindexedTarget
          exact PolyQuaternionCoeffEqv.trans
            (by simpa [remaining] using happlySplit)
            (PolyQuaternionCoeffEqv.trans hmul
              (PolyQuaternionCoeffEqv.trans hparts
                (by simpa [applySelectedTranslationStepWord, remaining] using
                  hreindexedTarget.symm)))

/-- Iterated word substitution in the same left-to-right order as the
selected-pair polynomial translation chain. -/
def applySelectedTranslationStepsWord
    {tailBlocks : Nat} :
    List (SelectedTranslationStep tailBlocks) →
      List OrientedSurfaceEdge → List OrientedSurfaceEdge
  | [], word => word
  | step :: rest, word =>
      applySelectedTranslationStepsWord rest
        (applySelectedTranslationStepWord step word)

private theorem applySelectedTranslationStepsQuaternion_identityReindex_nonempty
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)), steps ≠ [] →
      ∀ quaternion : PolyQuaternion,
      PolyQuaternionCoeffEqv
        (applySelectedTranslationStepsQuaternion hblocks steps
          (reindexPolyQuaternion
            (identityQuaternionBlockInvolution (tailBlocks + 1)) quaternion))
        (applySelectedTranslationStepsQuaternion hblocks steps quaternion)
  | [], hnonempty, _ => False.elim (hnonempty rfl)
  | step :: rest, _, quaternion => by
      have hfirst :=
        applySelectedTranslationStepQuaternion_identityReindex_coeffEqv
          hblocks step quaternion
      exact applySelectedTranslationStepsQuaternion_coeffEqv
        hblocks rest hfirst

private theorem surfaceForestGaugeLedgerStepsWord_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    ∀ (steps : List (SelectedTranslationStep 31)), steps ≠ [] →
      (∀ step, step ∈ steps →
        step ∈ surfaceForestGaugeTranslationSteps mask hmask) →
      ∀ word : List OrientedSurfaceEdge, word ≠ [] →
      (∀ entry, entry ∈ word → entry.1 < 32) →
      PolyQuaternionCoeffEqv
        (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
          steps (compactOrientedQuaternionWord word))
        (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
          (compactOrientedQuaternionWord
            (applySelectedTranslationStepsWord steps word))) := by
  intro steps hstepsNonempty hsteps word hwordNonempty hwordBound
  cases steps with
  | nil => exact False.elim (hstepsNonempty rfl)
  | cons step rest =>
      cases rest with
      | nil =>
          simpa [applySelectedTranslationStepsWord] using
            (surfaceForestGaugeLedgerStepWord_coeffEqv
              mask hmask step (hsteps step List.mem_cons_self)
              word hwordNonempty hwordBound)
      | cons next tail =>
          let remainingSteps : List (SelectedTranslationStep 31) := next :: tail
          let nextWord := applySelectedTranslationStepWord step word
          have hfirst := surfaceForestGaugeLedgerStepWord_coeffEqv
            mask hmask step (hsteps step List.mem_cons_self)
            word hwordNonempty hwordBound
          have hfirstUnderRest :=
            applySelectedTranslationStepsQuaternion_coeffEqv
              (by decide : 0 < 31) remainingSteps hfirst
          have hpadding :=
            applySelectedTranslationStepsQuaternion_identityReindex_nonempty
              (by decide : 0 < 31) remainingSteps (by simp [remainingSteps])
              (compactOrientedQuaternionWord nextWord)
          have hrest := surfaceForestGaugeLedgerStepsWord_coeffEqv
            mask hmask remainingSteps (by simp [remainingSteps])
            (fun candidate hcandidate =>
              hsteps candidate (List.mem_cons_of_mem step hcandidate))
            nextWord
            (applySelectedTranslationStepWord_nonempty step hwordNonempty)
            (applySelectedTranslationStepWord_block_lt step word hwordBound)
          exact PolyQuaternionCoeffEqv.trans hfirstUnderRest
            (PolyQuaternionCoeffEqv.trans hpadding
              (by simpa [applySelectedTranslationStepsWord,
                  remainingSteps, nextWord] using hrest))

/-- Executable word-level join between the dependent translation ledger and
the independently defined rooted-path gauge substitution.  This check never
constructs or canonicalizes a polynomial. -/
def surfaceForestGaugeLedgerWordRowCheck
    (maskEntry : {candidate // candidate ∈ binarySurfaceMasks}) : Bool :=
  if maskEntry.1 = 0 then true else
    decide (surfaceForestGaugeTranslationSteps
      maskEntry.1 maskEntry.2 ≠ []) &&
    (List.range 32).all fun edgeId =>
      [false, true].all fun reverse =>
        decide
          (applySelectedTranslationStepsWord
              (surfaceForestGaugeTranslationSteps
                maskEntry.1 maskEntry.2)
              [(surfaceActiveBlock edgeId, reverse)] =
            (substituteSurfaceGaugeEntry
              maskEntry.1 (edgeId, reverse)).map fun substituted =>
                (surfaceActiveBlock substituted.1, substituted.2))

def binarySurfaceForestGaugeLedgerWordCheck : Bool :=
  binarySurfaceMasks.attach.all surfaceForestGaugeLedgerWordRowCheck

private theorem surfaceForestGaugeTranslationSteps_nonempty
    (hcheck : binarySurfaceForestGaugeLedgerWordCheck = true)
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    surfaceForestGaugeTranslationSteps mask hmask ≠ [] := by
  have hrow := List.all_eq_true.mp
    hcheck
    ⟨mask, hmask⟩ (List.mem_attach _ ⟨mask, hmask⟩)
  simp only [surfaceForestGaugeLedgerWordRowCheck, hnonzero,
    if_false, Bool.and_eq_true] at hrow
  exact of_decide_eq_true hrow.1

private theorem surfaceForestGaugeLedgerWord_eq_substitution
    (hcheck : binarySurfaceForestGaugeLedgerWordCheck = true)
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (edgeId : Nat) (hedgeId : edgeId < 32)
    (reverse : Bool) :
    applySelectedTranslationStepsWord
        (surfaceForestGaugeTranslationSteps mask hmask)
        [(surfaceActiveBlock edgeId, reverse)] =
      (substituteSurfaceGaugeEntry mask (edgeId, reverse)).map
        fun substituted =>
          (surfaceActiveBlock substituted.1, substituted.2) := by
  have hrow := List.all_eq_true.mp
    hcheck
    ⟨mask, hmask⟩ (List.mem_attach _ ⟨mask, hmask⟩)
  simp only [surfaceForestGaugeLedgerWordRowCheck, hnonzero,
    if_false, Bool.and_eq_true] at hrow
  have hedgeRow := List.all_eq_true.mp hrow.2 edgeId
    (List.mem_range.mpr hedgeId)
  have horientation := List.all_eq_true.mp hedgeRow reverse (by
    cases reverse <;> simp)
  exact of_decide_eq_true horientation

def surfaceActiveBlockRangeCheck : Bool :=
  (List.range 32).all fun edgeId => decide (surfaceActiveBlock edgeId < 32)

theorem surfaceActiveBlockRangeCheck_true :
    surfaceActiveBlockRangeCheck = true := by
  decide

theorem surfaceActiveBlock_lt_of_lt
    (edgeId : Nat) (hedgeId : edgeId < 32) :
    surfaceActiveBlock edgeId < 32 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp surfaceActiveBlockRangeCheck_true edgeId
      (List.mem_range.mpr hedgeId))

/-- The full actual surface ledger sends either orientation of every physical
edge coordinate to the rooted-path substituted word. -/
theorem surfaceForestGaugeLedgerCoordinateSemantic_coeffEqv_of_wordCheck
    (hcheck : binarySurfaceForestGaugeLedgerWordCheck = true)
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (edgeId : Nat) (hedgeId : edgeId < 32)
    (reverse : Bool) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        (surfaceForestGaugeTranslationSteps mask hmask)
        (orientedCoordinateQuaternion
          (surfaceActiveBlock edgeId) reverse))
      (paddedSubstitutedSurfaceGaugeEntryQuaternion
        mask (edgeId, reverse)) := by
  let steps := surfaceForestGaugeTranslationSteps mask hmask
  let sourceWord : List OrientedSurfaceEdge :=
    [(surfaceActiveBlock edgeId, reverse)]
  have hchain := surfaceForestGaugeLedgerStepsWord_coeffEqv
    mask hmask steps
    (surfaceForestGaugeTranslationSteps_nonempty
      hcheck mask hmask hnonzero)
    (fun step hstep => hstep)
    sourceWord (by simp [sourceWord])
    (fun entry hentry => by
      have hentryEq : entry = (surfaceActiveBlock edgeId, reverse) := by
        simpa [sourceWord] using hentry
      subst entry
      exact surfaceActiveBlock_lt_of_lt edgeId hedgeId)
  have hsource := applySelectedTranslationStepsQuaternion_coeffEqv
    (by decide : 0 < 31) steps
    (compactOrientedQuaternionWord_singleton
      (surfaceActiveBlock edgeId, reverse))
  exact PolyQuaternionCoeffEqv.trans
    (by simpa [steps] using hsource.symm)
    (PolyQuaternionCoeffEqv.trans hchain (by
      rw [surfaceForestGaugeLedgerWord_eq_substitution
        hcheck mask hmask hnonzero edgeId hedgeId reverse]
      exact PolyQuaternionCoeffEqv.refl _))

/-! ## Selected-face word compiler -/

/-- One literal compact face word expressed in the 32-block active-carrier
order on which the selected-pair translation ledger acts. -/
def surfaceActiveFaceWord (faceId : Nat) : List OrientedSurfaceEdge :=
  (hypercubeFaceWords.getD faceId []).map fun entry =>
    (surfaceActiveBlock entry.1, entry.2)

/-- Executable join between the iterated ledger word compiler and the
rooted-path substitution on every selected face.  The source nonemptiness and
block bounds are carried in the same row so the structural theorem below has
no hidden geometry hypotheses. -/
def surfaceForestGaugeLedgerFaceWordRowCheck
    (maskEntry : {candidate // candidate ∈ binarySurfaceMasks}) : Bool :=
  if maskEntry.1 = 0 then true else
    (surfaceSelectedCompactFaceIds maskEntry.1).all fun faceId =>
      decide (surfaceActiveFaceWord faceId ≠ []) &&
      (surfaceActiveFaceWord faceId).all fun entry =>
        decide (entry.1 < 32) &&
          decide
            (applySelectedTranslationStepsWord
                (surfaceForestGaugeTranslationSteps
                  maskEntry.1 maskEntry.2)
                (surfaceActiveFaceWord faceId) =
              (substituteSurfaceGaugeWord maskEntry.1
                (hypercubeFaceWords.getD faceId [])).map fun substituted =>
                  (surfaceActiveBlock substituted.1, substituted.2))

def binarySurfaceForestGaugeLedgerFaceWordCheck : Bool :=
  binarySurfaceMasks.attach.all surfaceForestGaugeLedgerFaceWordRowCheck

/-- The complete actual ledger sends the active-carrier holonomy of every
selected face to the padded rooted-path-substituted holonomy.  This theorem
is entirely structural after the two finite word certificates are supplied. -/
theorem surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv_of_checks
    (hwordCheck : binarySurfaceForestGaugeLedgerWordCheck = true)
    (hfaceCheck : binarySurfaceForestGaugeLedgerFaceWordCheck = true)
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (faceId : Nat)
    (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        (surfaceForestGaugeTranslationSteps mask hmask)
        (compactOrientedQuaternionWord
          (surfaceActiveFaceWord faceId)))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          ((substituteSurfaceGaugeWord mask
            (hypercubeFaceWords.getD faceId [])).map fun substituted =>
              (surfaceActiveBlock substituted.1, substituted.2)))) := by
  have hmaskRow := List.all_eq_true.mp hfaceCheck
    ⟨mask, hmask⟩ (List.mem_attach _ ⟨mask, hmask⟩)
  simp only [surfaceForestGaugeLedgerFaceWordRowCheck, hnonzero,
    if_false] at hmaskRow
  have hfaceRow := List.all_eq_true.mp hmaskRow faceId hface
  simp only [Bool.and_eq_true] at hfaceRow
  have hsourceNonempty : surfaceActiveFaceWord faceId ≠ [] :=
    of_decide_eq_true hfaceRow.1
  have hsourceBound : ∀ entry, entry ∈ surfaceActiveFaceWord faceId →
      entry.1 < 32 := by
    intro entry hentry
    have hentryRow := List.all_eq_true.mp hfaceRow.2 entry hentry
    have hentryParts : decide (entry.1 < 32) = true ∧
        decide
          (applySelectedTranslationStepsWord
              (surfaceForestGaugeTranslationSteps mask hmask)
              (surfaceActiveFaceWord faceId) =
            (substituteSurfaceGaugeWord mask
              (hypercubeFaceWords.getD faceId [])).map fun substituted =>
                (surfaceActiveBlock substituted.1, substituted.2)) = true := by
      simpa only [Bool.and_eq_true] using hentryRow
    exact of_decide_eq_true hentryParts.1
  have hcompiled :
      applySelectedTranslationStepsWord
          (surfaceForestGaugeTranslationSteps mask hmask)
          (surfaceActiveFaceWord faceId) =
        (substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId [])).map fun substituted =>
            (surfaceActiveBlock substituted.1, substituted.2) := by
    have hentry := List.all_eq_true.mp hfaceRow.2
    cases hsource : surfaceActiveFaceWord faceId with
    | nil => exact False.elim (hsourceNonempty hsource)
    | cons first rest =>
        have hfirstRow := hentry first (by simp [hsource])
        have hfirstParts : decide (first.1 < 32) = true ∧
            decide
              (applySelectedTranslationStepsWord
                  (surfaceForestGaugeTranslationSteps mask hmask)
                  (surfaceActiveFaceWord faceId) =
                (substituteSurfaceGaugeWord mask
                  (hypercubeFaceWords.getD faceId [])).map fun substituted =>
                    (surfaceActiveBlock substituted.1, substituted.2)) =
              true := by
          simpa only [Bool.and_eq_true] using hfirstRow
        have horiginal :
            applySelectedTranslationStepsWord
                (surfaceForestGaugeTranslationSteps mask hmask)
                (surfaceActiveFaceWord faceId) =
              (substituteSurfaceGaugeWord mask
                (hypercubeFaceWords.getD faceId [])).map fun substituted =>
                  (surfaceActiveBlock substituted.1, substituted.2) :=
          of_decide_eq_true hfirstParts.2
        simpa [hsource] using horiginal
  have hchain := surfaceForestGaugeLedgerStepsWord_coeffEqv
    mask hmask (surfaceForestGaugeTranslationSteps mask hmask)
    (surfaceForestGaugeTranslationSteps_nonempty
      hwordCheck mask hmask hnonzero)
    (fun step hstep => hstep)
    (surfaceActiveFaceWord faceId) hsourceNonempty hsourceBound
  rw [hcompiled] at hchain
  exact hchain

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodeRawSelectedTranslationStep_selectedTranslationStepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodeRawSelectedTranslationStep_certify_stepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.selectedTranslationStepRaw_valid
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.selectedTranslationStepRaw_certify
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodedSelectedTranslationStepCoordinateCheck_stepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepSelectedCoordinate_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepForwardCoordinate_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepOrientedCoordinate_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceActiveBlockRangeCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerCoordinateSemantic_coeffEqv_of_wordCheck
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv_of_checks
