/-
# Conditional projection under an explicit block recoding

The selected-pair heat factor already has a finite Haar recoding.  The
remaining algebraic seam before a local head-map estimate is to transport
the conditional projection through the same block involutions.  This file
proves that transport on the raw polynomial carrier, retaining all spectator
coordinates and all coefficient data.

These are finite coordinate identities only.  They do not supply a
multi-factor angular telescope, an interacting endpoint estimate, an OS gap,
or a continuum limit.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockProjection
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.SU2QuaternionSelectedProjectionReindex

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem block_index_eq
    (a b remainder : Nat) (hremainder : remainder < 4)
    (hleft : 4 * a ≤ 4 * b + remainder)
    (hright : 4 * b + remainder < 4 * a + 4) :
    a = b := by
  omega

/-! ## 1. The coordinate mask commutes with a block involution -/

private theorem coordinateIn_reindex_iff
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected coordinate : Nat) (hselected : selected < blocks)
    (hcoordinate : coordinate < 4 * blocks) :
    coordinateInQuaternionBlock selected
        (4 * s.map (coordinate / 4) + coordinate % 4) ↔
      coordinateInQuaternionBlock (s.map selected) coordinate := by
  have hdecomp : 4 * (coordinate / 4) + coordinate % 4 = coordinate :=
    Nat.div_add_mod coordinate 4
  have hblock : coordinate / 4 < blocks := by
    apply Nat.lt_of_not_ge
    intro hle
    have hmul : 4 * blocks ≤ 4 * (coordinate / 4) :=
      Nat.mul_le_mul_left 4 hle
    have hbound : 4 * blocks ≤ coordinate :=
      Nat.le_trans hmul (by
        calc
          4 * (coordinate / 4) ≤ 4 * (coordinate / 4) + coordinate % 4 :=
            Nat.le_add_right _ _
          _ = coordinate := hdecomp)
    exact (Nat.not_le_of_lt hcoordinate) hbound
  have hcomponent : coordinate % 4 < 4 := Nat.mod_lt _ (by decide)
  constructor
  · intro h
    unfold coordinateInQuaternionBlock at h ⊢
    have hmap : selected = s.map (coordinate / 4) := by
      apply block_index_eq selected (s.map (coordinate / 4))
        (coordinate % 4) hcomponent
      · exact h.1
      · exact h.2
    have hsource : s.map selected = coordinate / 4 := by
      rw [hmap, s.involutive (coordinate / 4) hblock]
    rw [hsource]
    exact ⟨by
      calc
        4 * (coordinate / 4) ≤ 4 * (coordinate / 4) + coordinate % 4 :=
          Nat.le_add_right _ _
        _ = coordinate := hdecomp,
      by
        calc
          coordinate = 4 * (coordinate / 4) + coordinate % 4 := hdecomp.symm
          _ < 4 * (coordinate / 4) + 4 :=
            Nat.add_lt_add_left hcomponent _⟩
  · intro h
    unfold coordinateInQuaternionBlock at h ⊢
    have hdecomp := Nat.div_add_mod coordinate 4
    have hmap : s.map selected = coordinate / 4 := by
      apply block_index_eq (s.map selected) (coordinate / 4)
        (coordinate % 4) hcomponent
      · calc
          4 * s.map selected ≤ coordinate := h.1
          _ = 4 * (coordinate / 4) + coordinate % 4 := hdecomp.symm
      · calc
          4 * (coordinate / 4) + coordinate % 4 = coordinate := hdecomp
          _ < 4 * s.map selected + 4 := h.2
    have hsource : selected = s.map (coordinate / 4) := by
      have hinvolutive := s.involutive selected hselected
      rw [hmap] at hinvolutive
      exact hinvolutive.symm
    rw [hsource]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hcomponent _⟩

private theorem reindex_clear_exponents
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks)
    (monomial : List Nat) :
    reindexQuaternionExponents s (clearQuaternionBlock selected monomial) =
      clearQuaternionBlock (s.map selected)
        (reindexQuaternionExponents s monomial) := by
  apply natList_eq_of_length_getD
  · rw [reindexQuaternionExponents_length, clearQuaternionBlock_length,
      reindexQuaternionExponents_length]
  · intro coordinate hcoordinate
    have hcoordinate' : coordinate < 4 * blocks := by
      simpa only [reindexQuaternionExponents_length] using hcoordinate
    change exponentAt
        (reindexQuaternionExponents s (clearQuaternionBlock selected monomial))
        coordinate =
      exponentAt
        (clearQuaternionBlock (s.map selected)
          (reindexQuaternionExponents s monomial)) coordinate
    rw [exponentAt_reindexQuaternionExponents s
      (clearQuaternionBlock selected monomial) hcoordinate',
      exponentAt_clearQuaternionBlock]
    rw [exponentAt_clearQuaternionBlock,
      exponentAt_reindexQuaternionExponents s monomial hcoordinate']
    by_cases hmask :
        coordinateInQuaternionBlock selected
          (4 * s.map (coordinate / 4) + coordinate % 4)
    · have htarget := (coordinateIn_reindex_iff s selected coordinate
          hselected hcoordinate').mp hmask
      simp only [hmask, htarget]
    · have htarget : ¬ coordinateInQuaternionBlock (s.map selected) coordinate := by
        intro htarget
        exact hmask ((coordinateIn_reindex_iff s selected coordinate
          hselected hcoordinate').mpr htarget)
      simp only [hmask, htarget]

/-! ## 2. Partial integration commutes with the recoding -/

private theorem reindex_integrateQuaternionBlock_termwise
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks) :
    ∀ polynomial : RatPoly,
      RatPolyTermwiseEqv
        (reindexQuaternionPolynomial s
          (integrateQuaternionBlock selected polynomial))
        (integrateQuaternionBlock (s.map selected)
          (reindexQuaternionPolynomial s polynomial))
  | [] => by
      simp only [integrateQuaternionBlock, reindexQuaternionPolynomial,
        List.map_nil]
      exact RatPolyTermwiseEqv.refl []
  | term :: rest => by
      rcases term with ⟨monomial, coefficient⟩
      refine ⟨?_, ?_, ?_⟩
      · exact reindex_clear_exponents s selected hselected monomial
      · have hm := quaternionBlockMoment_reindex s monomial
          (block := s.map selected) (s.map_lt selected hselected)
        rw [s.involutive selected hselected] at hm
        change coefficient *
            SU2QuaternionArbitraryHaarBlockReflection.quaternionBlockMoment
              monomial selected ≈
          coefficient *
            SU2QuaternionArbitraryHaarBlockReflection.quaternionBlockMoment
              (reindexQuaternionExponents s monomial) (s.map selected)
        exact Q'.mul_eqv_congr_left coefficient _ _ (Q'.eqv_of_eq hm.symm)
      · exact reindex_integrateQuaternionBlock_termwise s selected
          hselected rest

private theorem ratWeightedSum_reindex
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (weight : List Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum weight
        (reindexQuaternionPolynomial s polynomial) ≈
      ratWeightedSum
        (fun monomial => weight
          (reindexQuaternionExponents s monomial)) polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        term.2 * weight (reindexQuaternionExponents s term.1) +
            ratWeightedSum weight
              (reindexQuaternionPolynomial s rest) ≈
          term.2 * weight (reindexQuaternionExponents s term.1) +
            ratWeightedSum
              (fun monomial => weight
                (reindexQuaternionExponents s monomial)) rest
      exact Q'.add_eqv_congr_left _ _ _
        (ratWeightedSum_reindex s weight rest)

private theorem reindex_coeff
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial s left)
      (reindexQuaternionPolynomial s right) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    weight (reindexQuaternionExponents s monomial)
  exact Q'.eqv_trans _ _ _
    (ratWeightedSum_reindex s weight left)
    (Q'.eqv_trans _ _ _
      (heqv transformed)
      (Q'.eqv_symm (ratWeightedSum_reindex s weight right)))

theorem reindex_integrateQuaternionBlock
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks) :
    ∀ polynomial : RatPoly,
      RatPolyCoeffEqv
        (reindexQuaternionPolynomial s
          (integrateQuaternionBlock selected polynomial))
        (integrateQuaternionBlock (s.map selected)
          (reindexQuaternionPolynomial s polynomial))
  | polynomial =>
      fun weight =>
        ratWeightedSum_termwise_eqv weight
          (reindex_integrateQuaternionBlock_termwise
            s selected hselected polynomial)

/-! ## 3. The selected pair becomes the literal head projection -/

theorem exposeTranslationPair_project
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    (hdistinct : selected ≠ multiplier) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial
        (translationPairTailPermutation blocks selected multiplier
          hblocks hselected hmultiplier)
      (reindexQuaternionPolynomial
        (translationPairHeadPermutation blocks selected hselected)
        (project selected polynomial)))
      (project 0
        (exposeTranslationPairPolynomial blocks selected multiplier
          hblocks hselected hmultiplier polynomial)) := by
  let head := translationPairHeadPermutation blocks selected hselected
  let tail := translationPairTailPermutation blocks selected multiplier
    hblocks hselected hmultiplier
  have hhead := reindex_integrateQuaternionBlock head selected hselected polynomial
  have htail := reindex_integrateQuaternionBlock tail 0
    (by omega : 0 < blocks)
      (reindexQuaternionPolynomial head polynomial)
  have hheadZero : head.map selected = 0 := by
    exact headSwapBlockInvolution_map_selected blocks selected hselected
  have htailZero : tail.map 0 = 0 := by
    exact translationPairTailPermutation_map_zero blocks selected multiplier
      hblocks hselected hmultiplier hdistinct
  have hhead' := reindex_coeff tail hhead
  have hfirst :
      RatPolyCoeffEqv
        (reindexQuaternionPolynomial tail
          (reindexQuaternionPolynomial head (project selected polynomial)))
        (reindexQuaternionPolynomial tail
          (project 0 (reindexQuaternionPolynomial head polynomial))) := by
    simpa only [project, hheadZero] using hhead'
  have hsecond :
      RatPolyCoeffEqv
        (reindexQuaternionPolynomial tail
          (project 0 (reindexQuaternionPolynomial head polynomial)))
        (project 0
          (exposeTranslationPairPolynomial blocks selected multiplier
            hblocks hselected hmultiplier polynomial)) := by
    simpa only [project, exposeTranslationPairPolynomial, htailZero] using htail
  exact hfirst.trans hsecond

/-! ## 4. Haar-carrier consequences -/

/-- The coefficient-level projection transport is immediately consumable by
the full finite quaternion Haar functional.  No support or positivity premise
is added: this is only the existing coefficient-probe elimination rule. -/
theorem reindex_project_haar
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks)
    (polynomial : RatPoly) :
    quaternionHaar blocks
        (reindexQuaternionPolynomial s (project selected polynomial)) ≈
      quaternionHaar blocks
        (project (s.map selected)
          (reindexQuaternionPolynomial s polynomial)) := by
  exact haar_of_coeff
    (reindex_integrateQuaternionBlock s selected hselected polynomial)

/-- The same transport remains valid with an arbitrary right insertion, so it
can be used directly under a finite pairing before any support specialization.
-/
theorem reindex_project_pairing
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks)
    (polynomial test : RatPoly) :
    quaternionHaar blocks
        (polyMul
          (reindexQuaternionPolynomial s (project selected polynomial)) test) ≈
      quaternionHaar blocks
        (polyMul
          (project (s.map selected)
            (reindexQuaternionPolynomial s polynomial)) test) := by
  exact haar_of_coeff
    ((reindex_integrateQuaternionBlock s selected hselected polynomial).mul_right test)

/-- A supported original pairing can be moved to the recoded selected block.
The support hypotheses belong only to the existing Haar change-of-variables
theorem; the projection transport itself remains coefficient-level. -/
theorem reindex_project_pairing_carrier
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (selected : Nat) (hselected : selected < blocks)
    (polynomial test : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial)
    (htest : SupportedQuaternionBlocks blocks test) :
    quaternionHaar blocks
        (polyMul (project selected polynomial) test) ≈
      quaternionHaar blocks
        (polyMul
          (project (s.map selected)
            (reindexQuaternionPolynomial s polynomial))
          (reindexQuaternionPolynomial s test)) := by
  have hchange := quaternionHaar_reindex s
    (polyMul (project selected polynomial) test)
    (supported_polyMul (project_supported selected hpolynomial) htest)
  rw [reindexQuaternionPolynomial_mul] at hchange
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hchange)
    (reindex_project_pairing s selected hselected polynomial
      (reindexQuaternionPolynomial s test))

end YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
