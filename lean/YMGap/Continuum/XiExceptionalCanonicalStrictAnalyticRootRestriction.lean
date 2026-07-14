/-
# Source-root restriction and a strict analytic payment fence

Every genuine exceptional source is rooted at the marked right occurrence.
The right source family is pointwise `!b2`, so that root cannot itself carry
`b2`.  The ambient strict canonical tree majorant forgot this invariant.

This module restores the source-root gate, factors the resulting finite
relaxation, and proves that it still dominates the complete exceptional
source.  A closed two-occurrence calculation also refutes the unreduced
analytic payment into the accepted connecting-chain budget: the old relaxed
product is `45/32` while the accepted budget is `21/16`.  In that example the
exceptional source is empty and the root-restricted tree majorant is zero,
pinpointing the exact unreachable stratum responsible for the failure.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryAll

namespace YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryAll

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## The invariant retained by every genuine source -/

theorem entryRootAttachmentTree_root_b2_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    b2 (polyAt Gamma
      (entryRootAttachmentCarrierCode
        Gamma qP b1 b2 entry).tree.root) = false := by
  let facts := exceptionalSourceFactsOfMem
    Gamma qP b1 b2 entry.1 entry.2
  change b2 (polyAt Gamma
    (exceptionalMarkedIndex Gamma b1 b2 entry.1)) = false
  exact facts.right_good _ facts.marked_right_true

def sourceRootStrictTreeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) : Q' :=
  if !(b2 (polyAt Gamma code.root)) then
    strictRootAttachmentTreeWeight w Gamma qP b1 b2 label code
  else 0

def sourceRootStrictTreeMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum (sourceRootStrictTreeWeight w Gamma qP b1 b2 label)
    (rootAttachmentTreeCodes Gamma.length Gamma.length)

theorem entry_sourceRootStrictTreeWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    sourceRootStrictTreeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree =
      strictRootAttachmentTreeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree := by
  unfold sourceRootStrictTreeWeight
  rw [entryRootAttachmentTree_root_b2_false Gamma qP b1 b2 entry]
  rfl

theorem sourceRootStrictTreeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) :
    (0 : Q') ≤ sourceRootStrictTreeWeight
      w Gamma qP b1 b2 label code := by
  unfold sourceRootStrictTreeWeight
  split
  · exact strictRootAttachmentTreeWeight_nonnegative
      hw Gamma qP b1 b2 label code
  · exact Q'.le_refl' _

/-! ## Source-root carrier and its independent finite relaxation -/

def sourceRootStrictCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) : Q' :=
  if rootAttachmentBackgroundValidB
      Gamma qP code.tree code.background then
    (sourceRootStrictTreeWeight w Gamma qP b1 b2 label code.tree *
      familyActivity w (selectByBits Gamma code.background) label) *
        admissibleFamilyWeight w qP label
          (selectByBits Gamma code.external)
  else 0

def sourceRootStrictRelaxedCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) : Q' :=
  (sourceRootStrictTreeWeight w Gamma qP b1 b2 label code.tree *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.background)) *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.external)

def sourceRootStrictRelaxedCarrierMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum
    (sourceRootStrictRelaxedCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (rootAttachmentCarrierCodes Gamma.length Gamma.length)

theorem entry_sourceRootStrictCarrierCodeWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    sourceRootStrictCarrierCodeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry) =
      strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry) := by
  unfold sourceRootStrictCarrierCodeWeight
    strictRootAttachmentCarrierCodeWeight
  rw [entry_sourceRootStrictTreeWeight_eq w Gamma qP b1 b2 label entry]

theorem sourceRootStrictCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ sourceRootStrictCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold sourceRootStrictCarrierCodeWeight
  split
  · exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (sourceRootStrictTreeWeight_nonnegative
          hw Gamma qP b1 b2 label code.tree)
        (familyActivity_nonneg hw
          (selectByBits Gamma code.background) label))
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.external))
  · exact Q'.le_refl' _

theorem sourceRootStrictRelaxedCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ sourceRootStrictRelaxedCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold sourceRootStrictRelaxedCarrierCodeWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (sourceRootStrictTreeWeight_nonnegative
        hw Gamma qP b1 b2 label code.tree)
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.background)))
    (admissibleFamilyWeight_nonnegative hw qP label
      (selectByBits Gamma code.external))

theorem sourceRootStrictCarrierCodeWeight_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    sourceRootStrictCarrierCodeWeight w Gamma qP b1 b2 label code ≤
      sourceRootStrictRelaxedCarrierCodeWeight
        w Gamma qP b1 b2 label code := by
  unfold sourceRootStrictCarrierCodeWeight
  split
  next hvalid =>
    have hgate :
        ((selectByBits Gamma code.background).all qP &&
          familyCompatibleB (selectByBits Gamma code.background)) = true := by
      unfold rootAttachmentBackgroundValidB at hvalid
      dsimp only at hvalid
      cases hq : (selectByBits Gamma code.background).all qP <;>
        cases hc : familyCompatibleB
          (selectByBits Gamma code.background) <;> simp_all
    unfold sourceRootStrictRelaxedCarrierCodeWeight
      admissibleFamilyWeight
    simp only [hgate, if_true]
    exact Q'.le_refl' _
  next _ =>
    exact sourceRootStrictRelaxedCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code

private theorem qListSum_le_pointwise (f g : a → Q') :
    ∀ xs : List a, (∀ x, x ∈ xs → f x ≤ g x) →
      qListSum f xs ≤ qListSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => by
      apply Q'.add_le_add
      · exact h x List.mem_cons_self
      · exact qListSum_le_pointwise f g xs
          (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem sourceRootStrictCarrierMajorant_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (sourceRootStrictCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) ≤
      sourceRootStrictRelaxedCarrierMajorant
        w Gamma qP b1 b2 label := by
  apply qListSum_le_pointwise
  intro code _
  exact sourceRootStrictCarrierCodeWeight_le_relaxed
    hw Gamma qP b1 b2 label code

/-! ## Exact factorization of the source-root relaxation -/

theorem sourceRootStrictRelaxedCarrierMajorant_eqv
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    sourceRootStrictRelaxedCarrierMajorant w Gamma qP b1 b2 label ≈
      (sourceRootStrictTreeMajorant w Gamma qP b1 b2 label *
        XiR w qP Gamma label) * XiR w qP Gamma label := by
  have hcodes : rootAttachmentCarrierCodes Gamma.length Gamma.length =
      (rootAttachmentTreeCodes Gamma.length Gamma.length).flatMap
        (fun tree => (bitVectors Gamma.length).flatMap (fun background =>
          (bitVectors Gamma.length).map (fun external =>
            RootAttachmentCarrierCode.mk tree background external))) := by
    unfold rootAttachmentCarrierCodes maskPairs
    simp only [List.map_flatMap, List.map_map]
    rfl
  unfold sourceRootStrictRelaxedCarrierMajorant
  rw [hcodes]
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap
      (sourceRootStrictRelaxedCarrierCodeWeight
        w Gamma qP b1 b2 label)
      (fun tree => (bitVectors Gamma.length).flatMap (fun background =>
        (bitVectors Gamma.length).map (fun external =>
          RootAttachmentCarrierCode.mk tree background external)))
      (rootAttachmentTreeCodes Gamma.length Gamma.length)) ?_
  have hexternal : ∀ tree background,
      qListSum
          (sourceRootStrictRelaxedCarrierCodeWeight
            w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).map (fun external =>
            RootAttachmentCarrierCode.mk tree background external)) ≈
        (sourceRootStrictTreeWeight w Gamma qP b1 b2 label tree *
          admissibleFamilyWeight w qP label
            (selectByBits Gamma background)) * XiR w qP Gamma label := by
    intro tree background
    rw [qListSum_map]
    unfold sourceRootStrictRelaxedCarrierCodeWeight
    refine Q'.eqv_trans _ _ _
      (qListSum_const_mul
        (sourceRootStrictTreeWeight w Gamma qP b1 b2 label tree *
          admissibleFamilyWeight w qP label
            (selectByBits Gamma background))
        (fun external => admissibleFamilyWeight w qP label
          (selectByBits Gamma external))
        (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (admissibleFamilyWeight_bitVectors_eqv_XiR
        w qP Gamma label)
  have hbackground : ∀ tree,
      qListSum
          (sourceRootStrictRelaxedCarrierCodeWeight
            w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).flatMap (fun background =>
            (bitVectors Gamma.length).map (fun external =>
              RootAttachmentCarrierCode.mk tree background external))) ≈
        (sourceRootStrictTreeWeight w Gamma qP b1 b2 label tree *
          XiR w qP Gamma label) * XiR w qP Gamma label := by
    intro tree
    refine Q'.eqv_trans _ _ _
      (qListSum_flatMap
        (sourceRootStrictRelaxedCarrierCodeWeight
          w Gamma qP b1 b2 label)
        (fun background => (bitVectors Gamma.length).map (fun external =>
          RootAttachmentCarrierCode.mk tree background external))
        (bitVectors Gamma.length)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_eqv_congr _ _ (bitVectors Gamma.length)
        (fun background _ => hexternal tree background)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (fun background =>
          sourceRootStrictTreeWeight w Gamma qP b1 b2 label tree *
            admissibleFamilyWeight w qP label
              (selectByBits Gamma background))
        (XiR w qP Gamma label) (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (qListSum_const_mul
          (sourceRootStrictTreeWeight w Gamma qP b1 b2 label tree)
          (fun background => admissibleFamilyWeight w qP label
            (selectByBits Gamma background))
          (bitVectors Gamma.length))
        (Q'.mul_eqv_congr_left _ _ _
          (admissibleFamilyWeight_bitVectors_eqv_XiR
            w qP Gamma label)))
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr _ _
      (rootAttachmentTreeCodes Gamma.length Gamma.length)
      (fun tree _ => hbackground tree)) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_mul_const
      (fun tree => sourceRootStrictTreeWeight
        w Gamma qP b1 b2 label tree * XiR w qP Gamma label)
      (XiR w qP Gamma label)
      (rootAttachmentTreeCodes Gamma.length Gamma.length)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (sourceRootStrictTreeWeight w Gamma qP b1 b2 label)
        (XiR w qP Gamma label)
        (rootAttachmentTreeCodes Gamma.length Gamma.length))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _)))

/-! ## The complete source is dominated by the root-restricted envelope -/

theorem fullExceptionalSource_sum_le_sourceRootStrictCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight
          w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) ≤
      qListSum
        (sourceRootStrictCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) := by
  apply qListSum_le_of_injective
    (fullExceptionalSource Gamma qP b1 b2)
    (rootAttachmentCarrierCodes Gamma.length Gamma.length)
    (fun entry => occurrencePairWeight
      w qP b1 b2 Gamma label entry.1)
    (sourceRootStrictCarrierCodeWeight w Gamma qP b1 b2 label)
    (entryRootAttachmentCarrierCode Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
  · intro entry _
    exact entryRootAttachmentCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact entryRootAttachmentCarrierCode_injective_all
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro entry _
    rw [entry_sourceRootStrictCarrierCodeWeight_eq
      w Gamma qP b1 b2 label entry]
    exact Q'.ge_of_eqv
      (entryRootAttachmentCarrierCode_strict_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact sourceRootStrictCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code

theorem exceptionalSourceCodes_sum_le_sourceRootStrictTree_mul_XiR_sq
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      (sourceRootStrictTreeMajorant w Gamma qP b1 b2 label *
        XiR w qP Gamma label) * XiR w qP Gamma label := by
  rw [← fullExceptionalSource_weight_eq]
  exact Q'.le_trans' _ _ _
    (fullExceptionalSource_sum_le_sourceRootStrictCarrier
      hw Gamma qP b1 b2 label)
    (Q'.le_trans' _ _ _
      (sourceRootStrictCarrierMajorant_le_relaxed
        hw Gamma qP b1 b2 label)
      (Q'.le_of_eqv
        (sourceRootStrictRelaxedCarrierMajorant_eqv
          w Gamma qP b1 b2 label)))

/-! ## Closed refutation of the old independent payment -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p : TL.Plaquette := (0, 0)
private def X : Polymer TL := [p]
private def Gamma2 : List (Polymer TL) := [X, X]
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def qAll : Polymer TL → Bool := fun _ => true
private def bAll : Polymer TL → Bool := fun _ => true
private def half : Q' := Q'.mkPos 1 2 (by decide)

set_option maxRecDepth 10000 in
theorem old_strict_tree_majorant_eqv_five_eighths :
    strictCanonicalRootAttachmentTreeMajorant
        half Gamma2 qAll bAll bAll labelOne ≈
      Q'.mkPos 5 8 (by decide) := by
  decide

theorem duplicate_XiR_eqv_three_halves :
    XiR half qAll Gamma2 labelOne ≈
      Q'.mkPos 3 2 (by decide) := by
  decide

set_option maxRecDepth 10000 in
theorem duplicate_chain_majorant_eqv_seven_eighths :
    connectingChainMajorant half qAll bAll bAll Gamma2 labelOne ≈
      Q'.mkPos 7 8 (by decide) := by
  decide

theorem duplicate_exceptional_source_empty :
    exceptionalSourceCodes Gamma2 qAll bAll bAll = [] := by
  decide

set_option maxRecDepth 10000 in
theorem source_root_strict_tree_majorant_eqv_zero :
    sourceRootStrictTreeMajorant
        half Gamma2 qAll bAll bAll labelOne ≈ 0 := by
  decide

set_option maxRecDepth 10000 in
theorem old_strict_tree_mul_XiR_not_le_chain :
    ¬ (strictCanonicalRootAttachmentTreeMajorant
          half Gamma2 qAll bAll bAll labelOne *
        XiR half qAll Gamma2 labelOne ≤
      connectingChainMajorant
        half qAll bAll bAll Gamma2 labelOne) := by
  decide

set_option maxRecDepth 10000 in
theorem old_relaxed_product_not_le_accepted_budget :
    ¬ ((strictCanonicalRootAttachmentTreeMajorant
          half Gamma2 qAll bAll bAll labelOne *
        XiR half qAll Gamma2 labelOne) *
          XiR half qAll Gamma2 labelOne ≤
      connectingChainMajorant half qAll bAll bAll Gamma2 labelOne *
        XiR half qAll Gamma2 labelOne) := by
  decide

#print axioms entryRootAttachmentTree_root_b2_false
#print axioms entry_sourceRootStrictTreeWeight_eq
#print axioms sourceRootStrictTreeWeight_nonnegative
#print axioms entry_sourceRootStrictCarrierCodeWeight_eq
#print axioms sourceRootStrictCarrierCodeWeight_le_relaxed
#print axioms sourceRootStrictRelaxedCarrierMajorant_eqv
#print axioms fullExceptionalSource_sum_le_sourceRootStrictCarrier
#print axioms exceptionalSourceCodes_sum_le_sourceRootStrictTree_mul_XiR_sq
#print axioms old_strict_tree_majorant_eqv_five_eighths
#print axioms duplicate_XiR_eqv_three_halves
#print axioms duplicate_chain_majorant_eqv_seven_eighths
#print axioms duplicate_exceptional_source_empty
#print axioms source_root_strict_tree_majorant_eqv_zero
#print axioms old_strict_tree_mul_XiR_not_le_chain
#print axioms old_relaxed_product_not_le_accepted_budget

end YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction
