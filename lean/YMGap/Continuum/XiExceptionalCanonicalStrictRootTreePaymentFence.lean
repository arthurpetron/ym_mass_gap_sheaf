/-
# Nonempty source-root tree-to-chain payment fence

The source-root gate removes trees whose root already carries `b2`, but it
does not yet characterize the image of two compatible source families.  This
closed three-polymer example has a nonempty exceptional source and disjoint
endpoint markers.  Five source-root-admissible canonical trees already have
enough total weight to violate the direct tree-times-`XiR` comparison with the
accepted connecting-chain majorant.

The four offending three-vertex trees cannot be covered by two compatible
occurrence masks: their polymers form a three-clique for incompatibility.
Thus the next invariant is a retained two-source-side compatibility/coloring
certificate, not another relaxation of the tree and family data.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction

namespace YMGap.Continuum.XiExceptionalCanonicalStrictRootTreePaymentFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction

local infix:50 " ≈ " => Q'.eqv

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)

/- All three polymers have two plaquette occurrences and activity `1/16` at
`w = 1/2`, but are distinct lists and pairwise incompatible. -/
private def X : Polymer TL := [p, q]
private def Y : Polymer TL := [q, p]
private def Z : Polymer TL := [p, p]
private def Gamma3 : List (Polymer TL) := [X, Y, Z]

private def qAll : Polymer TL → Bool := fun _ => true
private def bX : Polymer TL → Bool := fun T => decide (T = X)
private def bY : Polymer TL → Bool := fun T => decide (T = Y)
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def half : Q' := Q'.mkPos 1 2 (by decide)

/- One direct rooted edge and all four strict construction orders/parents for
adding the third occurrence. -/
private def witnessTrees :
    List (RootAttachmentTreeCode Gamma3.length) :=
  [⟨0, [(0, 1)]⟩,
   ⟨0, [(0, 1), (0, 2)]⟩,
   ⟨0, [(0, 1), (1, 2)]⟩,
   ⟨0, [(0, 2), (0, 1)]⟩,
   ⟨0, [(0, 2), (2, 1)]⟩]

theorem witnessTrees_nodup : witnessTrees.Nodup := by
  decide

theorem witnessTree_mem_ambient
    (code : RootAttachmentTreeCode Gamma3.length)
    (hcode : code ∈ witnessTrees) :
    code ∈ rootAttachmentTreeCodes Gamma3.length Gamma3.length := by
  simp only [witnessTrees, List.mem_cons, List.not_mem_nil, or_false] at hcode
  rcases hcode with hcode | hcode | hcode | hcode | hcode <;>
    subst code <;>
    apply RootAttachmentTreeCode.mem_rootAttachmentTreeCodes <;>
    decide

theorem witnessTrees_sum_le_sourceRootStrictTreeMajorant :
    qListSum
        (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
        witnessTrees ≤
      sourceRootStrictTreeMajorant half Gamma3 qAll bX bY labelOne := by
  unfold sourceRootStrictTreeMajorant
  apply qListSum_le_of_injective
    witnessTrees
    (rootAttachmentTreeCodes Gamma3.length Gamma3.length)
    (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
    (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
    (fun code => code)
    witnessTrees_nodup
  · intro code hcode
    exact witnessTree_mem_ambient code hcode
  · intro code _ code' _ h
    exact h
  · intro code _
    exact Q'.le_refl' _
  · intro code _
    exact sourceRootStrictTreeWeight_nonnegative
      (by decide) Gamma3 qAll bX bY labelOne code

set_option maxRecDepth 10000 in
theorem witnessTrees_sum_eqv_five_over_1024 :
    qListSum
        (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
        witnessTrees ≈
      Q'.mkPos 5 1024 (by decide) := by
  decide

theorem Gamma3_XiR_eqv_nineteen_over_16 :
    XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 19 16 (by decide) := by
  decide

set_option maxRecDepth 10000 in
theorem Gamma3_chain_eqv_313_over_65536 :
    connectingChainMajorant half qAll bX bY Gamma3 labelOne ≈
      Q'.mkPos 313 65536 (by decide) := by
  decide

/- This is a genuine exceptional configuration, unlike the old root-`b2`
fence whose exceptional source was empty. -/
theorem Gamma3_exceptional_source_nonempty :
    exceptionalSourceCodes Gamma3 qAll bX bY ≠ [] := by
  decide

/-! ## Exact failure of the refined direct payment -/

set_option maxRecDepth 10000 in
theorem witnessTrees_mul_XiR_eqv_95_over_16384 :
    qListSum
          (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
          witnessTrees *
        XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 95 16384 (by decide) := by
  decide

theorem sourceRootStrictTree_mul_XiR_not_le_chain :
    ¬ (sourceRootStrictTreeMajorant half Gamma3 qAll bX bY labelOne *
          XiR half qAll Gamma3 labelOne ≤
        connectingChainMajorant half qAll bX bY Gamma3 labelOne) := by
  intro hpayment
  have hxi : (0 : Q') ≤ XiR half qAll Gamma3 labelOne :=
    XiR_nonneg (by decide) qAll Gamma3 labelOne
  have hlower := Q'.mul_le_mul_of_nonneg_right
    (qListSum
      (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
      witnessTrees)
    (sourceRootStrictTreeMajorant half Gamma3 qAll bX bY labelOne)
    (XiR half qAll Gamma3 labelOne)
    witnessTrees_sum_le_sourceRootStrictTreeMajorant hxi
  have hclosed := Q'.le_trans' _ _ _ hlower hpayment
  have hnumeric :
      Q'.mkPos 95 16384 (by decide) ≤
        Q'.mkPos 313 65536 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv witnessTrees_mul_XiR_eqv_95_over_16384)
      (Q'.le_trans' _ _ _ hclosed
        (Q'.le_of_eqv Gamma3_chain_eqv_313_over_65536))
  exact (by decide : ¬ (Q'.mkPos 95 16384 (by decide) ≤
    Q'.mkPos 313 65536 (by decide))) hnumeric

set_option maxRecDepth 10000 in
theorem witnessTrees_mul_XiR_sq_eqv_1805_over_262144 :
    (qListSum
          (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
          witnessTrees *
        XiR half qAll Gamma3 labelOne) *
          XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 1805 262144 (by decide) := by
  decide

set_option maxRecDepth 10000 in
theorem Gamma3_chain_mul_XiR_eqv_5947_over_1048576 :
    connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 5947 1048576 (by decide) := by
  decide

theorem sourceRootStrictTree_XiR_sq_not_le_accepted_budget :
    ¬ ((sourceRootStrictTreeMajorant half Gamma3 qAll bX bY labelOne *
            XiR half qAll Gamma3 labelOne) *
          XiR half qAll Gamma3 labelOne ≤
        connectingChainMajorant half qAll bX bY Gamma3 labelOne *
          XiR half qAll Gamma3 labelOne) := by
  intro hpayment
  have hxi : (0 : Q') ≤ XiR half qAll Gamma3 labelOne :=
    XiR_nonneg (by decide) qAll Gamma3 labelOne
  have hlower1 := Q'.mul_le_mul_of_nonneg_right
    (qListSum
      (sourceRootStrictTreeWeight half Gamma3 qAll bX bY labelOne)
      witnessTrees)
    (sourceRootStrictTreeMajorant half Gamma3 qAll bX bY labelOne)
    (XiR half qAll Gamma3 labelOne)
    witnessTrees_sum_le_sourceRootStrictTreeMajorant hxi
  have hlower2 := Q'.mul_le_mul_of_nonneg_right _ _
    (XiR half qAll Gamma3 labelOne) hlower1 hxi
  have hclosed := Q'.le_trans' _ _ _ hlower2 hpayment
  have hnumeric :
      Q'.mkPos 1805 262144 (by decide) ≤
        Q'.mkPos 5947 1048576 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv witnessTrees_mul_XiR_sq_eqv_1805_over_262144)
      (Q'.le_trans' _ _ _ hclosed
        (Q'.le_of_eqv Gamma3_chain_mul_XiR_eqv_5947_over_1048576))
  exact (by decide : ¬ (Q'.mkPos 1805 262144 (by decide) ≤
    Q'.mkPos 5947 1048576 (by decide))) hnumeric

/-! ## The missing source-side compatibility certificate -/

def twoCompatibleMaskCoverB
    (Gamma : List (Polymer TL))
    (code : RootAttachmentTreeCode Gamma.length) : Bool :=
  (maskPairs Gamma.length).any (fun masks =>
    code.vertices.all (fun i => masks.1.at i || masks.2.at i) &&
      familyCompatibleB (selectByBits Gamma masks.1) &&
        familyCompatibleB (selectByBits Gamma masks.2))

theorem direct_witness_has_two_compatible_mask_cover :
    twoCompatibleMaskCoverB Gamma3 ⟨0, [(0, 1)]⟩ = true := by
  decide

theorem three_vertex_witnesses_have_no_two_compatible_mask_cover :
    (witnessTrees.drop 1).all
      (fun code => !(twoCompatibleMaskCoverB Gamma3 code)) = true := by
  decide

#print axioms witnessTrees_nodup
#print axioms witnessTree_mem_ambient
#print axioms witnessTrees_sum_le_sourceRootStrictTreeMajorant
#print axioms witnessTrees_sum_eqv_five_over_1024
#print axioms Gamma3_XiR_eqv_nineteen_over_16
#print axioms Gamma3_chain_eqv_313_over_65536
#print axioms Gamma3_exceptional_source_nonempty
#print axioms witnessTrees_mul_XiR_eqv_95_over_16384
#print axioms sourceRootStrictTree_mul_XiR_not_le_chain
#print axioms witnessTrees_mul_XiR_sq_eqv_1805_over_262144
#print axioms Gamma3_chain_mul_XiR_eqv_5947_over_1048576
#print axioms sourceRootStrictTree_XiR_sq_not_le_accepted_budget
#print axioms direct_witness_has_two_compatible_mask_cover
#print axioms three_vertex_witnesses_have_no_two_compatible_mask_cover

end YMGap.Continuum.XiExceptionalCanonicalStrictRootTreePaymentFence
