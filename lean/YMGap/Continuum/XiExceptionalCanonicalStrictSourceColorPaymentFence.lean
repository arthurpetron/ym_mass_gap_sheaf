/-
# Canonical source-color payment fence

The first-valid source coloring removes the Cartesian color multiplicity, but
the retained compatibility gate is not sufficient for analytic payment into
the existing connecting-chain budget.  This module first rechecks the
three-clique fence: every three-vertex carrier is killed by the canonical
color gate.  It then gives a smaller-mechanism obstruction on a three-vertex
star.

The star has one `b1` root and two mutually compatible leaves, one carrying
`b2`.  The gate accepts the direct tree, both ordered constructions of the
two-leaf tree, and every compatible external submask.  These fifteen distinct
payloads have total weight `39/1024`, whereas the existing
`connectingChainMajorant * XiR` budget is exactly `4745/131072`.  Thus a
successful successor gate must retain more than source-side two-colorability:
it must reject at least one of the explicit branch-order/role-multiplicity
witnesses below.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorPaymentFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical
open YMGap.Continuum.XiExceptionalTargetNodup

local infix:50 " ≈ " => Q'.eqv

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

private def zero3 : OccBitVec 3 := bits3 false false false
private def x3 : OccBitVec 3 := bits3 true false false
private def y3 : OccBitVec 3 := bits3 false true false
private def z3 : OccBitVec 3 := bits3 false false true
private def yz3 : OccBitVec 3 := bits3 false true true

private def qAll : Polymer TL → Bool := fun _ => true
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## The checked three-clique remains excluded -/

private def KX : Polymer TL := [p, q]
private def KY : Polymer TL := [q, p]
private def KZ : Polymer TL := [p, p]
private def KGamma : List (Polymer TL) := [KX, KY, KZ]

private def k3Trees : List (RootAttachmentTreeCode KGamma.length) :=
  [⟨0, [(0, 1), (0, 2)]⟩,
   ⟨0, [(0, 1), (1, 2)]⟩,
   ⟨0, [(0, 2), (0, 1)]⟩,
   ⟨0, [(0, 2), (2, 1)]⟩]

private def k3Carriers :
    List (RootAttachmentCarrierCode KGamma.length) :=
  k3Trees.map (fun tree => ⟨tree, zero3, zero3⟩)

theorem checkedGamma3_clique_canonical_gate_rejects :
    k3Carriers.all (fun carrier =>
      !(sourceSideColorValidB KGamma
        (canonicalSourceColorCode KGamma carrier))) = true := by
  decide

theorem checkedGamma3_clique_canonical_weight_zero :
    qListSum
        (canonicalSourceColorCarrierCodeWeight
          half KGamma qAll qAll qAll labelOne)
        (k3Carriers.map (canonicalSourceColorCode KGamma)) ≈ 0 := by
  decide

/-! ## A two-colorable three-star -/

private def X : Polymer TL := [p, q]
private def Y : Polymer TL := [p]
private def Z : Polymer TL := [q]
private def Gamma3 : List (Polymer TL) := [X, Y, Z]

private def bX : Polymer TL → Bool := fun T => decide (T = X)
private def bY : Polymer TL → Bool := fun T => decide (T = Y)

/- The corresponding two-polymer trunk still pays, so the third occurrence
is the first place where this closed mechanism fails. -/
private def Gamma2 : List (Polymer TL) := [X, Y]

set_option maxRecDepth 10000 in
theorem two_polymer_canonical_majorant_eqv_21_over_1024 :
    canonicalSourceColorCarrierMajorant
        half Gamma2 qAll bX bY labelOne ≈
      Q'.mkPos 21 1024 (by decide) := by
  decide

theorem two_polymer_accepted_budget_eqv_441_over_16384 :
    connectingChainMajorant half qAll bX bY Gamma2 labelOne *
        XiR half qAll Gamma2 labelOne ≈
      Q'.mkPos 441 16384 (by decide) := by
  decide

theorem two_polymer_canonical_majorant_le_accepted_budget :
    canonicalSourceColorCarrierMajorant
        half Gamma2 qAll bX bY labelOne ≤
      connectingChainMajorant half qAll bX bY Gamma2 labelOne *
        XiR half qAll Gamma2 labelOne := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv two_polymer_canonical_majorant_eqv_21_over_1024)
    (Q'.le_trans' _ _ _
      (by decide : Q'.mkPos 21 1024 (by decide) ≤
        Q'.mkPos 441 16384 (by decide))
      (Q'.ge_of_eqv two_polymer_accepted_budget_eqv_441_over_16384))

private def starTrees :
    List (RootAttachmentTreeCode Gamma3.length) :=
  [⟨0, [(0, 1)]⟩,
   ⟨0, [(0, 1), (0, 2)]⟩,
   ⟨0, [(0, 2), (0, 1)]⟩]

private def starExternals : List (OccBitVec Gamma3.length) :=
  [zero3, x3, y3, z3, yz3]

private def starWitnessCarriers :
    List (RootAttachmentCarrierCode Gamma3.length) :=
  starTrees.flatMap (fun tree =>
    starExternals.map (fun external =>
      RootAttachmentCarrierCode.mk tree zero3 external))

private def starWitnessCodes :
    List (SourceColoredRootAttachmentCarrierCode Gamma3.length) :=
  starWitnessCarriers.map (canonicalSourceColorCode Gamma3)

theorem starTrees_nodup : starTrees.Nodup := by
  decide

theorem starExternals_nodup : starExternals.Nodup := by
  decide

theorem starWitnessCarriers_nodup : starWitnessCarriers.Nodup := by
  unfold starWitnessCarriers
  apply nodup_flatMap_map₂
    (fun tree external => RootAttachmentCarrierCode.mk tree zero3 external)
    starTrees starExternals starTrees_nodup starExternals_nodup
  intro tree _ external _ tree' _ external' _ h
  exact ⟨congrArg RootAttachmentCarrierCode.tree h,
    congrArg RootAttachmentCarrierCode.external h⟩

theorem starWitnessCodes_nodup : starWitnessCodes.Nodup := by
  unfold starWitnessCodes
  apply nodup_map_of_injOn
    (canonicalSourceColorCode Gamma3)
    starWitnessCarriers starWitnessCarriers_nodup
  intro carrier _ carrier' _ hcode
  exact canonicalSourceColorCode_injective
    Gamma3 carrier carrier' hcode

theorem starTree_mem_ambient
    (tree : RootAttachmentTreeCode Gamma3.length)
    (htree : tree ∈ starTrees) :
    tree ∈ rootAttachmentTreeCodes Gamma3.length Gamma3.length := by
  simp only [starTrees, List.mem_cons, List.not_mem_nil, or_false] at htree
  rcases htree with htree | htree | htree <;>
    subst tree <;>
    apply RootAttachmentTreeCode.mem_rootAttachmentTreeCodes <;>
    decide

theorem starWitnessCarrier_mem_ambient
    (carrier : RootAttachmentCarrierCode Gamma3.length)
    (hcarrier : carrier ∈ starWitnessCarriers) :
    carrier ∈ rootAttachmentCarrierCodes Gamma3.length Gamma3.length := by
  obtain ⟨tree, htree, hblock⟩ := List.mem_flatMap.mp hcarrier
  obtain ⟨external, _, rfl⟩ := List.mem_map.mp hblock
  apply RootAttachmentCarrierCode.mem_rootAttachmentCarrierCodes
  exact starTree_mem_ambient tree htree

theorem starWitnessCode_mem_canonical
    (code : SourceColoredRootAttachmentCarrierCode Gamma3.length)
    (hcode : code ∈ starWitnessCodes) :
    code ∈ canonicalSourceColorCarrierCodes Gamma3 Gamma3.length := by
  obtain ⟨carrier, hcarrier, rfl⟩ := List.mem_map.mp hcode
  unfold canonicalSourceColorCarrierCodes
  exact List.mem_map.mpr
    ⟨carrier, starWitnessCarrier_mem_ambient carrier hcarrier, rfl⟩

theorem starWitnessCarrier_has_valid_two_color_cover
    (carrier : RootAttachmentCarrierCode Gamma3.length)
    (hcarrier : carrier ∈ starWitnessCarriers) :
    ∃ colors, colors ∈ maskPairs Gamma3.length ∧
      sourceSideColorValidB Gamma3 ⟨carrier, colors⟩ = true := by
  refine ⟨(x3, yz3), maskPairs_complete _, ?_⟩
  obtain ⟨tree, htree, hblock⟩ := List.mem_flatMap.mp hcarrier
  obtain ⟨external, hexternal, rfl⟩ := List.mem_map.mp hblock
  simp only [starTrees, List.mem_cons, List.not_mem_nil, or_false] at htree
  simp only [starExternals, List.mem_cons, List.not_mem_nil, or_false]
    at hexternal
  rcases htree with htree | htree | htree <;>
    rcases hexternal with hexternal | hexternal | hexternal |
      hexternal | hexternal <;>
    subst tree <;> subst external <;> decide

theorem starWitnessCanonicalCodes_valid :
    starWitnessCodes.all
      (fun code => sourceSideColorValidB Gamma3 code) = true := by
  apply List.all_eq_true.mpr
  intro code hcode
  obtain ⟨carrier, hcarrier, rfl⟩ := List.mem_map.mp hcode
  exact canonicalSourceColors_valid_of_exists Gamma3 carrier
    (starWitnessCarrier_has_valid_two_color_cover carrier hcarrier)

set_option maxRecDepth 10000 in
theorem starWitnessCodes_sum_eqv_39_over_1024 :
    qListSum
        (canonicalSourceColorCarrierCodeWeight
          half Gamma3 qAll bX bY labelOne)
        starWitnessCodes ≈
      Q'.mkPos 39 1024 (by decide) := by
  decide

theorem starWitnessCodes_sum_le_canonicalMajorant :
    qListSum
        (canonicalSourceColorCarrierCodeWeight
          half Gamma3 qAll bX bY labelOne)
        starWitnessCodes ≤
      canonicalSourceColorCarrierMajorant
        half Gamma3 qAll bX bY labelOne := by
  unfold canonicalSourceColorCarrierMajorant
  apply qListSum_le_of_injective
    starWitnessCodes
    (canonicalSourceColorCarrierCodes Gamma3 Gamma3.length)
    (canonicalSourceColorCarrierCodeWeight
      half Gamma3 qAll bX bY labelOne)
    (canonicalSourceColorCarrierCodeWeight
      half Gamma3 qAll bX bY labelOne)
    (fun code => code)
    starWitnessCodes_nodup
  · intro code hcode
    exact starWitnessCode_mem_canonical code hcode
  · intro code _ code' _ h
    exact h
  · intro code _
    exact Q'.le_refl' _
  · intro code _
    exact canonicalSourceColorCarrierCodeWeight_nonnegative
      (by decide) Gamma3 qAll bX bY labelOne code

/-! ## The accepted budget is strictly smaller -/

theorem star_Gamma3_chain_eqv_365_over_16384 :
    connectingChainMajorant half qAll bX bY Gamma3 labelOne ≈
      Q'.mkPos 365 16384 (by decide) := by
  decide

theorem star_Gamma3_XiR_eqv_13_over_8 :
    XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 13 8 (by decide) := by
  decide

theorem star_accepted_budget_eqv_4745_over_131072 :
    connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 4745 131072 (by decide) := by
  decide

theorem canonicalSourceColorMajorant_not_le_accepted_budget :
    ¬ (canonicalSourceColorCarrierMajorant
          half Gamma3 qAll bX bY labelOne ≤
        connectingChainMajorant half qAll bX bY Gamma3 labelOne *
          XiR half qAll Gamma3 labelOne) := by
  intro hpayment
  have hclosed := Q'.le_trans' _ _ _
    starWitnessCodes_sum_le_canonicalMajorant hpayment
  have hnumeric :
      Q'.mkPos 39 1024 (by decide) ≤
        Q'.mkPos 4745 131072 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv starWitnessCodes_sum_eqv_39_over_1024)
      (Q'.le_trans' _ _ _ hclosed
        (Q'.le_of_eqv star_accepted_budget_eqv_4745_over_131072))
  exact (by decide : ¬ (Q'.mkPos 39 1024 (by decide) ≤
    Q'.mkPos 4745 131072 (by decide))) hnumeric

/-! ## Necessary invariant for every corrected payment gate

An additional Boolean gate may retain any desired exact payload invariant.
If it retains all fifteen star witnesses, it still cannot pay.  Consequently
every successful refinement must reject at least one of them; two-color
compatibility by itself accepts all of them.
-/

def starGatedCanonicalWeight
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma3.length) : Q' :=
  if keep code then
    canonicalSourceColorCarrierCodeWeight
      half Gamma3 qAll bX bY labelOne code
  else 0

def starGatedCanonicalMajorant
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool) :
    Q' :=
  qListSum (starGatedCanonicalWeight keep)
    (canonicalSourceColorCarrierCodes Gamma3 Gamma3.length)

theorem starGatedCanonicalWeight_nonnegative
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma3.length) :
    (0 : Q') ≤ starGatedCanonicalWeight keep code := by
  unfold starGatedCanonicalWeight
  split
  · exact canonicalSourceColorCarrierCodeWeight_nonnegative
      (by decide) Gamma3 qAll bX bY labelOne code
  · exact Q'.le_refl' _

theorem starWitnessCodes_sum_le_gatedMajorant
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (hkeep : starWitnessCodes.all keep = true) :
    qListSum
        (canonicalSourceColorCarrierCodeWeight
          half Gamma3 qAll bX bY labelOne)
        starWitnessCodes ≤
      starGatedCanonicalMajorant keep := by
  unfold starGatedCanonicalMajorant
  apply qListSum_le_of_injective
    starWitnessCodes
    (canonicalSourceColorCarrierCodes Gamma3 Gamma3.length)
    (canonicalSourceColorCarrierCodeWeight
      half Gamma3 qAll bX bY labelOne)
    (starGatedCanonicalWeight keep)
    (fun code => code)
    starWitnessCodes_nodup
  · intro code hcode
    exact starWitnessCode_mem_canonical code hcode
  · intro code _ code' _ h
    exact h
  · intro code hcode
    have hkept := (List.all_eq_true.mp hkeep) code hcode
    unfold starGatedCanonicalWeight
    rw [hkept]
    exact Q'.le_refl' _
  · intro code _
    exact starGatedCanonicalWeight_nonnegative keep code

theorem any_gate_accepting_all_star_witnesses_fails_payment
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (hkeep : starWitnessCodes.all keep = true) :
    ¬ (starGatedCanonicalMajorant keep ≤
      connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne) := by
  intro hpayment
  have hclosed := Q'.le_trans' _ _ _
    (starWitnessCodes_sum_le_gatedMajorant keep hkeep) hpayment
  have hnumeric :
      Q'.mkPos 39 1024 (by decide) ≤
        Q'.mkPos 4745 131072 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv starWitnessCodes_sum_eqv_39_over_1024)
      (Q'.le_trans' _ _ _ hclosed
        (Q'.le_of_eqv star_accepted_budget_eqv_4745_over_131072))
  exact (by decide : ¬ (Q'.mkPos 39 1024 (by decide) ≤
    Q'.mkPos 4745 131072 (by decide))) hnumeric

theorem successful_gate_must_reject_a_star_witness
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (hpayment : starGatedCanonicalMajorant keep ≤
      connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne) :
    starWitnessCodes.all keep = false := by
  cases hkeep : starWitnessCodes.all keep with
  | false => rfl
  | true =>
      exact False.elim
        ((any_gate_accepting_all_star_witnesses_fails_payment keep hkeep)
          hpayment)

private theorem exists_false_member_of_all_false (test : alpha → Bool) :
    ∀ xs : List alpha, xs.all test = false →
      ∃ x, x ∈ xs ∧ test x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : test x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have htail : xs.all test = false := by
            simpa only [List.all_cons, hx, Bool.true_and] using h
          obtain ⟨y, hy, htest⟩ :=
            exists_false_member_of_all_false test xs htail
          exact ⟨y, List.mem_cons_of_mem x hy, htest⟩

theorem successful_gate_rejects_concrete_star_witness
    (keep : SourceColoredRootAttachmentCarrierCode Gamma3.length → Bool)
    (hpayment : starGatedCanonicalMajorant keep ≤
      connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne) :
    ∃ code, code ∈ starWitnessCodes ∧ keep code = false := by
  exact exists_false_member_of_all_false keep starWitnessCodes
    (successful_gate_must_reject_a_star_witness keep hpayment)

#print axioms checkedGamma3_clique_canonical_gate_rejects
#print axioms checkedGamma3_clique_canonical_weight_zero
#print axioms starWitnessCarriers_nodup
#print axioms starWitnessCodes_nodup
#print axioms starTree_mem_ambient
#print axioms starWitnessCarrier_mem_ambient
#print axioms starWitnessCode_mem_canonical
#print axioms starWitnessCarrier_has_valid_two_color_cover
#print axioms starWitnessCanonicalCodes_valid
#print axioms two_polymer_canonical_majorant_eqv_21_over_1024
#print axioms two_polymer_accepted_budget_eqv_441_over_16384
#print axioms two_polymer_canonical_majorant_le_accepted_budget
#print axioms starWitnessCodes_sum_eqv_39_over_1024
#print axioms starWitnessCodes_sum_le_canonicalMajorant
#print axioms star_Gamma3_chain_eqv_365_over_16384
#print axioms star_Gamma3_XiR_eqv_13_over_8
#print axioms star_accepted_budget_eqv_4745_over_131072
#print axioms canonicalSourceColorMajorant_not_le_accepted_budget
#print axioms starGatedCanonicalWeight_nonnegative
#print axioms starWitnessCodes_sum_le_gatedMajorant
#print axioms any_gate_accepting_all_star_witnesses_fails_payment
#print axioms successful_gate_must_reject_a_star_witness
#print axioms successful_gate_rejects_concrete_star_witness

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorPaymentFence
