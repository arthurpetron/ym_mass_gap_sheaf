/-
# Exact factorization of finite link-separated all-spin families

The arbitrary-cutoff two-component factorization is lifted here to finite
families.  The recursive separation predicate is the same geometric one used
by the cutoff-one surface gas; only physicality and the exact weight retain
the cutoff parameter.
-/

import YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
import YMGap.Continuum.Z4LinkSeparatedFamilyFactorization

namespace YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

def KPhysicalFamily (K n : Nat) (family : List EdgeLabelling) : Prop :=
  ∀ label, label ∈ family →
    label ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))

theorem zeroEdgeLabelling_mem_bounded (K n : Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)) := by
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    simp only [zeroEdgeLabelling]
    omega
  · intro edge hedge
    rfl

theorem kPhysicalFamily_head {K n : Nat} {head : EdgeLabelling}
    {tail : List EdgeLabelling}
    (hphysical : KPhysicalFamily K n (head :: tail)) :
    head ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)) :=
  hphysical head List.mem_cons_self

theorem kPhysicalFamily_tail {K n : Nat} {head : EdgeLabelling}
    {tail : List EdgeLabelling}
    (hphysical : KPhysicalFamily K n (head :: tail)) :
    KPhysicalFamily K n tail :=
  fun label hlabel => hphysical label (List.mem_cons_of_mem head hlabel)

theorem unionLabels_mem_bounded (K n : Nat) :
    ∀ family : List EdgeLabelling,
      KPhysicalFamily K n family →
      LinkSeparatedFamily n family →
      binaryUnionLabels family ∈ boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount n))
  | [], _, _ => zeroEdgeLabelling_mem_bounded K n
  | head :: tail, hphysical, hseparated => by
      have hhead := kPhysicalFamily_head hphysical
      have htail := unionLabels_mem_bounded K n tail
        (kPhysicalFamily_tail hphysical) hseparated.2.2
      exact unionLabel_mem_bounded hhead htail hseparated.1

def parametricKPhysicalTermProduct (w : Q') (K n : Nat) :
    List EdgeLabelling → Q'
  | [] => 1
  | head :: tail =>
      parametricKPhysicalTerm w K n head *
        parametricKPhysicalTermProduct w K n tail

theorem parametricKPhysicalTerm_unionLabels_factor
    (w : Q') (K n : Nat) :
    ∀ family : List EdgeLabelling,
      KPhysicalFamily K n family →
      LinkSeparatedFamily n family →
      parametricKPhysicalTerm w K n (binaryUnionLabels family) ≈
        parametricKPhysicalTermProduct w K n family
  | [], _, _ => parametricKPhysicalTerm_zero_eqv_one w K n
  | head :: tail, hphysical, hseparated => by
      have hhead := kPhysicalFamily_head hphysical
      have htailPhysical := kPhysicalFamily_tail hphysical
      have htailUnion := unionLabels_mem_bounded K n tail
        htailPhysical hseparated.2.2
      have hbinary :=
        Z4AllSpinLinkSeparatedFactorization.parametricKPhysicalTerm_union_factor
          (w := w) hhead htailUnion hseparated.1 hseparated.2.1
      have hinduction :=
        parametricKPhysicalTerm_unionLabels_factor w K n tail
          htailPhysical hseparated.2.2
      exact Q'.eqv_trans _ _ _ hbinary
        (Q'.mul_eqv_congr_left
          (parametricKPhysicalTerm w K n head) _ _ hinduction)

end YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization.zeroEdgeLabelling_mem_bounded
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization.unionLabels_mem_bounded
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization.parametricKPhysicalTerm_unionLabels_factor
