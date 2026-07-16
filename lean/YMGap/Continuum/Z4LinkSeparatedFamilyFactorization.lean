/-
# Exact factorization of finite link-separated cutoff-one families

The binary factorization theorem is lifted here to arbitrary finite families.
The separation predicate is deliberately recursive: the head support is
face-disjoint and link-separated from the union of the tail, and the tail is
again separated.  This is precisely the induction interface that a maximal
link-connected-component decomposition must produce.

No abstract polymer compatibility relation is used.  All separation is stated
against the actual finite-box physical links that occur in the packet graph.
-/

import YMGap.Continuum.Z4LinkSeparatedComponentFactorization

namespace YMGap.Continuum.Z4LinkSeparatedFamilyFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Union, physicality, and recursive separation -/

def binaryUnionLabels : List EdgeLabelling → EdgeLabelling
  | [] => zeroEdgeLabelling
  | head :: tail => binaryUnionLabel head (binaryUnionLabels tail)

def PhysicalFamily (n : Nat) (family : List EdgeLabelling) : Prop :=
  ∀ label, label ∈ family → label ∈ explicitPhysicalLabellings 1 n

def LinkSeparatedFamily (n : Nat) : List EdgeLabelling → Prop
  | [] => True
  | head :: tail =>
      FaceDisjoint n head (binaryUnionLabels tail) ∧
        LinkSeparated n head (binaryUnionLabels tail) ∧
          LinkSeparatedFamily n tail

theorem zeroEdgeLabelling_mem_explicitPhysicalLabellings (n : Nat) :
    zeroEdgeLabelling ∈ explicitPhysicalLabellings 1 n := by
  unfold explicitPhysicalLabellings
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    simp only [zeroEdgeLabelling]
    omega
  · intro edge hedge
    rfl

theorem physicalFamily_head {n : Nat} {head : EdgeLabelling}
    {tail : List EdgeLabelling}
    (hphysical : PhysicalFamily n (head :: tail)) :
    head ∈ explicitPhysicalLabellings 1 n :=
  hphysical head List.mem_cons_self

theorem physicalFamily_tail {n : Nat} {head : EdgeLabelling}
    {tail : List EdgeLabelling}
    (hphysical : PhysicalFamily n (head :: tail)) :
    PhysicalFamily n tail :=
  fun label hlabel => hphysical label (List.mem_cons_of_mem head hlabel)

theorem binaryUnionLabels_mem_physical (n : Nat) :
    ∀ family : List EdgeLabelling,
      PhysicalFamily n family →
      LinkSeparatedFamily n family →
      binaryUnionLabels family ∈ explicitPhysicalLabellings 1 n
  | [], _, _ => zeroEdgeLabelling_mem_explicitPhysicalLabellings n
  | head :: tail, hphysical, hseparated => by
      have hhead := physicalFamily_head hphysical
      have htail := binaryUnionLabels_mem_physical n tail
        (physicalFamily_tail hphysical) hseparated.2.2
      exact binaryUnionLabel_mem_physical hhead htail hseparated.1

/-! ## 2. Exact finite-family multiplication -/

def parametricLocalizedWeightProduct (w : Q') (n : Nat) :
    List EdgeLabelling → Q'
  | [] => 1
  | head :: tail =>
      parametricLocalizedSpinFoamWeight w n head *
        parametricLocalizedWeightProduct w n tail

theorem parametricLocalizedSpinFoamWeight_unionLabels_factor
    (w : Q') (n : Nat) :
    ∀ family : List EdgeLabelling,
      PhysicalFamily n family →
      LinkSeparatedFamily n family →
      parametricLocalizedSpinFoamWeight w n (binaryUnionLabels family) ≈
        parametricLocalizedWeightProduct w n family
  | [], _, _ => parametricLocalizedSpinFoamWeight_zero_eqv_one w n
  | head :: tail, hphysical, hseparated => by
      have hhead := physicalFamily_head hphysical
      have htailPhysical := physicalFamily_tail hphysical
      have htailUnion := binaryUnionLabels_mem_physical n tail
        htailPhysical hseparated.2.2
      have hbinary := parametricLocalizedSpinFoamWeight_union_factor (w := w)
        hhead htailUnion hseparated.1 hseparated.2.1
      have hinduction :=
        parametricLocalizedSpinFoamWeight_unionLabels_factor w n tail
          htailPhysical hseparated.2.2
      exact Q'.eqv_trans _ _ _ hbinary
        (Q'.mul_eqv_congr_left
          (parametricLocalizedSpinFoamWeight w n head) _ _ hinduction)

end YMGap.Continuum.Z4LinkSeparatedFamilyFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LinkSeparatedFamilyFactorization.zeroEdgeLabelling_mem_explicitPhysicalLabellings
#print axioms YMGap.Continuum.Z4LinkSeparatedFamilyFactorization.binaryUnionLabels_mem_physical
#print axioms YMGap.Continuum.Z4LinkSeparatedFamilyFactorization.parametricLocalizedSpinFoamWeight_unionLabels_factor
