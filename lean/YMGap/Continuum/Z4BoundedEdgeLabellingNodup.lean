/-
# Duplicate-freeness of bounded edge-labelling enumeration

The Cartesian labelling generator is duplicate-free whenever its edge list is
duplicate-free.  This fact is needed to regard the arbitrary-cutoff decorated
surface families as an honest finite gas domain rather than as a list with
uncontrolled enumeration multiplicities.
-/

import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

namespace YMGap.Continuum.Z4BoundedEdgeLabellingNodup

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

private theorem range_nodup_local (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

private theorem nodup_flatMap_of_disjoint_blocks {A B : Type}
    (block : A → List B) :
    ∀ source : List A,
      source.Nodup →
      (∀ a, a ∈ source → (block a).Nodup) →
      (∀ a, a ∈ source → ∀ b, b ∈ source → a ≠ b →
        ∀ value, value ∈ block a → value ∉ block b) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun a ha => hblocks a (List.mem_cons_of_mem head ha))
          (fun a ha b hb hne => hdisjoint a
            (List.mem_cons_of_mem head ha) b
            (List.mem_cons_of_mem head hb) hne), ?_⟩
      intro value hhead tailValue htail heq
      have htailFlat : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨other, hother, hvalueOther⟩ :=
        List.mem_flatMap.mp htailFlat
      have hne : head ≠ other := by
        intro heqHead
        subst other
        exact hparts.1 hother
      exact (hdisjoint head List.mem_cons_self other
        (List.mem_cons_of_mem head hother) hne value hhead) hvalueOther

private theorem setEdgeLabel_injective_on_supported
    {K edge : Nat} {rest : List Nat} (hedge : edge ∉ rest)
    (spin : Nat) {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K rest)
    (hright : right ∈ boundedEdgeLabellings K rest)
    (heq : setEdgeLabel left edge spin =
      setEdgeLabel right edge spin) :
    left = right := by
  have hleftSound := boundedEdgeLabellings_sound K rest left hleft
  have hrightSound := boundedEdgeLabellings_sound K rest right hright
  funext position
  by_cases hposition : position = edge
  · subst position
    rw [hleftSound.2 edge hedge, hrightSound.2 edge hedge]
  · have hpoint := congrArg (fun label => label position) heq
    simpa [setEdgeLabel, hposition] using hpoint

private theorem setEdgeLabel_different_spins
    {edge leftSpin rightSpin : Nat} {left right : EdgeLabelling}
    (heq : setEdgeLabel left edge leftSpin =
      setEdgeLabel right edge rightSpin) :
    leftSpin = rightSpin := by
  have hpoint := congrArg (fun label => label edge) heq
  simpa [setEdgeLabel] using hpoint

theorem boundedEdgeLabellings_nodup (K : Nat) :
    ∀ edges : List Nat, edges.Nodup →
      (boundedEdgeLabellings K edges).Nodup
  | [], _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | edge :: rest, hedges => by
      have hparts := List.nodup_cons.mp hedges
      unfold boundedEdgeLabellings
      apply nodup_flatMap_of_disjoint_blocks
      · exact range_nodup_local _
      · intro spin hspin
        apply CayleyPruferInjection.nodup_map_of_injOn
        · exact boundedEdgeLabellings_nodup K rest hparts.2
        · intro left hleft right hright heq
          exact setEdgeLabel_injective_on_supported hparts.1 spin
            hleft hright heq
      · intro leftSpin hleftSpin rightSpin hrightSpin hne
          value hvalueLeft hvalueRight
        obtain ⟨left, hleft, heqLeft⟩ := List.mem_map.mp hvalueLeft
        obtain ⟨right, hright, heqRight⟩ := List.mem_map.mp hvalueRight
        have hlabels :
            setEdgeLabel left edge leftSpin =
              setEdgeLabel right edge rightSpin := by
          exact heqLeft.trans heqRight.symm
        exact hne (setEdgeLabel_different_spins hlabels)

end YMGap.Continuum.Z4BoundedEdgeLabellingNodup

#print axioms YMGap.Continuum.Z4BoundedEdgeLabellingNodup.boundedEdgeLabellings_nodup
