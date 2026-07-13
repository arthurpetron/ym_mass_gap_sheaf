/-
# Occurrence carrier target codes are duplicate-free

Fiberwise summation assigns each source fiber to a target *value*, so the
explicit target enumeration must not repeat a value.  The occurrence-indexed
enumerations have exactly this property.  This file proves it constructively
from a generic duplicate-free Cartesian-block lemma.
-/

import YMGap.Continuum.XiExceptionalFiberwiseInjection

namespace YMGap.Continuum.XiExceptionalTargetNodup

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Duplicate-free mapped Cartesian blocks -/

theorem nodup_flatMap_map₂ {alpha beta gamma : Type}
    (f : alpha → beta → gamma) (xs : List alpha) (ys : List beta)
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ ys →
      ∀ a', a' ∈ xs → ∀ b', b' ∈ ys →
        f a b = f a' b' → a = a' ∧ b = b') :
    (xs.flatMap (fun a => ys.map (f a))).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hp := List.nodup_cons.mp hxs
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · exact nodup_map_of_injOn (f x) ys hys
          (fun b hb b' hb' h => by
            have hpair : x = x ∧ b = b' :=
              hinj x List.mem_cons_self b hb
                x List.mem_cons_self b' hb' h
            exact hpair.2)
      · exact ih hp.2 (fun a ha b hb a' ha' b' hb' h =>
          hinj a (List.mem_cons_of_mem x ha) b hb
            a' (List.mem_cons_of_mem x ha') b' hb' h)
      · intro u hu v hv huv
        obtain ⟨b, hb, hbu⟩ := List.mem_map.mp hu
        obtain ⟨a, ha, hav⟩ := List.mem_flatMap.mp hv
        obtain ⟨b', hb', hb'v⟩ := List.mem_map.mp hav
        rw [← hbu, ← hb'v] at huv
        have hxa := (hinj x List.mem_cons_self b hb
          a (List.mem_cons_of_mem x ha) b' hb' huv).1
        exact hp.1 (hxa ▸ ha)

/-! ## 2. Recursive chain codes -/

theorem occurrenceTerminalCodes_nodup (Gamma : List (Polymer L)) :
    (occurrenceTerminalCodes Gamma).Nodup := by
  unfold occurrenceTerminalCodes
  exact nodup_map_of_injOn OccChainCode.terminal
    (bitVectors Gamma.length) (bitVectors_nodup Gamma.length)
    (fun _ _ _ _ h => by injection h)

theorem occurrenceChainCodes_nodup (Gamma : List (Polymer L)) :
    ∀ fuel, (occurrenceChainCodes Gamma fuel).Nodup
  | 0 => occurrenceTerminalCodes_nodup Gamma
  | fuel + 1 => by
      unfold occurrenceChainCodes
      have hterminal := occurrenceTerminalCodes_nodup Gamma
      have hindices := occurrenceIndices_nodup Gamma.length
      have hrest := occurrenceChainCodes_nodup Gamma fuel
      have hsteps : (occurrenceIndices Gamma.length).flatMap
          (fun next => (occurrenceChainCodes Gamma fuel).map
            (OccChainCode.step next)) |>.Nodup := by
        apply nodup_flatMap_map₂ OccChainCode.step
          (occurrenceIndices Gamma.length)
          (occurrenceChainCodes Gamma fuel) hindices hrest
        intro a _ b _ a' _ b' _ h
        injection h with ha hb
        exact ⟨ha, hb⟩
      apply List.nodup_append.mpr
      refine ⟨hterminal, hsteps, ?_⟩
      intro terminal hterminalMem step hstepMem heq
      obtain ⟨background, _, hterminalEq⟩ :=
        List.mem_map.mp hterminalMem
      obtain ⟨next, _, hblock⟩ := List.mem_flatMap.mp hstepMem
      obtain ⟨rest, _, hstepEq⟩ := List.mem_map.mp hblock
      rw [← hterminalEq, ← hstepEq] at heq
      cases heq

/-! ## 3. Carrier and carrier-times-Xi codes -/

theorem occurrenceCarrierCodes_nodup (Gamma : List (Polymer L)) :
    (occurrenceCarrierCodes Gamma).Nodup := by
  unfold occurrenceCarrierCodes
  apply nodup_flatMap_map₂ (fun start chain =>
      OccCarrierCodeAt.mk start chain)
    (occurrenceIndices Gamma.length)
    (occurrenceChainCodes Gamma Gamma.length)
    (occurrenceIndices_nodup Gamma.length)
    (occurrenceChainCodes_nodup Gamma Gamma.length)
  intro a _ b _ a' _ b' _ h
  have ha := congrArg OccCarrierCodeAt.start h
  have hb := congrArg OccCarrierCodeAt.chain h
  exact ⟨ha, hb⟩

theorem occurrenceCarrierXiCodes_nodup (Gamma : List (Polymer L)) :
    (occurrenceCarrierXiCodes Gamma).Nodup := by
  unfold occurrenceCarrierXiCodes
  apply nodup_flatMap_map₂ (fun external carrier =>
      OccCarrierXiCodeAt.mk carrier external)
    (bitVectors Gamma.length) (occurrenceCarrierCodes Gamma)
    (bitVectors_nodup Gamma.length) (occurrenceCarrierCodes_nodup Gamma)
  intro external _ carrier _ external' _ carrier' _ h
  have hcarrier := congrArg OccCarrierXiCodeAt.carrier h
  have hexternal := congrArg OccCarrierXiCodeAt.external h
  exact ⟨hexternal, hcarrier⟩

#print axioms nodup_flatMap_map₂
#print axioms occurrenceTerminalCodes_nodup
#print axioms occurrenceChainCodes_nodup
#print axioms occurrenceCarrierCodes_nodup
#print axioms occurrenceCarrierXiCodes_nodup

end YMGap.Continuum.XiExceptionalTargetNodup
