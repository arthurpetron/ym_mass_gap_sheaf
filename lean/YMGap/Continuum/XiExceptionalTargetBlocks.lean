/-
# Disjoint finite target-block allocation

A branch-rich exceptional source need not fit one positive carrier code.  This
file gives the constructive finite replacement: allocate a duplicate-free,
pairwise-disjoint block of target codes to each source.  If the source term is
bounded by its whole block, flattening the blocks and embedding that flattened
list in the explicit target enumeration proves the global weighted bound.
-/

import YMGap.Continuum.XiExceptionalMarkedPrunedFence

namespace YMGap.Continuum.XiExceptionalTargetBlocks

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pointwise finite-sum monotonicity -/

theorem qListSum_le_pointwise (f g : alpha → Q') :
    ∀ (xs : List alpha),
      (∀ x, x ∈ xs → f x ≤ g x) →
      qListSum f xs ≤ qListSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => by
      simp only [qListSum_cons]
      exact Q'.add_le_add (h x List.mem_cons_self)
        (qListSum_le_pointwise f g xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-! ## 2. A checkable criterion for disjoint flattened blocks -/

theorem nodup_flatMap_of_pairwise_disjoint [DecidableEq beta]
    (source : List alpha) (block : alpha → List beta)
    (hsource : source.Nodup)
    (hblock : ∀ x, x ∈ source → (block x).Nodup)
    (hdisjoint : ∀ x, x ∈ source → ∀ y, y ∈ source →
      x ≠ y → ∀ z, z ∈ block x → z ∉ block y) :
    (source.flatMap block).Nodup := by
  induction source with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hs := List.nodup_cons.mp hsource
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblock x List.mem_cons_self, ?_, ?_⟩
      · apply ih hs.2
        · intro y hy
          exact hblock y (List.mem_cons_of_mem x hy)
        · intro y hy z hz hyz t ht
          exact hdisjoint y (List.mem_cons_of_mem x hy)
            z (List.mem_cons_of_mem x hz) hyz t ht
      · intro z hz t ht hzt
        obtain ⟨y, hy, hty⟩ := List.mem_flatMap.mp ht
        have hxy : x ≠ y := by
          intro hxy
          subst y
          exact hs.1 hy
        have hnot := hdisjoint x List.mem_cons_self
          y (List.mem_cons_of_mem x hy) hxy z hz
        exact hnot (hzt ▸ hty)

/-! ## 3. Weighted domination by disjoint target blocks -/

theorem qListSum_le_of_disjoint_blocks [DecidableEq beta]
    (source : List alpha) (target : List beta)
    (sourceWeight : alpha → Q') (targetWeight : beta → Q')
    (block : alpha → List beta)
    (hflatNodup : (source.flatMap block).Nodup)
    (hmem : ∀ y, y ∈ source.flatMap block → y ∈ target)
    (hsourceBlock : ∀ x, x ∈ source →
      sourceWeight x ≤ qListSum targetWeight (block x))
    (htargetNonneg : ∀ y, y ∈ target → (0 : Q') ≤ targetWeight y) :
    qListSum sourceWeight source ≤ qListSum targetWeight target := by
  have hsourceToBlocks : qListSum sourceWeight source ≤
      qListSum (fun x => qListSum targetWeight (block x)) source :=
    qListSum_le_pointwise sourceWeight
      (fun x => qListSum targetWeight (block x)) source hsourceBlock
  have hflatEq := qListSum_flatMap targetWeight block source
  have hsourceToFlat : qListSum sourceWeight source ≤
      qListSum targetWeight (source.flatMap block) :=
    Q'.le_trans' _ _ _ hsourceToBlocks (Q'.ge_of_eqv hflatEq)
  have hflatToTarget : qListSum targetWeight (source.flatMap block) ≤
      qListSum targetWeight target := by
    apply qListSum_le_of_injective (source.flatMap block) target
      targetWeight targetWeight (fun y => y) hflatNodup
    · intro y hy
      exact hmem y hy
    · intro y _ z _ hyz
      exact hyz
    · intro y _
      exact Q'.le_refl' _
    · exact htargetNonneg
  exact Q'.le_trans' _ _ _ hsourceToFlat hflatToTarget

#print axioms qListSum_le_pointwise
#print axioms nodup_flatMap_of_pairwise_disjoint
#print axioms qListSum_le_of_disjoint_blocks

end YMGap.Continuum.XiExceptionalTargetBlocks
