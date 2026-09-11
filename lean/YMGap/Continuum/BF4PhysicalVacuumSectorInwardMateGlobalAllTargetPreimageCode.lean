/-
# A six-bit ambiguity code for the global inward-mate target

The scalar inward-mate map is injective away from its single collision:
the source labels `0` and `2` both map to `1`.  One Boolean recording whether
the source label was zero resolves that collision.  Applying this code on the
six central lower cube faces gives an exhaustive carrier of exactly
`2^6 = 64` words, and equality of target physical fields together with
equality of codes recovers the entire source physical field.

This is the physical-coordinate part of the target-fiber capacity proof.  It
does not yet recover the source intertwiner assignment from the complete raw
target, bound the full target-atom fiber, sum transported mass, or assert a
posterior-variance, OS form, spectral-gap, or continuum estimate.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. One bit resolves the only scalar collision -/

/-- The lost scalar datum: whether an inward-mate source label was zero. -/
def evenInwardMatePreimageBit (spin : Nat) : Bool :=
  if spin = 0 then true else false

/-- The inward-mate output together with the zero bit uniquely determines its
natural-number source label. -/
theorem evenInwardMateLabel_injective_with_bit
    (left right : Nat)
    (hmate : evenInwardMateLabel left = evenInwardMateLabel right)
    (hbit : evenInwardMatePreimageBit left =
      evenInwardMatePreimageBit right) :
    left = right := by
  by_cases hleft : left = 0
  · subst left
    by_cases hright : right = 0
    · exact hright.symm
    · simp [evenInwardMatePreimageBit, hright] at hbit
  · by_cases hright : right = 0
    · subst right
      simp [evenInwardMatePreimageBit, hleft] at hbit
    · unfold evenInwardMateLabel at hmate
      rw [if_neg hleft, if_neg hright] at hmate
      omega

/-! ## 2. The exact six-bit code carrier -/

/-- Every Boolean word of one exact length. -/
def globalInwardMateBoolWords : Nat → List (List Bool)
  | 0 => [[]]
  | count + 1 =>
      (globalInwardMateBoolWords count).map (fun bits => false :: bits) ++
        (globalInwardMateBoolWords count).map (fun bits => true :: bits)

theorem globalInwardMateBoolWords_complete :
    ∀ {count : Nat} (bits : List Bool), bits.length = count →
      bits ∈ globalInwardMateBoolWords count
  | 0, bits, hlength => by
      cases bits with
      | nil => exact List.mem_cons_self
      | cons _ _ => simp only [List.length_cons] at hlength; omega
  | count + 1, [], hlength => by
      simp only [List.length_nil] at hlength
      omega
  | count + 1, bit :: bits, hlength => by
      have htail : bits.length = count := by
        simp only [List.length_cons] at hlength
        omega
      cases bit with
      | false =>
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨bits, globalInwardMateBoolWords_complete bits htail, rfl⟩
      | true =>
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨bits, globalInwardMateBoolWords_complete bits htail, rfl⟩

@[simp] theorem globalInwardMateBoolWords_length :
    ∀ count : Nat,
      (globalInwardMateBoolWords count).length = 2 ^ count
  | 0 => rfl
  | count + 1 => by
      simp only [globalInwardMateBoolWords, List.length_append,
        List.length_map, globalInwardMateBoolWords_length]
      rw [Nat.pow_succ]
      omega

/-- The six lost zero/nonzero decisions of one successful global source. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List Bool :=
  centralLowerCubeFaceIds.map
    (fun faceId => evenInwardMatePreimageBit (source.physical faceId))

@[simp] theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_length
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode
      source).length = 6 := by
  rfl

/-- The fixed exhaustive carrier for all six-bit preimage codes. -/
def globalInwardMateTargetPreimageCodeSpace : List (List Bool) :=
  globalInwardMateBoolWords 6

theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode source ∈
      globalInwardMateTargetPreimageCodeSpace := by
  unfold globalInwardMateTargetPreimageCodeSpace
  apply globalInwardMateBoolWords_complete
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_length
      source

@[simp] theorem globalInwardMateTargetPreimageCodeSpace_length :
    globalInwardMateTargetPreimageCodeSpace.length = 64 := by
  rfl

/-! ## 3. Target physical field plus code recovers the source physical field -/

private theorem listMap_functions_eq_on_mem
    {A B : Type} (items : List A) (left right : A → B)
    (hmap : items.map left = items.map right) :
    ∀ item, item ∈ items → left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by
        injection hmap
      have htail : tail.map left = tail.map right := by
        injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · exact heq ▸ hhead
      · exact ih htail item htailMem

/-- Equality of parity-flipped targets and equality of the six-bit ambiguity
code recover the entire source physical field, including the unchanged
off-cube complement. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.physical_eq_of_targetPhysical_eq_of_targetPreimageCode_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (htarget :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right)
    (hcode :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode right) :
    left.physical = right.physical := by
  funext faceId
  by_cases hface : faceId ∈ centralLowerCubeFaceIds
  · have hbit : evenInwardMatePreimageBit (left.physical faceId) =
        evenInwardMatePreimageBit (right.physical faceId) := by
      unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode
        at hcode
      exact listMap_functions_eq_on_mem centralLowerCubeFaceIds
        (fun id => evenInwardMatePreimageBit (left.physical id))
        (fun id => evenInwardMatePreimageBit (right.physical id))
        hcode faceId hface
    have hmate : evenInwardMateLabel (left.physical faceId) =
        evenInwardMateLabel (right.physical faceId) := by
      calc
        evenInwardMateLabel (left.physical faceId) =
            GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
              left faceId :=
          (centralLowerCubeEvenInwardMatePhysical_on_cube
            left.physical hface).symm
        _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
              right faceId := congrFun htarget faceId
        _ = evenInwardMateLabel (right.physical faceId) :=
          centralLowerCubeEvenInwardMatePhysical_on_cube
            right.physical hface
    exact evenInwardMateLabel_injective_with_bit
      (left.physical faceId) (right.physical faceId) hmate hbit
  · calc
      left.physical faceId =
          GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
            left faceId :=
        (centralLowerCubeEvenInwardMatePhysical_off_cube
          left.physical hface).symm
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
            right faceId := congrFun htarget faceId
      _ = right.physical faceId :=
        centralLowerCubeEvenInwardMatePhysical_off_cube
          right.physical hface

#print axioms evenInwardMateLabel_injective_with_bit
#print axioms globalInwardMateBoolWords_complete
#print axioms globalInwardMateBoolWords_length
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_length
#print axioms globalInwardMateTargetPreimageCodeSpace_length
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.physical_eq_of_targetPhysical_eq_of_targetPreimageCode_eq

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode
