/-
# Corrected distinct-occurrence exceptional path and injection substrate

The frozen normalization fence in `XiExceptionalRecoveredBackground` shows
that physical occurrence graphs must have a false diagonal.  This successor
rebuilds the exceptional occurrence-to-polymer path over `incAtDistinct` and
supplies the first list/mask primitives needed for the eventual finite
weighted injection.
-/

import YMGap.Continuum.XiExceptionalRecoveredBackground

namespace YMGap.Continuum.XiExceptionalDistinctInjection

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Non-vacuous same-side guards for the corrected graph -/

/-- Pairwise compatibility of distinct occupied occurrences is exactly what
is needed to discharge the same-side graph guard after the diagonal is
removed. -/
theorem sameSide_guard_incAtDistinct
    (Γ : List (Polymer L)) (mask : Nat → Bool)
    (hcompat : ∀ i j, i ≠ j → mask i = true → mask j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true) :
    ∀ i j, mask i = true → mask j = true →
      symConflict (incAtDistinct Γ) i j = false := by
  intro i j hi hj
  by_cases hij : i = j
  · subst j
    simp [symConflict, incAtDistinct]
  · have hijc := hcompat i j hij hi hj
    have hjic := hcompat j i (fun h => hij h.symm) hj hi
    unfold symConflict incAtDistinct
    simp [hij, hijc, hjic]

/-! ## 2. Corrected occurrence-to-polymer path -/

structure DistinctExceptionalPolymerPath
    (Γ : List (Polymer L)) (qP b2 : Polymer L → Bool)
    (left right : Nat → Bool) (marked : Nat) : Type where
  seed : Nat
  seed_true :
    forwardSeed Γ.length left right (predAt Γ b2) seed = true
  indexWalk :
    CWalk (disagreementEdge Γ.length (incAtDistinct Γ) left right) marked seed
  index_nodup : indexWalk.vertices.Nodup
  polymerWalk :
    CWalk (fun X Y : Polymer L => !(compatibleB X Y))
      (polyAt Γ marked) (polyAt Γ seed)
  polymer_vertices :
    polymerWalk.vertices = indexWalk.vertices.map (polyAt Γ)
  length_le : polymerWalk.vertices.length ≤ Γ.length
  ambient_mem : ∀ X, X ∈ polymerWalk.vertices → X ∈ Γ
  q_true : ∀ X, X ∈ polymerWalk.vertices → qP X = true

def distinctExceptionalPolymerPathOfReach
    (Γ : List (Polymer L)) (qP b2 : Polymer L → Bool)
    (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) marked = true) :
    DistinctExceptionalPolymerPath Γ qP b2 left right marked := by
  let ep := reverseOccurrencePathOfReach Γ.length (incAtDistinct Γ) left right
    (predAt Γ b2) marked hreach
  let pw : CWalk (fun X Y : Polymer L => !(compatibleB X Y))
      (polyAt Γ marked) (polyAt Γ ep.seed) :=
    mapCWalk (edgeB := fun X Y : Polymer L => !(compatibleB X Y)) (polyAt Γ)
      (fun _ _ h => disagreementEdge_incAtDistinct Γ left right h) ep.walk
  have hseedN : ep.seed < Γ.length :=
    (forwardSeed_parts Γ.length left right (predAt Γ b2) ep.seed_true).1
  have hindexLt : ∀ i, i ∈ ep.walk.vertices → i < Γ.length :=
    walk_vertices_lt_of_seed Γ.length (incAtDistinct Γ) left right ep.walk hseedN
  have hoccupied : ∀ i, i ∈ ep.walk.vertices →
      left i || right i = true :=
    walk_vertices_occupied_of_seed Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) ep.walk ep.seed_true
  have hpverts : pw.vertices = ep.walk.vertices.map (polyAt Γ) :=
    vertices_mapCWalk (polyAt Γ)
      (fun _ _ h => disagreementEdge_incAtDistinct Γ left right h) ep.walk
  have hlen : pw.vertices.length ≤ Γ.length := by
    rw [hpverts, List.length_map]
    exact ep.length_le
  have hmem : ∀ X, X ∈ pw.vertices → X ∈ Γ := by
    intro X hX
    rw [hpverts] at hX
    obtain ⟨i, hi, hiX⟩ := List.mem_map.mp hX
    rw [← hiX]
    exact polyAt_mem Γ (hindexLt i hi)
  have hq : ∀ X, X ∈ pw.vertices → qP X = true := by
    intro X hX
    rw [hpverts] at hX
    obtain ⟨i, hi, hiX⟩ := List.mem_map.mp hX
    rw [← hiX]
    cases hli : left i with
    | true => exact hleftQ i (hindexLt i hi) hli
    | false =>
        have hoc := hoccupied i hi
        rw [hli] at hoc
        exact hrightQ i (hindexLt i hi) (of_decide_eq_true hoc)
  exact
    { seed := ep.seed
      seed_true := ep.seed_true
      indexWalk := ep.walk
      index_nodup := ep.nodup
      polymerWalk := pw
      polymer_vertices := hpverts
      length_le := hlen
      ambient_mem := hmem
      q_true := hq }

theorem distinct_exceptional_path_term_le_connectingChainMajorant {w : Q'}
    (hw : (0 : Q') ≤ w)
    (Γ B : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) marked = true)
    (hmarked : b1 (polyAt Γ marked) = true)
    (hBsub : B ∈ sublists Γ) (hBcompat : familyCompatibleB B = true)
    (hBq : B.all qP = true)
    (hBpath : ∀ X,
      X ∈ (distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
        hleftQ hrightQ hreach).polymerWalk.vertices →
      ∀ T, T ∈ B → compatibleB X T = true) :
    let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
      hleftQ hrightQ hreach
    ep.polymerWalk.activityWeight w label * familyActivity w B label ≤
      connectingChainMajorant w qP b1 b2 Γ label := by
  dsimp only
  let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
    hleftQ hrightQ hreach
  have hb2seed : b2 (polyAt Γ ep.seed) = true :=
    (forwardSeed_parts Γ.length left right (predAt Γ b2)
      ep.seed_true).2.2.2
  exact walk_term_le_connectingChainMajorant hw qP b1 b2 Γ B label
    ep.polymerWalk ep.length_le ep.ambient_mem ep.q_true hmarked hb2seed
    hBsub hBcompat hBq hBpath

/-! ## 3. Occurrence extraction from `maskFamily` -/

@[simp] theorem polyAt_cons_zero (X : Polymer L) (Γ : List (Polymer L)) :
    polyAt (X :: Γ) 0 = X := rfl

@[simp] theorem polyAt_cons_succ (X : Polymer L) (Γ : List (Polymer L))
    (i : Nat) : polyAt (X :: Γ) (i + 1) = polyAt Γ i := rfl

/-- Membership in a selected mask family exposes an actual selected ambient
occurrence.  The result is propositional because it is used only to discharge
membership side conditions, never to choose computational data. -/
theorem mem_maskFamilyFrom_occurrence (mask : Nat → Bool) :
    ∀ (Γ : List (Polymer L)) (offset : Nat) (X : Polymer L),
      X ∈ maskFamilyFrom Γ mask offset →
      ∃ i, i < Γ.length ∧ mask (offset + i) = true ∧ polyAt Γ i = X
  | [], _, X, hX => by simp [maskFamilyFrom] at hX
  | A :: Γ, offset, X, hX => by
      cases hm : mask offset with
      | false =>
          simp only [maskFamilyFrom, hm, Bool.false_eq_true, ↓reduceIte] at hX
          obtain ⟨i, hi, hmi, hval⟩ :=
            mem_maskFamilyFrom_occurrence mask Γ (offset + 1) X hX
          refine ⟨i + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
          · rw [show offset + (i + 1) = (offset + 1) + i by omega]
            exact hmi
          · rw [polyAt_cons_succ]
            exact hval
      | true =>
          simp only [maskFamilyFrom, hm, ↓reduceIte] at hX
          rcases List.mem_cons.mp hX with hXA | htail
          · subst X
            exact ⟨0, by simp, by simpa using hm, rfl⟩
          · obtain ⟨i, hi, hmi, hval⟩ :=
              mem_maskFamilyFrom_occurrence mask Γ (offset + 1) X htail
            refine ⟨i + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
            · rw [show offset + (i + 1) = (offset + 1) + i by omega]
              exact hmi
            · rw [polyAt_cons_succ]
              exact hval

theorem mem_maskFamily_occurrence (Γ : List (Polymer L))
    (mask : Nat → Bool) {X : Polymer L} (hX : X ∈ maskFamily Γ mask) :
    ∃ i, i < Γ.length ∧ mask i = true ∧ polyAt Γ i = X := by
  unfold maskFamily at hX
  obtain ⟨i, hi, hmi, hval⟩ :=
    mem_maskFamilyFrom_occurrence mask Γ 0 X hX
  exact ⟨i, hi, by simpa using hmi, hval⟩

theorem maskFamily_all_of_pointwise (Γ : List (Polymer L))
    (mask : Nat → Bool) (p : Polymer L → Bool)
    (h : ∀ i, i < Γ.length → mask i = true → p (polyAt Γ i) = true) :
    (maskFamily Γ mask).all p = true := by
  apply List.all_eq_true.mpr
  intro X hX
  obtain ⟨i, hi, hmi, hval⟩ := mem_maskFamily_occurrence Γ mask hX
  rw [← hval]
  exact h i hi hmi

/-! ## 4. Lifting the exterior cut to an actual background family -/

theorem maskFamilyFrom_sublist_of_submask
    (small big : Nat → Bool)
    (hsub : ∀ i, small i = true → big i = true) :
    ∀ (Γ : List (Polymer L)) (offset : Nat),
      (maskFamilyFrom Γ small offset).Sublist
        (maskFamilyFrom Γ big offset)
  | [], _ => by
      simp [maskFamilyFrom]
  | A :: Γ, offset => by
      have ih := maskFamilyFrom_sublist_of_submask small big hsub Γ (offset + 1)
      cases hs : small offset with
      | false =>
          cases hb : big offset with
          | false =>
              simpa [maskFamilyFrom, hs, hb] using ih
          | true =>
              simpa [maskFamilyFrom, hs, hb] using List.Sublist.cons A ih
      | true =>
          have hb : big offset = true := hsub offset hs
          simpa [maskFamilyFrom, hs, hb] using List.Sublist.cons₂ A ih

theorem maskFamily_sublist_of_submask
    (Γ : List (Polymer L)) (small big : Nat → Bool)
    (hsub : ∀ i, small i = true → big i = true) :
    (maskFamily Γ small).Sublist (maskFamily Γ big) := by
  unfold maskFamily
  exact maskFamilyFrom_sublist_of_submask small big hsub Γ 0

theorem familyCompatibleB_of_sublist {A B : List (Polymer L)}
    (hsub : A.Sublist B) (hB : familyCompatibleB B = true) :
    familyCompatibleB A = true := by
  induction hsub with
  | slnil => rfl
  | @cons X A B hsub ih =>
      rw [familyCompatibleB_cons] at hB
      exact ih ((Bool.and_eq_true _ _).mp hB).2
  | @cons₂ X A B hsub ih =>
      rw [familyCompatibleB_cons] at hB ⊢
      have hp := (Bool.and_eq_true _ _).mp hB
      apply (Bool.and_eq_true _ _).mpr
      constructor
      · apply List.all_eq_true.mpr
        intro Y hYA
        exact List.all_eq_true.mp hp.1 Y (List.Sublist.mem hYA hsub)
      · exact ih hp.2

theorem outsideMask_submask (cut mask : Nat → Bool) (i : Nat) :
    outsideMask cut mask i = true → mask i = true :=
  fun h => (outsideMask_parts cut mask h).1

theorem outsideMask_familyCompatible
    (Γ : List (Polymer L)) (cut mask : Nat → Bool)
    (hcompat : familyCompatibleB (maskFamily Γ mask) = true) :
    familyCompatibleB (maskFamily Γ (outsideMask cut mask)) = true :=
  familyCompatibleB_of_sublist
    (maskFamily_sublist_of_submask Γ (outsideMask cut mask) mask
      (outsideMask_submask cut mask)) hcompat

theorem compatibleB_of_incAtDistinct_symConflict_false
    (Γ : List (Polymer L)) {i j : Nat} (hij : i ≠ j)
    (h : symConflict (incAtDistinct Γ) i j = false) :
    compatibleB (polyAt Γ i) (polyAt Γ j) = true := by
  have hijInc : incAtDistinct Γ i j = false := by
    cases hi : incAtDistinct Γ i j <;>
      cases hj : incAtDistinct Γ j i <;>
      simp_all [symConflict]
  unfold incAtDistinct at hijInc
  rw [decide_eq_true hij] at hijInc
  cases hc : compatibleB (polyAt Γ i) (polyAt Γ j) <;> simp_all

/-- Every member of the outside-left mask family is compatible with every
vertex of the corrected exceptional polymer path. -/
theorem distinct_path_compatible_with_outside_left
    (Γ : List (Polymer L)) (qP b2 : Polymer L → Bool)
    (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) marked = true)
    (hleft : ∀ i j, i ≠ j → left i = true → left j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hright : ∀ i j, i ≠ j → right i = true → right j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true) :
    let cut := forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2)
    let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
      hleftQ hrightQ hreach
    ∀ X, X ∈ ep.polymerWalk.vertices →
      ∀ T, T ∈ maskFamily Γ (outsideMask cut left) →
        compatibleB X T = true := by
  dsimp only
  let cut := forwardComponent Γ.length (incAtDistinct Γ) left right
    (predAt Γ b2)
  let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
    hleftQ hrightQ hreach
  intro X hX T hT
  rw [ep.polymer_vertices] at hX
  obtain ⟨i, hiPath, hiX⟩ := List.mem_map.mp hX
  obtain ⟨j, hjN, hjOutside, hjT⟩ :=
    mem_maskFamily_occurrence Γ (outsideMask cut left) hT
  have hiCut : cut i = true := by
    exact walk_vertices_in_component Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) ep.indexWalk hreach i hiPath
  have hout := outsideMask_parts cut left hjOutside
  have hij : i ≠ j := by
    intro hij
    subst j
    rw [hiCut] at hout
    exact Bool.false_ne_true hout.2.symm
  have hsym : symConflict (incAtDistinct Γ) i j = false :=
    component_compatible_with_outside_left Γ.length (incAtDistinct Γ)
      left right (predAt Γ b2)
      (sameSide_guard_incAtDistinct Γ left hleft)
      (sameSide_guard_incAtDistinct Γ right hright)
      hiCut hjN hjOutside
  rw [← hiX, ← hjT]
  exact compatibleB_of_incAtDistinct_symConflict_false Γ hij hsym

/-- The outside-left background is now constructed rather than assumed. -/
theorem distinct_exceptional_outside_left_term_le_carrier {w : Q'}
    (hw : (0 : Q') ≤ w)
    (Γ : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2) marked = true)
    (hmarked : b1 (polyAt Γ marked) = true)
    (hleftFamily : familyCompatibleB (maskFamily Γ left) = true)
    (hleft : ∀ i j, i ≠ j → left i = true → left j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hright : ∀ i j, i ≠ j → right i = true → right j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true) :
    let cut := forwardComponent Γ.length (incAtDistinct Γ) left right
      (predAt Γ b2)
    let B := maskFamily Γ (outsideMask cut left)
    let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
      hleftQ hrightQ hreach
    ep.polymerWalk.activityWeight w label * familyActivity w B label ≤
      connectingChainMajorant w qP b1 b2 Γ label := by
  dsimp only
  let cut := forwardComponent Γ.length (incAtDistinct Γ) left right
    (predAt Γ b2)
  let B := maskFamily Γ (outsideMask cut left)
  let ep := distinctExceptionalPolymerPathOfReach Γ qP b2 left right marked
    hleftQ hrightQ hreach
  apply distinct_exceptional_path_term_le_connectingChainMajorant hw Γ B
    qP b1 b2 label left right marked hleftQ hrightQ hreach hmarked
  · exact maskFamily_mem_sublists Γ (outsideMask cut left)
  · exact outsideMask_familyCompatible Γ cut left hleftFamily
  · exact maskFamily_all_of_pointwise Γ (outsideMask cut left) qP
      (fun i hi hsel => hleftQ i hi (outsideMask_parts cut left hsel).1)
  · exact distinct_path_compatible_with_outside_left Γ qP b2 left right
      marked hleftQ hrightQ hreach hleft hright

/-! ## 5. Reverse recovery and injectivity of the corrected switch -/

/-- Generic reverse recovery specializes non-vacuously to the corrected
occurrence graph.  The output pair alone recomputes the original forward
cut, with the sides reversed. -/
theorem reverse_component_recovers_incAtDistinct
    (Γ : List (Polymer L)) (b2 : Polymer L → Bool)
    (left right : Nat → Bool)
    (hleft : ∀ i j, i ≠ j → left i = true → left j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hright : ∀ i j, i ≠ j → right i = true → right j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hrightGood : ∀ i, right i = true → predAt Γ b2 i = false)
    (i : Nat) :
    reverseComponent Γ.length (incAtDistinct Γ)
        (switchedLeft Γ.length (incAtDistinct Γ) left right (predAt Γ b2))
        (switchedRight Γ.length (incAtDistinct Γ) left right (predAt Γ b2))
        (predAt Γ b2) i =
      forwardComponent Γ.length (incAtDistinct Γ) left right
        (predAt Γ b2) i := by
  exact reverse_component_recovers Γ.length (incAtDistinct Γ) left right
    (predAt Γ b2)
    (sameSide_guard_incAtDistinct Γ left hleft)
    (sameSide_guard_incAtDistinct Γ right hright)
    hrightGood i

/-- Although the corrected switch uses a cut computed from its source pair,
it is injective on the admissible domain.  Equality of the two output masks
first forces equality of their reverse-recovered cuts; the fixed-cut
involution then recovers both input masks occurrence by occurrence. -/
theorem distinct_switched_pair_injective
    (Γ : List (Polymer L)) (b2 : Polymer L → Bool)
    (left₁ right₁ left₂ right₂ : Nat → Bool)
    (hleft₁ : ∀ i j, i ≠ j → left₁ i = true → left₁ j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hright₁ : ∀ i j, i ≠ j → right₁ i = true → right₁ j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hgood₁ : ∀ i, right₁ i = true → predAt Γ b2 i = false)
    (hleft₂ : ∀ i j, i ≠ j → left₂ i = true → left₂ j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hright₂ : ∀ i j, i ≠ j → right₂ i = true → right₂ j = true →
      compatibleB (polyAt Γ i) (polyAt Γ j) = true)
    (hgood₂ : ∀ i, right₂ i = true → predAt Γ b2 i = false)
    (houtLeft : ∀ i,
      switchedLeft Γ.length (incAtDistinct Γ) left₁ right₁ (predAt Γ b2) i =
        switchedLeft Γ.length (incAtDistinct Γ) left₂ right₂
          (predAt Γ b2) i)
    (houtRight : ∀ i,
      switchedRight Γ.length (incAtDistinct Γ) left₁ right₁ (predAt Γ b2) i =
        switchedRight Γ.length (incAtDistinct Γ) left₂ right₂
          (predAt Γ b2) i) :
    (∀ i, left₁ i = left₂ i) ∧ (∀ i, right₁ i = right₂ i) := by
  let cut₁ := forwardComponent Γ.length (incAtDistinct Γ) left₁ right₁
    (predAt Γ b2)
  let cut₂ := forwardComponent Γ.length (incAtDistinct Γ) left₂ right₂
    (predAt Γ b2)
  have hsl :
      switchedLeft Γ.length (incAtDistinct Γ) left₁ right₁ (predAt Γ b2) =
        switchedLeft Γ.length (incAtDistinct Γ) left₂ right₂
          (predAt Γ b2) :=
    funext houtLeft
  have hsr :
      switchedRight Γ.length (incAtDistinct Γ) left₁ right₁ (predAt Γ b2) =
        switchedRight Γ.length (incAtDistinct Γ) left₂ right₂
          (predAt Γ b2) :=
    funext houtRight
  have hcut : ∀ i, cut₁ i = cut₂ i := by
    intro i
    have hr₁ := reverse_component_recovers_incAtDistinct Γ b2 left₁ right₁
      hleft₁ hright₁ hgood₁ i
    have hr₂ := reverse_component_recovers_incAtDistinct Γ b2 left₂ right₂
      hleft₂ hright₂ hgood₂ i
    dsimp only [cut₁, cut₂]
    rw [← hr₁, ← hr₂, hsl, hsr]
  have hcutFun : cut₁ = cut₂ := funext hcut
  apply swapMasks_pair_injective cut₁ left₁ right₁ left₂ right₂
  · intro i
    have h := houtLeft i
    unfold switchedLeft at h
    change swapLeftMask cut₁ left₁ right₁ i =
      swapLeftMask cut₂ left₂ right₂ i at h
    rw [← hcutFun] at h
    exact h
  · intro i
    have h := houtRight i
    unfold switchedRight at h
    change swapRightMask cut₁ left₁ right₁ i =
      swapRightMask cut₂ left₂ right₂ i at h
    rw [← hcutFun] at h
    exact h

#print axioms sameSide_guard_incAtDistinct
#print axioms distinctExceptionalPolymerPathOfReach
#print axioms distinct_exceptional_path_term_le_connectingChainMajorant
#print axioms polyAt_cons_zero
#print axioms polyAt_cons_succ
#print axioms mem_maskFamilyFrom_occurrence
#print axioms mem_maskFamily_occurrence
#print axioms maskFamily_all_of_pointwise
#print axioms maskFamilyFrom_sublist_of_submask
#print axioms maskFamily_sublist_of_submask
#print axioms familyCompatibleB_of_sublist
#print axioms outsideMask_submask
#print axioms outsideMask_familyCompatible
#print axioms compatibleB_of_incAtDistinct_symConflict_false
#print axioms distinct_path_compatible_with_outside_left
#print axioms distinct_exceptional_outside_left_term_le_carrier
#print axioms reverse_component_recovers_incAtDistinct
#print axioms distinct_switched_pair_injective

end YMGap.Continuum.XiExceptionalDistinctInjection
