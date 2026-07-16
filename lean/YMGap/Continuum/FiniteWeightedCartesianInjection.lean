/-
# Finite weighted Cartesian injections

Constructive list lemmas for turning an injective, weight-dominating map on a
finite Cartesian source into a rational sum bound.  The implementation uses
only duplicate-free lists and first-occurrence erasure; no cardinality,
quotient, choice, or finite-set API is needed.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching

namespace YMGap.Continuum.FiniteWeightedCartesianInjection

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

def cartesian (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

theorem mem_cartesian_iff (xs : List A) (ys : List B) (pair : A × B) :
    pair ∈ cartesian xs ys ↔ pair.1 ∈ xs ∧ pair.2 ∈ ys := by
  constructor
  · intro hpair
    obtain ⟨x, hx, hmap⟩ := List.mem_flatMap.mp hpair
    obtain ⟨y, hy, hp⟩ := List.mem_map.mp hmap
    have hxEq : x = pair.1 := by
      rw [← hp]
    have hyEq : y = pair.2 := by
      rw [← hp]
    exact ⟨hxEq ▸ hx, hyEq ▸ hy⟩
  · intro hpair
    apply List.mem_flatMap.mpr
    exact ⟨pair.1, hpair.1,
      List.mem_map.mpr ⟨pair.2, hpair.2, by cases pair; rfl⟩⟩

private theorem nodup_map_pair_left (x : A) :
    ∀ {ys : List B}, ys.Nodup →
      (ys.map (fun y => (x, y))).Nodup
  | [], _ => List.nodup_nil
  | y :: ys, hys => by
      have hparts := List.nodup_cons.mp hys
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmem
        have hyz : y = z := (congrArg Prod.snd heq).symm
        exact hparts.1 (hyz ▸ hz)
      · exact nodup_map_pair_left x hparts.2

theorem cartesian_nodup (xs : List A) (ys : List B)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    (cartesian xs ys).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hparts := List.nodup_cons.mp hxs
      unfold cartesian
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨nodup_map_pair_left x hys, ih hparts.2, ?_⟩
      intro pair hhead other htail heq
      obtain ⟨y, hy, hpair⟩ := List.mem_map.mp hhead
      obtain ⟨z, hz, hzmap⟩ := List.mem_flatMap.mp htail
      obtain ⟨w, hw, hzw⟩ := List.mem_map.mp hzmap
      rw [← hpair, ← hzw] at heq
      have hxz : x = z := by injection heq
      exact hparts.1 (hxz ▸ hz)

private theorem nodup_of_map_nodup (value : A → B) :
    ∀ {xs : List A}, (xs.map value).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hparts := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hx
        exact hparts.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)
      · exact nodup_of_map_nodup value hparts.2

theorem attach_nodup_of_nodup (xs : List A) (hxs : xs.Nodup) :
    xs.attach.Nodup := by
  apply nodup_of_map_nodup Subtype.val
  rw [List.attach_map_subtype_val]
  exact hxs

theorem listQSum_attach (weight : A → Q') (xs : List A) :
    listQSum (fun item : {x // x ∈ xs} => weight item.val) xs.attach =
      listQSum weight xs := by
  rw [← listQSum_map weight Subtype.val xs.attach]
  rw [List.attach_map_subtype_val]

theorem listQSum_filter_partition (weight : A → Q')
    (test : A → Bool) :
    ∀ xs : List A,
      listQSum weight xs ≈
        listQSum weight (xs.filter test) +
          listQSum weight (xs.filter (fun x => !(test x)))
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | x :: xs => by
      have ih := listQSum_filter_partition weight test xs
      cases hx : test x with
      | false =>
          simp only [listQSum, List.filter_cons, hx,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv (weight x)
                (listQSum weight (xs.filter test)))) ?_
          exact Q'.add_assoc_eqv _ _ _
      | true =>
          simp only [listQSum, List.filter_cons, hx, ↓reduceIte,
            Bool.not_true, Bool.false_eq_true]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem listQSum_mul_left (a : Q') (weight : B → Q') :
    ∀ ys : List B,
      listQSum (fun y => a * weight y) ys ≈
        a * listQSum weight ys
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | y :: ys => by
      change a * weight y + listQSum (fun z => a * weight z) ys ≈
        a * (weight y + listQSum weight ys)
      exact Q'.eqv_trans _
        (a * weight y + a * listQSum weight ys) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_left a weight ys))
        (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

theorem listQSum_cartesian_product
    (leftWeight : A → Q') (rightWeight : B → Q') :
    ∀ (xs : List A) (ys : List B),
      listQSum (fun pair =>
          leftWeight pair.1 * rightWeight pair.2)
          (cartesian xs ys) ≈
        listQSum leftWeight xs * listQSum rightWeight ys
  | [], ys => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | x :: xs, ys => by
      unfold cartesian
      simp only [List.flatMap_cons]
      refine Q'.eqv_trans _
        (listQSum (fun pair =>
            leftWeight pair.1 * rightWeight pair.2)
            (ys.map (fun y => (x, y))) +
          listQSum (fun pair =>
            leftWeight pair.1 * rightWeight pair.2)
            (cartesian xs ys)) _ ?_ ?_
      · exact listQSum_append _ _ _
      rw [listQSum_map]
      refine Q'.eqv_trans _
        (leftWeight x * listQSum rightWeight ys +
          listQSum leftWeight xs * listQSum rightWeight ys) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (listQSum_mul_left (leftWeight x) rightWeight ys)
          (listQSum_cartesian_product leftWeight rightWeight xs ys)
      exact Q'.eqv_symm
        (Q'.add_mul_eqv (leftWeight x)
          (listQSum leftWeight xs) (listQSum rightWeight ys))

theorem mem_erase_of_mem_of_ne [DecidableEq A] {x y : A}
    (hxy : x ≠ y) :
    ∀ {xs : List A}, x ∈ xs → x ∈ xs.erase y
  | [], hx => by cases hx
  | a :: xs, hx => by
      by_cases hay : a = y
      · subst a
        rw [List.erase_cons_head]
        exact (List.mem_cons.mp hx).resolve_left hxy
      · rw [List.erase_cons_tail (by simpa [hay])]
        rcases List.mem_cons.mp hx with hxa | hxs
        · exact List.mem_cons.mpr (Or.inl hxa)
        · exact List.mem_cons.mpr
            (Or.inr (mem_erase_of_mem_of_ne hxy hxs))

theorem listQSum_erase_decompose [DecidableEq A]
    (weight : A → Q') :
    ∀ (xs : List A) (y : A), y ∈ xs →
      listQSum weight xs ≈
        weight y + listQSum weight (xs.erase y)
  | [], _, hy => by cases hy
  | x :: xs, y, hy => by
      by_cases hxy : x = y
      · subst x
        rw [List.erase_cons_head]
        exact Q'.eqv_refl _
      · have hyTail : y ∈ xs :=
          (List.mem_cons.mp hy).resolve_left (fun h => hxy h.symm)
        rw [List.erase_cons_tail (a := y) (b := x) (by simp [hxy])]
        have ih := listQSum_erase_decompose weight xs y hyTail
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (weight x) _ _ ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_assoc_eqv (weight x) (weight y)
              (listQSum weight (xs.erase y)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            (weight x + weight y) (weight y + weight x)
            (listQSum weight (xs.erase y))
            (Q'.add_comm_eqv (weight x) (weight y))) ?_
        exact Q'.add_assoc_eqv (weight y) (weight x)
          (listQSum weight (xs.erase y))

private theorem listQSum_nonnegative_on (weight : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → (0 : Q') ≤ weight x) →
      (0 : Q') ≤ listQSum weight xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h =>
      Q'.zero_le_add _ _
        (h x List.mem_cons_self)
        (listQSum_nonnegative_on weight xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Constructive finite weighted-injection bound for the repository's native
`listQSum`. -/
theorem listQSum_le_of_injective [DecidableEq B]
    (source : List A) (target : List B)
    (sourceWeight : A → Q') (targetWeight : B → Q')
    (encode : A → B)
    (hsource : source.Nodup)
    (hmem : ∀ x, x ∈ source → encode x ∈ target)
    (hinjective : ∀ x, x ∈ source → ∀ y, y ∈ source →
      encode x = encode y → x = y)
    (hterm : ∀ x, x ∈ source →
      sourceWeight x ≤ targetWeight (encode x))
    (htarget : ∀ y, y ∈ target → (0 : Q') ≤ targetWeight y) :
    listQSum sourceWeight source ≤ listQSum targetWeight target := by
  induction source generalizing target with
  | nil =>
      exact listQSum_nonnegative_on targetWeight target htarget
  | cons x xs ih =>
      have hnd := List.nodup_cons.mp hsource
      have hxmem : x ∈ x :: xs := List.mem_cons_self
      have henc : encode x ∈ target := hmem x hxmem
      have hrest : listQSum sourceWeight xs ≤
          listQSum targetWeight (target.erase (encode x)) := by
        apply ih (target.erase (encode x)) hnd.2
        · intro y hy
          have hySource : y ∈ x :: xs := List.mem_cons_of_mem x hy
          have hne : encode y ≠ encode x := by
            intro heq
            have hyx := hinjective y hySource x hxmem heq
            subst y
            exact hnd.1 hy
          exact mem_erase_of_mem_of_ne hne (hmem y hySource)
        · intro y hy z hz heq
          exact hinjective y (List.mem_cons_of_mem x hy)
            z (List.mem_cons_of_mem x hz) heq
        · intro y hy
          exact hterm y (List.mem_cons_of_mem x hy)
        · intro y hy
          exact htarget y (List.mem_of_mem_erase hy)
      have hadd : sourceWeight x + listQSum sourceWeight xs ≤
          targetWeight (encode x) +
            listQSum targetWeight (target.erase (encode x)) :=
        Q'.add_le_add (hterm x hxmem) hrest
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.eqv_symm
          (listQSum_erase_decompose targetWeight target (encode x) henc)))

end YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.cartesian_nodup
#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.attach_nodup_of_nodup
#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.listQSum_attach
#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.listQSum_filter_partition
#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.listQSum_cartesian_product
#print axioms YMGap.Continuum.FiniteWeightedCartesianInjection.listQSum_le_of_injective
