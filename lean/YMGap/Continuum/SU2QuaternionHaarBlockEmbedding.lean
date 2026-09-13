/-
# Injective placement of a finite quaternion Haar carrier

An ordered, duplicate-free list of target blocks places each source block
without identifying link variables. The polynomial map reads the unique
source index at each target block; absent target blocks read the zero tail.
For supported source polynomials, every unused target block integrates to
one. Thus the ORIGINAL normalized quaternion Haar integral is preserved.

This is finite product-Haar geometry, not an interacting marginal identity.
The latter additionally needs the original action and insertion pins.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
import YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

structure BlockEmbedding (source target : Nat) : Type where
  image : List Nat
  length : image.length = source
  nodup : image.Nodup
  physical : ∀ block, block ∈ image → block < target

private theorem getD_mem {A : Type} (xs : List A) (fallback : A) {i : Nat}
    (hi : i < xs.length) : xs.getD i fallback ∈ xs := by
  rw [← List.getElem_eq_getD (h := hi)]
  exact List.getElem_mem hi

private theorem index_getD : ∀ (xs : List Nat), xs.Nodup → ∀ i, i < xs.length → listIndexOf (xs.getD i 0) xs = i
  | [], _, i, hi => by simp at hi
  | a :: xs, _, 0, _ => by
      change (if a = a then 0 else listIndexOf a xs + 1) = 0
      rw [if_pos rfl]
  | a :: xs, hn, i+1, hi => by
      have hparts := List.nodup_cons.mp hn
      have hi' : i < xs.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
      have hne : xs.getD i 0 ≠ a := fun h => hparts.1 (h ▸ getD_mem xs 0 hi')
      simp only [List.getD_cons_succ, listIndexOf, if_neg hne, index_getD xs hparts.2 i hi']

private theorem index_absent (b : Nat) : ∀ (xs : List Nat), b ∉ xs → listIndexOf b xs = xs.length
  | [], _ => rfl
  | a :: xs, hb => by
      have hne : b ≠ a := fun h => hb (h ▸ List.mem_cons_self)
      have hout : b ∉ xs := fun h => hb (List.mem_cons_of_mem a h)
      simp only [listIndexOf, if_neg hne, index_absent b xs hout, List.length_cons]

namespace BlockEmbedding

variable {source target : Nat} (E : BlockEmbedding source target)

def block (i : Nat) : Nat := E.image.getD i 0

def index (b : Nat) : Nat := listIndexOf b E.image

theorem block_mem {i : Nat} (hi : i < source) : E.block i ∈ E.image :=
  getD_mem E.image 0 (by rw [E.length]; exact hi)

theorem block_lt {i : Nat} (hi : i < source) : E.block i < target := E.physical _ (E.block_mem hi)

theorem index_block {i : Nat} (hi : i < source) : E.index (E.block i) = i :=
  index_getD E.image E.nodup i (by rw [E.length]; exact hi)

theorem block_index {b : Nat} (hb : b ∈ E.image) : E.block (E.index b) = b := getD_listIndexOf_of_mem 0 b E.image hb

theorem index_lt {b : Nat} (hb : b ∈ E.image) : E.index b < source :=
  Nat.lt_of_lt_of_eq (listIndexOf_lt_of_mem b E.image hb) E.length

theorem index_not_mem {b : Nat} (hb : b ∉ E.image) : E.index b = source :=
  (index_absent b E.image hb).trans E.length

theorem index_eq_block {i b : Nat} (hi : i < source) : E.index b = i ↔ b = E.block i := by
  constructor
  · intro he
    by_cases hb : b ∈ E.image
    · rw [← he, E.block_index hb]
    · have hout := E.index_not_mem hb
      omega
  · intro he
    rw [he, E.index_block hi]

theorem index_injective {a b : Nat} (ha : a ∈ E.image) (hb : b ∈ E.image)
    (h : E.index a = E.index b) : a = b := by
  have he := congrArg E.block h
  rw [E.block_index ha, E.block_index hb] at he
  exact he

theorem index_order_perm : (E.image.map E.index).Perm (quaternionBlockOrder source) := by
  apply perm_of_nodup_mem_iff _ _
    (nodup_map_of_injOn _ _ E.nodup (fun _ ha _ hb => E.index_injective ha hb))
    (quaternionBlockOrder_nodup source)
  intro i
  constructor
  · intro hi
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
    exact (mem_quaternionBlockOrder_iff _ _).mpr (E.index_lt hb)
  · intro hi
    have hi' := (mem_quaternionBlockOrder_iff _ _).mp hi
    exact List.mem_map.mpr ⟨E.block i, E.block_mem hi', E.index_block hi'⟩

def selected : List Nat := (quaternionBlockOrder target).filter (fun b => decide (b ∈ E.image))

theorem selected_perm : E.selected.Perm E.image := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (quaternionBlockOrder_nodup target)) E.nodup
  intro b
  constructor
  · intro hb
    exact of_decide_eq_true (List.mem_filter.mp hb).2
  · intro hb
    exact List.mem_filter.mpr ⟨(mem_quaternionBlockOrder_iff _ _).mpr (E.physical _ hb), decide_eq_true hb⟩

def exponents (m : List Nat) : List Nat :=
  List.ofFn (fun c : Fin (4*target) => exponentAt m (4 * E.index (c.val / 4) + c.val % 4))

theorem exponents_length (m : List Nat) : (E.exponents m).length = 4*target := List.length_ofFn

theorem exponent_pin (m : List Nat) {c : Nat} (hc : c < 4*target) :
    exponentAt (E.exponents m) c = exponentAt m (4 * E.index (c / 4) + c % 4) := by
  unfold exponentAt
  rw [← List.getElem_eq_getD (h := by rw [E.exponents_length]; exact hc)]
  exact List.getElem_ofFn (h := by rw [List.length_ofFn]; exact hc)

theorem blockMoment_pin (m : List Nat) {b : Nat} (hb : b < target) :
    quaternionBlockMoment (E.exponents m) b = quaternionBlockMoment m (E.index b) := by
  unfold quaternionBlockMoment
  rw [E.exponent_pin m (by omega), E.exponent_pin m (by omega),
    E.exponent_pin m (by omega), E.exponent_pin m (by omega)]
  have decomp (c : Nat) (hc : c < 4) : (4*b+c)/4 = b ∧ (4*b+c)%4 = c := ⟨by omega, by omega⟩
  have h0 := decomp 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0.1, h0.2, (decomp 1 (by omega)).1, (decomp 1 (by omega)).2,
    (decomp 2 (by omega)).1, (decomp 2 (by omega)).2,
    (decomp 3 (by omega)).1, (decomp 3 (by omega)).2]
  rfl

private theorem exponent_zero : ∀ (m : List Nat) (c : Nat), m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero m c (by simp only [List.length_cons] at h; omega)

theorem unused_moment (m : List Nat) (hm : m.length ≤ 4*source) {b : Nat}
    (hb : b < target) (hout : b ∉ E.image) : quaternionBlockMoment (E.exponents m) b ≈ 1 := by
  rw [E.blockMoment_pin m hb, index, index_absent b E.image hout, E.length]
  unfold quaternionBlockMoment
  rw [exponent_zero m _ hm, exponent_zero m _ (by omega), exponent_zero m _ (by omega), exponent_zero m _ (by omega)]
  exact sphereMoment4_one

theorem haar_monomial (m : List Nat) (hm : m.length ≤ 4*source) :
    quaternionHaarMono target (E.exponents m) ≈ quaternionHaarMono source m := by
  unfold quaternionHaarMono
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq (E.exponents_length m)), List.drop_eq_nil_of_le hm]
  change quaternionHaarPrefix target (E.exponents m) ≈ quaternionHaarPrefix source m
  refine Q'.eqv_trans _ _ _ (quaternionHaarPrefix_eq_block_product _ _) ?_
  have hremove : listQProduct (quaternionBlockMoment (E.exponents m)) (quaternionBlockOrder target) ≈
      listQProduct (quaternionBlockMoment (E.exponents m)) E.selected := by
    apply listQProduct_sublist_vacuum _ List.filter_sublist (quaternionBlockOrder_nodup target)
    intro b hb hout
    apply E.unused_moment m hm ((mem_quaternionBlockOrder_iff _ _).mp hb)
    intro hin
    exact hout (List.mem_filter.mpr ⟨hb, decide_eq_true hin⟩)
  refine Q'.eqv_trans _ _ _ hremove (Q'.eqv_trans _ _ _ (listQProduct_perm _ E.selected_perm) ?_)
  refine Q'.eqv_trans _ (listQProduct (quaternionBlockMoment m) (E.image.map E.index)) _ ?_ ?_
  · rw [listQProduct_map]
    exact listQProduct_congr_eqv _ _ _ (fun b hb => Q'.eqv_of_eq (E.blockMoment_pin m (E.physical _ hb)))
  · exact Q'.eqv_trans _ _ _ (listQProduct_perm _ E.index_order_perm)
      (Q'.eqv_symm (quaternionHaarPrefix_eq_block_product _ _))

def polynomial (p : RatPoly) : RatPoly := p.map (fun term => (E.exponents term.1, term.2))

theorem polynomial_supported (p : RatPoly) : SupportedQuaternionBlocks target (E.polynomial p) := by
  intro term ht
  obtain ⟨sourceTerm, _, rfl⟩ := List.mem_map.mp ht
  exact Nat.le_of_eq (E.exponents_length sourceTerm.1)

theorem haar : ∀ p : RatPoly, SupportedQuaternionBlocks source p →
    quaternionHaar target (E.polynomial p) ≈ quaternionHaar source p
  | [], _ => Q'.eqv_refl 0
  | term :: rest, hp =>
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (E.haar_monomial term.1 (hp term List.mem_cons_self)))
        (haar rest (fun t ht => hp t (List.mem_cons_of_mem term ht)))

end BlockEmbedding
end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.block
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.block_mem
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.block_lt
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_block
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.block_index
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_lt
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_not_mem
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_eq_block
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_injective
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.index_order_perm
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.selected
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.selected_perm
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.exponents
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.exponents_length
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.exponent_pin
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.blockMoment_pin
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.unused_moment
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.haar_monomial
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.haar
