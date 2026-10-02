/-
# Exact-key sparse collection for rational quaternion polynomials

This computable collector merges the first equal monomial key and discards
coefficients with zero numerator. It preserves every coefficient probe and
never introduces a new key. Consequently a supplied finite key cover bounds
the number of collected terms, independently of raw multiplicities. This is
only a representation-length bound: coefficient bit sizes, collection work,
and any Yang--Mills margin estimate are not controlled here.
-/

import YMGap.Continuum.SU2QuaternionRatPolyDifferential
import YMGap.Continuum.SU2QuaternionBlockDegreeBound
import YMGap.Continuum.FiniteBoolGraphSimplePaths

namespace YMGap.Continuum.SU2QuaternionSparseCoefficientCollector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionBlockDegreeBound (DegreeLE)

local infix:50 " ≈ " => Q'.eqv

/-- Merge into the first identical key, deleting a zero sum. No order on keys
or quotient by sphere relations is used. -/
def insertKey (key : List Nat) (coefficient : Q') : RatPoly → RatPoly
  | [] => if coefficient.num = 0 then [] else [(key, coefficient)]
  | (other, value) :: rest =>
      if key = other then
        let combined := coefficient + value
        if combined.num = 0 then rest else (other, combined) :: rest
      else (other, value) :: insertKey key coefficient rest

/-- A deterministic finite sparse presentation of the same rational
polynomial coefficients. -/
def collect : RatPoly → RatPoly
  | [] => []
  | term :: rest => insertKey term.1 term.2 (collect rest)

private theorem weighted_zero (weight : List Nat → Q')
    (key : List Nat) (coefficient : Q') (hz : coefficient.num = 0) :
    coefficient * weight key ≈ 0 := by
  have hc : coefficient ≈ 0 := by
    show coefficient.num * ((0 : Q').den : Int) =
      (0 : Q').num * (coefficient.den : Int)
    rw [hz]
    change (0 : Int) * 1 = 0 * (coefficient.den : Int)
    simp
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
    (Q'.zero_mul_eqv _)

/-- Insertion preserves all rational monomial-weighted sums. -/
theorem weighted_insert (weight : List Nat → Q')
    (key : List Nat) (coefficient : Q') :
    ∀ p : RatPoly,
      ratWeightedSum weight (insertKey key coefficient p) ≈
        coefficient * weight key + ratWeightedSum weight p
  | [] => by
      by_cases hz : coefficient.num = 0
      · simp only [insertKey, if_pos hz, ratWeightedSum]
        exact Q'.eqv_symm
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (weighted_zero weight key coefficient hz)
              (Q'.eqv_refl 0))
            (QPoly.q_zero_add_eqv 0))
      · simp only [insertKey, if_neg hz, ratWeightedSum]
        exact Q'.eqv_refl _
  | (other, value) :: rest => by
      by_cases he : key = other
      · subst other
        let combined := coefficient + value
        by_cases hz : combined.num = 0
        · rw [insertKey, if_pos rfl, if_pos hz]
          change ratWeightedSum weight rest ≈
            coefficient * weight key +
              (value * weight key + ratWeightedSum weight rest)
          refine Q'.eqv_trans _ (0 + ratWeightedSum weight rest) _
            (Q'.eqv_symm (QPoly.q_zero_add_eqv _)) ?_
          refine Q'.eqv_trans _
            ((coefficient * weight key + value * weight key) +
              ratWeightedSum weight rest) _ ?_ (Q'.add_assoc_eqv _ _ _)
          exact Q'.add_eqv_congr'
            (Q'.eqv_symm (Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.add_mul_eqv coefficient value (weight key)))
              (weighted_zero weight key combined hz)))
            (Q'.eqv_refl _)
        · rw [insertKey, if_pos rfl, if_neg hz]
          change combined * weight key + ratWeightedSum weight rest ≈
            coefficient * weight key +
              (value * weight key + ratWeightedSum weight rest)
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_mul_eqv coefficient value (weight key)))
            (Q'.add_assoc_eqv _ _ _)
      · simp only [insertKey, if_neg he, ratWeightedSum]
        refine Q'.eqv_trans _
          (value * weight other +
            (coefficient * weight key + ratWeightedSum weight rest)) _
          (Q'.add_eqv_congr_left _ _ _
            (weighted_insert weight key coefficient rest)) ?_
        refine Q'.eqv_trans _
          ((value * weight other + coefficient * weight key) +
            ratWeightedSum weight rest) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((coefficient * weight key + value * weight other) +
            ratWeightedSum weight rest) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
        exact Q'.add_assoc_eqv _ _ _

/-- Every arbitrary coefficient probe sees exactly the original polynomial. -/
theorem collect_coeff (p : RatPoly) : RatPolyCoeffEqv (collect p) p := by
  intro weight
  induction p with
  | nil => exact Q'.eqv_refl 0
  | cons term rest ih =>
      change ratWeightedSum weight (insertKey term.1 term.2 (collect rest)) ≈
        term.2 * weight term.1 + ratWeightedSum weight rest
      exact Q'.eqv_trans _ _ _
        (weighted_insert weight term.1 term.2 (collect rest))
        (Q'.add_eqv_congr_left _ _ _ ih)

private theorem insert_keys (key : List Nat) (coefficient : Q') :
    ∀ (p : RatPoly) (m : List Nat),
      m ∈ (insertKey key coefficient p).map Prod.fst →
        m = key ∨ m ∈ p.map Prod.fst
  | [], m, hm => by
      by_cases hz : coefficient.num = 0
      · simp [insertKey, hz] at hm
      · have he : m = key := by simpa [insertKey, hz] using hm
        exact Or.inl he
  | (other, value) :: rest, m, hm => by
      by_cases he : key = other
      · by_cases hz : (coefficient + value).num = 0
        · have hr : m ∈ rest.map Prod.fst := by
            simpa [insertKey, he, hz] using hm
          exact Or.inr (List.mem_cons_of_mem _ hr)
        · have hr : m = other ∨ m ∈ rest.map Prod.fst := by
            simpa [insertKey, he, hz] using hm
          rcases hr with hhead | htail
          · exact Or.inl (hhead.trans he.symm)
          · exact Or.inr (List.mem_cons_of_mem _ htail)
      · have hr : m = other ∨
            m ∈ (insertKey key coefficient rest).map Prod.fst := by
          simpa [insertKey, he] using hm
        rcases hr with hhead | htail
        · exact Or.inr (List.mem_cons.mpr (Or.inl hhead))
        · rcases insert_keys key coefficient rest m htail with hnew | hold
          · exact Or.inl hnew
          · exact Or.inr (List.mem_cons_of_mem _ hold)

/-- The collector introduces no exponent-list key. -/
theorem collect_keys (p : RatPoly) (m : List Nat)
    (hm : m ∈ (collect p).map Prod.fst) : m ∈ p.map Prod.fst := by
  induction p with
  | nil => simp [collect] at hm
  | cons term rest ih =>
      rcases insert_keys term.1 term.2 (collect rest) m hm with hhead | htail
      · exact List.mem_cons.mpr (Or.inl hhead)
      · exact List.mem_cons_of_mem _ (ih htail)

private theorem insert_nodup (key : List Nat) (coefficient : Q') :
    ∀ p : RatPoly, (p.map Prod.fst).Nodup →
      ((insertKey key coefficient p).map Prod.fst).Nodup
  | [], _ => by
      by_cases hz : coefficient.num = 0 <;> simp [insertKey, hz]
  | (other, value) :: rest, hp => by
      have hparts := List.nodup_cons.mp (by simpa only [List.map_cons] using hp)
      by_cases he : key = other
      · by_cases hz : (coefficient + value).num = 0
        · simpa [insertKey, he, hz] using hparts.2
        · simpa [insertKey, he, hz] using hp
      · have htail := insert_nodup key coefficient rest hparts.2
        have hnot : other ∉ (insertKey key coefficient rest).map Prod.fst := by
          intro hm
          rcases insert_keys key coefficient rest other hm with hnew | hold
          · exact he hnew.symm
          · exact hparts.1 hold
        simpa [insertKey, he] using
          (List.nodup_cons.mpr ⟨hnot, htail⟩)

/-- Output monomial keys are pairwise distinct, including for repeated input
terms with cancellation. -/
theorem collect_nodup (p : RatPoly) : ((collect p).map Prod.fst).Nodup := by
  induction p with
  | nil => simp [collect]
  | cons term rest ih => exact insert_nodup term.1 term.2 (collect rest) ih

private theorem insert_nonzero (key : List Nat) (coefficient : Q') :
    ∀ p : RatPoly,
      (∀ t, t ∈ p → t.2.num ≠ 0) →
      ∀ t, t ∈ insertKey key coefficient p → t.2.num ≠ 0
  | [], _, t, ht => by
      by_cases hz : coefficient.num = 0
      · simp [insertKey, hz] at ht
      · have he : t = (key, coefficient) := by
          simpa [insertKey, hz] using ht
        subst t
        exact hz
  | (other, value) :: rest, hp, t, ht => by
      by_cases he : key = other
      · by_cases hz : (coefficient + value).num = 0
        · have hr : t ∈ rest := by simpa [insertKey, he, hz] using ht
          exact hp t (List.mem_cons_of_mem _ hr)
        · have hr : t = (other, coefficient + value) ∨ t ∈ rest := by
            simpa [insertKey, he, hz] using ht
          rcases hr with hhead | htail
          · subst t; exact hz
          · exact hp t (List.mem_cons_of_mem _ htail)
      · have hr : t = (other, value) ∨
            t ∈ insertKey key coefficient rest := by
          simpa [insertKey, he] using ht
        rcases hr with hhead | htail
        · subst t; exact hp _ List.mem_cons_self
        · exact insert_nonzero key coefficient rest
            (fun u hu => hp u (List.mem_cons_of_mem _ hu)) t htail

/-- The collector removes every coefficient with zero numerator. -/
theorem collect_nonzero (p : RatPoly) :
    ∀ t, t ∈ collect p → t.2.num ≠ 0 := by
  induction p with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons term rest ih => exact insert_nonzero term.1 term.2 (collect rest) ih

/-- Any list with distinct exponent keys has length bounded by an arbitrary
finite covering key list; the cover itself need not be duplicate-free. -/
theorem length_le_cover (p : RatPoly) (hn : (p.map Prod.fst).Nodup)
    (U : List (List Nat))
    (hcover : ∀ m, m ∈ p.map Prod.fst → m ∈ U) :
    p.length ≤ U.length := by
  have h := YMGap.Continuum.FiniteBoolGraphSimplePaths.FiniteListBound.nodup_subset_length_le
    (p.map Prod.fst) U hn hcover
  simpa only [List.length_map] using h

/-- An arbitrary finite covering key list bounds the collected term count. -/
theorem collect_length_le_cover (p : RatPoly) (U : List (List Nat))
    (hcover : ∀ m, m ∈ p.map Prod.fst → m ∈ U) :
    (collect p).length ≤ U.length :=
  length_le_cover (collect p) (collect_nodup p) U
    (fun m hm => hcover m (collect_keys p m hm))

/-- Collection preserves literal quaternion-coordinate support, by key
provenance rather than by any sphere-quotient reduction. -/
theorem collect_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (collect p) := by
  intro t ht
  have hk : t.1 ∈ p.map Prod.fst :=
    collect_keys p t.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hk
  calc
    t.1.length = u.1.length := congrArg List.length he.symm
    _ ≤ 4 * blocks := hp u hu

/-- Collection preserves every syntactic per-block degree ceiling. -/
theorem collect_degree {block d : Nat} {p : RatPoly}
    (hp : DegreeLE block d p) : DegreeLE block d (collect p) := by
  intro t ht
  have hk : t.1 ∈ p.map Prod.fst :=
    collect_keys p t.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hk
  calc
    quaternionBlockDegree t.1 block = quaternionBlockDegree u.1 block :=
      congrArg (fun m => quaternionBlockDegree m block) he.symm
    _ ≤ d := hp u hu

#print axioms insertKey
#print axioms collect
#print axioms weighted_insert
#print axioms collect_coeff
#print axioms collect_keys
#print axioms collect_nodup
#print axioms collect_nonzero
#print axioms length_le_cover
#print axioms collect_length_le_cover
#print axioms collect_supported
#print axioms collect_degree

end YMGap.Continuum.SU2QuaternionSparseCoefficientCollector
