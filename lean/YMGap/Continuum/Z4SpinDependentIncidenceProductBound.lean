/-
# Facewise allocation of spin-dependent link multiplicities

The local fusion bound is naturally written in the canonical coordinates of a
trivalent resolution.  For a global polymer estimate those factors must be
charged back to the physical plaquettes.  This module begins that transport
constructively: it identifies the canonical prefix product exactly with the
product of `(spin + 1)` over the incident plaquette identifiers.

The subsequent incidence argument can therefore count each physical face at
its four boundary links, with no dependence on the auxiliary cutoff.
-/

import YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.Z4SpinDependentIncidenceProductBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Constructive products of natural-number decorations -/

def natListProduct : List Nat → Nat
  | [] => 1
  | x :: xs => x * natListProduct xs

theorem natListProduct_append : ∀ left right : List Nat,
    natListProduct (left ++ right) =
      natListProduct left * natListProduct right
  | [], right => by simp [natListProduct]
  | x :: xs, right => by
      simp only [List.cons_append, natListProduct]
      rw [natListProduct_append xs right]
      exact (Nat.mul_assoc x (natListProduct xs) (natListProduct right)).symm

theorem natListProduct_map_congr {A : Type} (left right : A → Nat) :
    ∀ xs : List A, (∀ x, x ∈ xs → left x = right x) →
      natListProduct (xs.map left) = natListProduct (xs.map right)
  | [], _ => rfl
  | x :: xs, hagree => by
      simp only [List.map_cons, natListProduct]
      rw [hagree x List.mem_cons_self,
        natListProduct_map_congr left right xs
          (fun y hy => hagree y (List.mem_cons_of_mem x hy))]

theorem natListProduct_map_one {A : Type} : ∀ xs : List A,
    natListProduct (xs.map (fun _ => 1)) = 1
  | [] => rfl
  | _ :: xs => by
      simp only [List.map_cons, natListProduct, Nat.one_mul]
      exact natListProduct_map_one xs

theorem natListProduct_map_mul {A : Type} (left right : A → Nat) :
    ∀ xs : List A,
      natListProduct (xs.map (fun x => left x * right x)) =
        natListProduct (xs.map left) * natListProduct (xs.map right)
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, natListProduct]
      rw [natListProduct_map_mul left right xs]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem natListProduct_filter_eq_if {A : Type}
    (predicate : A → Bool) (weight : A → Nat) : ∀ xs : List A,
    natListProduct ((xs.filter predicate).map weight) =
      natListProduct (xs.map fun x =>
        if predicate x then weight x else 1)
  | [] => rfl
  | x :: xs => by
      cases h : predicate x <;>
        simp [List.filter_cons, h, natListProduct,
          natListProduct_filter_eq_if predicate weight xs]

theorem natListProduct_map_const {A : Type} (value : Nat) :
    ∀ xs : List A,
      natListProduct (xs.map (fun _ => value)) = value ^ xs.length
  | [] => rfl
  | _ :: xs => by
      simp only [List.map_cons, natListProduct, List.length_cons,
        Nat.pow_succ, natListProduct_map_const value xs]
      exact Nat.mul_comm value (value ^ xs.length)

/-! A finite multiplicative Fubini theorem. -/

def natRectangleProduct {A B : Type} (rows : List A) (columns : List B)
    (term : A → B → Nat) : Nat :=
  natListProduct (rows.map fun row =>
    natListProduct (columns.map (term row)))

theorem natRectangleProduct_swap {A B : Type}
    (rows : List A) (columns : List B) (term : A → B → Nat) :
    natRectangleProduct rows columns term =
      natRectangleProduct columns rows (fun column row => term row column) := by
  induction rows with
  | nil =>
      unfold natRectangleProduct
      simp only [List.map_nil, natListProduct]
      exact (natListProduct_map_one columns).symm
  | cons row rest ih =>
      unfold natRectangleProduct at ih ⊢
      simp only [List.map_cons, natListProduct]
      change natListProduct (columns.map (term row)) *
          natListProduct (rest.map fun next =>
            natListProduct (columns.map (term next))) =
        natListProduct (columns.map fun column =>
          term row column * natListProduct
            (rest.map fun next => term next column))
      rw [natListProduct_map_mul]
      exact congrArg (fun value =>
        natListProduct (columns.map (term row)) * value) ih

theorem externalPrefixSpinProduct_eq_listProduct
    (degree : Nat) (external : EdgeLabelling) :
    externalPrefixSpinProduct degree external =
      natListProduct ((List.range degree).map
        (fun position => external position + 1)) := by
  induction degree with
  | zero => rfl
  | succ degree ih =>
      simp only [externalPrefixSpinProduct, List.range_succ,
        List.map_append, natListProduct_append, List.map_singleton,
        natListProduct, Nat.mul_one, ih]

/-! ## 2. Removal of the synthetic local-coordinate layer -/

theorem actualIncidentSpinProduct_eq_incidentProduct
    (n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) :
    actualIncidentSpinProduct n physical indexed =
      natListProduct ((incidentPlaqIds n indexed.2).map
        (fun identifier => physical identifier + 1)) := by
  unfold actualIncidentSpinProduct
  rw [externalPrefixSpinProduct_eq_listProduct]
  let labels := incidentPlaqIds n indexed.2
  let base := linkBlockBase n indexed.1
  change natListProduct ((List.range labels.length).map
      ((fun identifier => physical identifier + 1) ∘
        localIdentifierRename labels base)) =
    natListProduct (labels.map (fun identifier => physical identifier + 1))
  rw [← List.map_map, map_localIdentifierRename_range]

/-! ## 3. Every box plaquette has exactly four listed boundary links -/

private theorem filtered_eraseDups_nodup {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ predicate : A → Bool, (xs.filter predicate).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons x rest ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun y => (!(y == x)) && predicate y)⟩
        intro hx
        have hx' : x ∈ rest.filter
            (fun y => (!(y == x)) && predicate y) :=
          List.mem_eraseDups.mp hx
        have hfalse := (List.mem_filter.mp hx').2
        have hself : (x == x) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

private theorem filter_true {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | x :: rest => congrArg (List.cons x) (filter_true rest)

private theorem eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup xs (fun _ => true)
  rw [filter_true] at h
  exact h

theorem distinctBoxLinks_nodup (n : Nat) :
    (distinctBoxLinks n).Nodup := by
  unfold distinctBoxLinks
  exact eraseDups_nodup_local _

theorem edgesOf_length (p : Z4Plaq) : (edgesOf p).length = 4 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;> rfl

theorem listedBoundaryLinks_length_eq_four
    {n : Nat} {p : Z4Plaq} (hp : p ∈ boxPlaquettes n) :
    ((distinctBoxLinks n).filter fun ell =>
      decide (ell ∈ edgesOf p)).length = 4 := by
  let selected := (distinctBoxLinks n).filter fun ell =>
    decide (ell ∈ edgesOf p)
  change selected.length = 4
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup (distinctBoxLinks_nodup n)
  have hselectedSubset : ∀ ell, ell ∈ selected → ell ∈ edgesOf p := by
    intro ell hell
    have hinc := (List.mem_filter.mp hell).2
    simpa only [decide_eq_true_eq] using hinc
  have hselectedLe : selected.length ≤ (edgesOf p).length :=
    nodup_subset_length_le selected (edgesOf p)
      hselectedNodup hselectedSubset
  have hedgeSubset : ∀ ell, ell ∈ edgesOf p → ell ∈ selected := by
    intro ell hell
    have hbox : ell ∈ boxLinks n := boundary_mem_boxLinks hp hell
    have hdistinct : ell ∈ distinctBoxLinks n := by
      unfold distinctBoxLinks
      exact List.mem_eraseDups.mpr hbox
    exact List.mem_filter.mpr
      ⟨hdistinct, by simpa only [decide_eq_true_eq]⟩
  have hedgeLe : (edgesOf p).length ≤ selected.length :=
    nodup_subset_length_le (edgesOf p) selected
      (edgesOf_nodup p) hedgeSubset
  rw [edgesOf_length] at hselectedLe hedgeLe
  omega

/-! ## 4. Exact multiplicative incidence allocation -/

private theorem enumerateFrom_snd_mem {A : Type} (start : Nat) :
    ∀ {xs : List A} {indexed : Nat × A},
      indexed ∈ enumerateFrom start xs → indexed.2 ∈ xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: rest, indexed, hmem => by
      simp only [enumerateFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem head
          (enumerateFrom_snd_mem (start + 1) hrest)

private theorem enumerate_snd_mem {A : Type} {xs : List A}
    {indexed : Nat × A} (hmem : indexed ∈ enumerate xs) :
    indexed.2 ∈ xs :=
  enumerateFrom_snd_mem 0 hmem

/-- Product of all incident `(spin + 1)` factors, first grouped by physical
link. -/
def boxLinkIncidentSpinProduct (n : Nat) (physical : EdgeLabelling) : Nat :=
  natListProduct ((distinctBoxLinks n).map fun ell =>
    natListProduct ((incidentPlaqIds n ell).map fun identifier =>
      physical identifier + 1))

/-- The same incidence product after allocation to faces.  Every plaquette
has four distinct boundary links. -/
def boxFaceFourthSpinProduct (n : Nat) (physical : EdgeLabelling) : Nat :=
  natListProduct ((enumerate (boxPlaquettes n)).map fun indexed =>
    (physical indexed.1 + 1) ^ 4)

theorem boxLinkIncidentSpinProduct_eq_rectangle
    (n : Nat) (physical : EdgeLabelling) :
    boxLinkIncidentSpinProduct n physical =
      natRectangleProduct (distinctBoxLinks n)
        (enumerate (boxPlaquettes n))
        (fun ell indexed =>
          if decide (ell ∈ edgesOf indexed.2)
          then physical indexed.1 + 1 else 1) := by
  unfold boxLinkIncidentSpinProduct natRectangleProduct
  apply natListProduct_map_congr
  intro ell _
  unfold incidentPlaqIds
  let entries := enumerate (boxPlaquettes n)
  let predicate : (Nat × Z4Plaq) → Bool := fun indexed =>
    decide (ell ∈ edgesOf indexed.2)
  change natListProduct
      (((entries.filter predicate).map Prod.fst).map
        (fun identifier => physical identifier + 1)) =
    natListProduct (entries.map fun indexed =>
      if predicate indexed then physical indexed.1 + 1 else 1)
  rw [List.map_map]
  exact natListProduct_filter_eq_if predicate
    (fun indexed => physical indexed.1 + 1) entries

theorem listedBoundarySpinProduct_eq_fourth
    {n : Nat} (physical : EdgeLabelling)
    {indexed : Nat × Z4Plaq}
    (hindexed : indexed ∈ enumerate (boxPlaquettes n)) :
    natListProduct ((distinctBoxLinks n).map fun ell =>
      if decide (ell ∈ edgesOf indexed.2)
      then physical indexed.1 + 1 else 1) =
        (physical indexed.1 + 1) ^ 4 := by
  have hp : indexed.2 ∈ boxPlaquettes n := enumerate_snd_mem hindexed
  rw [← natListProduct_filter_eq_if
    (fun ell => decide (ell ∈ edgesOf indexed.2))
    (fun _ => physical indexed.1 + 1)]
  rw [natListProduct_map_const,
    listedBoundaryLinks_length_eq_four hp]

/-- Multiplicative Fubini together with the exact four-edge plaquette boundary
allocates every link-local incident-spin factor to faces without any cutoff-
or volume-dependent loss. -/
theorem boxLinkIncidentSpinProduct_eq_faceFourthSpinProduct
    (n : Nat) (physical : EdgeLabelling) :
    boxLinkIncidentSpinProduct n physical =
      boxFaceFourthSpinProduct n physical := by
  rw [boxLinkIncidentSpinProduct_eq_rectangle,
    natRectangleProduct_swap]
  unfold natRectangleProduct boxFaceFourthSpinProduct
  apply natListProduct_map_congr
  intro indexed hindexed
  exact listedBoundarySpinProduct_eq_fourth physical hindexed

/-! ## 5. The cubic fusion charge becomes a twelfth power per face -/

theorem natListProduct_map_spinProductCube {A : Type} (weight : A → Nat) :
    ∀ xs : List A,
      natListProduct (xs.map fun x => spinProductCube (weight x)) =
        spinProductCube (natListProduct (xs.map weight))
  | xs => by
      unfold spinProductCube
      rw [natListProduct_map_mul weight
        (fun x => weight x * weight x) xs,
        natListProduct_map_mul weight weight xs]

theorem spinProductCube_pow_four (value : Nat) :
    spinProductCube (value ^ 4) = value ^ 12 := by
  unfold spinProductCube
  rw [show 12 = 4 + (4 + 4) by omega, Nat.pow_add, Nat.pow_add]

/-- The natural-number majorant obtained by cubing the incident-spin product
at every physical link. -/
def boxLinkIncidentSpinCubeProduct (n : Nat)
    (physical : EdgeLabelling) : Nat :=
  natListProduct ((distinctBoxLinks n).map fun ell =>
    spinProductCube
      (natListProduct ((incidentPlaqIds n ell).map fun identifier =>
        physical identifier + 1)))

/-- The exact facewise form of the cubic local-fusion charge. -/
def boxFaceTwelfthSpinProduct (n : Nat)
    (physical : EdgeLabelling) : Nat :=
  natListProduct ((enumerate (boxPlaquettes n)).map fun indexed =>
    (physical indexed.1 + 1) ^ 12)

theorem boxLinkIncidentSpinCubeProduct_eq_faceTwelfthSpinProduct
    (n : Nat) (physical : EdgeLabelling) :
    boxLinkIncidentSpinCubeProduct n physical =
      boxFaceTwelfthSpinProduct n physical := by
  calc
    boxLinkIncidentSpinCubeProduct n physical =
        spinProductCube (boxLinkIncidentSpinProduct n physical) := by
      unfold boxLinkIncidentSpinCubeProduct boxLinkIncidentSpinProduct
      exact natListProduct_map_spinProductCube _ _
    _ = spinProductCube (boxFaceFourthSpinProduct n physical) :=
      congrArg spinProductCube
        (boxLinkIncidentSpinProduct_eq_faceFourthSpinProduct n physical)
    _ = natListProduct ((enumerate (boxPlaquettes n)).map fun indexed =>
          spinProductCube ((physical indexed.1 + 1) ^ 4)) := by
      unfold boxFaceFourthSpinProduct
      exact (natListProduct_map_spinProductCube _ _).symm
    _ = boxFaceTwelfthSpinProduct n physical := by
      unfold boxFaceTwelfthSpinProduct
      apply natListProduct_map_congr
      intro indexed _
      exact spinProductCube_pow_four (physical indexed.1 + 1)

/-! ## 6. The rational link product inherits the facewise majorant -/

private theorem ofNat_nonnegative (value : Nat) :
    (0 : Q') ≤ Q'.ofNat value := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.ofNat value).num
  exact Int.natCast_nonneg value

private theorem ofNat_mul_eqv (left right : Nat) :
    (Q'.ofNat left * Q'.ofNat right).eqv
      (Q'.ofNat (left * right)) := by
  show (Q'.ofNat left * Q'.ofNat right).num *
      ((Q'.ofNat (left * right)).den : Int) =
    (Q'.ofNat (left * right)).num *
      ((Q'.ofNat left * Q'.ofNat right).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat left) * (Int.ofNat right)) * 1 =
    (Int.ofNat (left * right)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

def indexedLinkIncidentSpinCubeProduct (n : Nat)
    (physical : EdgeLabelling) : List (Nat × Z4Link) → Nat
  | links =>
      natListProduct (links.map fun indexed =>
        spinProductCube
          (natListProduct ((incidentPlaqIds n indexed.2).map
            (fun identifier => physical identifier + 1))))

theorem explicitLinkMultiplicityProduct_le_indexedSpinCubeProduct
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat × Z4Link),
      explicitLinkMultiplicityProduct K n physical links ≤
        Q'.ofNat (indexedLinkIncidentSpinCubeProduct n physical links)
  | [] => Q'.le_refl' 1
  | indexed :: rest => by
      simp only [explicitLinkMultiplicityProduct,
        indexedLinkIncidentSpinCubeProduct, List.map_cons, natListProduct]
      have hhead := explicitLinkMultiplicityFactor_le_spinProductCube
        K n physical indexed
      rw [actualIncidentSpinProduct_eq_incidentProduct] at hhead
      have htail :=
        explicitLinkMultiplicityProduct_le_indexedSpinCubeProduct
          K n physical rest
      have htail0 : (0 : Q') ≤
          explicitLinkMultiplicityProduct K n physical rest :=
        explicitLinkMultiplicityProduct_nonnegative K n physical rest
      let headBound := spinProductCube
        (natListProduct ((incidentPlaqIds n indexed.2).map
          (fun identifier => physical identifier + 1)))
      let tailBound := indexedLinkIncidentSpinCubeProduct n physical rest
      have hfirst :
          explicitLinkMultiplicityFactor K n physical indexed *
              explicitLinkMultiplicityProduct K n physical rest ≤
            Q'.ofNat headBound *
              explicitLinkMultiplicityProduct K n physical rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hhead htail0
      have hsecond :
          Q'.ofNat headBound *
              explicitLinkMultiplicityProduct K n physical rest ≤
            Q'.ofNat headBound * Q'.ofNat tailBound :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail
          (ofNat_nonnegative headBound)
      have hproduct :
          explicitLinkMultiplicityFactor K n physical indexed *
              explicitLinkMultiplicityProduct K n physical rest ≤
            Q'.ofNat headBound * Q'.ofNat tailBound :=
        Q'.le_trans' _ _ _ hfirst hsecond
      exact Q'.le_trans' _ _ _ hproduct
        (Q'.le_of_eqv (ofNat_mul_eqv headBound tailBound))

theorem indexedLinkIncidentSpinCubeProduct_enumerate_eq_box
    (n : Nat) (physical : EdgeLabelling) :
    indexedLinkIncidentSpinCubeProduct n physical
        (enumerate (distinctBoxLinks n)) =
      boxLinkIncidentSpinCubeProduct n physical := by
  unfold indexedLinkIncidentSpinCubeProduct
    boxLinkIncidentSpinCubeProduct
  change natListProduct ((enumerate (distinctBoxLinks n)).map
      ((fun ell => spinProductCube
        (natListProduct ((incidentPlaqIds n ell).map
          (fun identifier => physical identifier + 1)))) ∘ Prod.snd)) = _
  rw [← List.map_map, enumerate_map_snd]

/-- The complete literal link multiplicity is bounded by a product of one
twelfth-power spin factor per physical plaquette.  Neither the auxiliary
cutoff `K` nor the box volume occurs in a local factor. -/
theorem explicitLinkMultiplicityProduct_le_faceTwelfthSpinProduct
    (K n : Nat) (physical : EdgeLabelling) :
    explicitLinkMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) ≤
      Q'.ofNat (boxFaceTwelfthSpinProduct n physical) := by
  have h := explicitLinkMultiplicityProduct_le_indexedSpinCubeProduct
    K n physical (enumerate (distinctBoxLinks n))
  rw [indexedLinkIncidentSpinCubeProduct_enumerate_eq_box,
    boxLinkIncidentSpinCubeProduct_eq_faceTwelfthSpinProduct] at h
  exact h

end YMGap.Continuum.Z4SpinDependentIncidenceProductBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.natListProduct_append
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.natRectangleProduct_swap
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.externalPrefixSpinProduct_eq_listProduct
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.actualIncidentSpinProduct_eq_incidentProduct
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.listedBoundaryLinks_length_eq_four
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.boxLinkIncidentSpinProduct_eq_faceFourthSpinProduct
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.boxLinkIncidentSpinCubeProduct_eq_faceTwelfthSpinProduct
#print axioms YMGap.Continuum.Z4SpinDependentIncidenceProductBound.explicitLinkMultiplicityProduct_le_faceTwelfthSpinProduct
